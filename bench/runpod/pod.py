#!/usr/bin/env python3
"""Run evaluate.py on a RunPod CPU pod. Runs on your machine; Python 3.8+ stdlib, curl, ssh.

  pod.py create [--vcpus 8]            create a CPU pod (REST API), print its id   ** BILLS **
  pod.py list                          list your pods (check that nothing is left running)
  pod.py info POD                      show a pod's state and ssh endpoint
  pod.py ssh POD [CMD...]              open a shell, or run CMD, on the pod
  pod.py evaluate POD --base REF --cand REF [evaluate.py options]
                                       upload, set up, measure base, judge cand, download
  pod.py full LOGIC [--timeout 10]     create a pod, run every LOGIC benchmark with smt-rex,
                                       z3 and cvc5, download the results, delete the pod
  pod.py fetch POD                     download bench/results from the pod again
  pod.py delete POD                    delete the pod (stops billing; cannot be undone)

Every command takes --dry-run: print what would happen (with the API key redacted), touch
nothing remote. `evaluate --dry-run` still builds the upload bundle locally, as a check.

WARNING: a pod bills until it is deleted. Always finish with `pod.py delete POD` (or pass
`evaluate --delete`), then `pod.py list` to confirm. Backup: `nix build nixpkgs#runpodctl` and
`./result/bin/runpodctl remove pod POD`.

Pods are created through the REST API (https://rest.runpod.io/v1/pods) with curl:
`runpodctl pod create` cannot choose a CPU size, and Python's urllib gets blocked by
Cloudflare. The API key is read from ~/.runpod/config.toml (`apikey = ...`); the ssh key is
~/.runpod/ssh/runpodctl-ssh-key (created by `runpodctl config`).
"""

import argparse
import io
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
BENCH = HERE.parent
ROOT = BENCH.parent
REPO = ROOT
API = "https://rest.runpod.io/v1"
CONFIG = Path.home() / ".runpod" / "config.toml"
SSH_KEY = Path.home() / ".runpod" / "ssh" / "runpodctl-ssh-key"
IMAGE = "runpod/base:0.6.2-cpu"
FLAVORS = ["cpu5c", "cpu3c", "cpu3g", "cpu5g"]  # tried in order
REMOTE = "/workspace/smtrex"  # everything on the pod lives here
TAR_FILTER = {"filter": "data"} if hasattr(tarfile, "data_filter") else {}
DRY_POD = {"id": "DRYRUN", "publicIp": "203.0.113.1", "portMappings": {"22": 22}}


def die(msg):
    sys.exit("pod.py: " + msg)


def say(msg):
    print(msg, flush=True)


# ---------------------------------------------------------------------------------------------
# REST API through curl


def api_key():
    try:
        text = CONFIG.read_text()
    except OSError:
        die(f"no {CONFIG}; run `runpodctl config --apiKey ...` first")
    m = re.search(r"""^\s*api_?key\s*=\s*['"]?([^'"\s]+)""", text, re.M | re.I)
    if not m:
        die(f"no apikey in {CONFIG}")
    return m.group(1)


def api(method, path, body=None, dry=False):
    """Call the REST API with curl; the key goes through a 0600 header file, not argv."""
    url = API + path
    argv = ["curl", "-sS", "-X", method, url, "-H", "Content-Type: application/json"]
    if body is not None:
        argv += ["-d", json.dumps(body)]
    if dry:
        say("+ " + " ".join(shlex.quote(a) for a in argv) +
            " -H 'Authorization: Bearer <redacted>'")
        return None
    fd, hdr = tempfile.mkstemp(prefix="runpod-hdr-")
    try:
        with os.fdopen(fd, "w") as f:
            f.write(f"Authorization: Bearer {api_key()}\n")
        p = subprocess.run(argv + ["-H", "@" + hdr, "-w", "\n%{http_code}"],
                           stdout=subprocess.PIPE, universal_newlines=True)
    finally:
        os.unlink(hdr)
    out, _, code = p.stdout.rpartition("\n")
    if p.returncode != 0:
        die(f"curl failed ({p.returncode}) on {method} {path}")
    try:
        data = json.loads(out) if out.strip() else None
    except ValueError:
        data = {"error": out.strip()[:300]}
    return int(code or 0), data


def get_pod(pod_id, dry=False):
    if dry or pod_id == DRY_POD["id"]:
        return dict(DRY_POD, id=pod_id)
    code, data = api("GET", f"/pods/{pod_id}")
    if code != 200 or not isinstance(data, dict):
        die(f"GET pod {pod_id}: HTTP {code} {data}")
    return data


def ssh_endpoint(pod):
    ip = pod.get("publicIp")
    port = (pod.get("portMappings") or {}).get("22")
    if not ip or not port:
        return None
    return ip, int(port)


def wait_for_ssh(pod_id, dry=False, timeout=600):
    if dry:
        return ssh_endpoint(get_pod(pod_id, dry=True))
    t = time.time()
    while time.time() - t < timeout:
        pod = get_pod(pod_id)
        ep = ssh_endpoint(pod)
        if ep and ssh_argv(ep, ["true"], probe=True):
            return ep
        say(f"  waiting for ssh ({pod.get('desiredStatus')}, {time.time() - t:.0f}s)")
        time.sleep(10)
    die(f"pod {pod_id} has no ssh after {timeout}s; delete it: pod.py delete {pod_id}")


# ---------------------------------------------------------------------------------------------
# ssh


def ssh_base(ep):
    ip, port = ep
    return ["ssh", "-o", "StrictHostKeyChecking=accept-new", "-o", "ConnectTimeout=20",
            "-o", "IdentitiesOnly=yes", "-o", "IdentityAgent=none",
            "-o", "ServerAliveInterval=30", "-o", "ServerAliveCountMax=10",
            "-i", str(SSH_KEY), "-p", str(port), f"root@{ip}"]


def ssh_argv(ep, remote_argv, probe=False):
    """True if the remote command succeeds (used to probe for a live sshd)."""
    p = subprocess.run(ssh_base(ep) + ["-o", "BatchMode=yes"] + remote_argv,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return p.returncode == 0


def remote(ep, script, dry=False, stdin=None, stdout=None):
    """Run a bash script on the pod, streaming its output."""
    if dry:
        say(f"+ ssh root@{ep[0]} -p {ep[1]} bash -lc " + shlex.quote(script.strip()))
        return 0
    p = subprocess.run(ssh_base(ep) + ["bash -lc " + shlex.quote(script)], stdin=stdin,
                       stdout=stdout)
    return p.returncode


# ---------------------------------------------------------------------------------------------
# The upload bundle


def git(*args):
    p = subprocess.run(["git", "-C", str(REPO)] + list(args), stdout=subprocess.PIPE,
                       universal_newlines=False)
    if p.returncode != 0:
        die("git " + " ".join(args) + " failed")
    return p.stdout


def add_bytes(tar, name, data, mode=0o644):
    info = tarfile.TarInfo(name)
    info.size = len(data)
    info.mode = mode
    info.mtime = int(time.time())
    tar.addfile(info, io.BytesIO(data))


def tuning_files():
    """(logic, relative path) of every tuning instance. Held-out files never leave this host."""
    out = []
    for setfile in sorted((BENCH / "sets").glob("*.json")):
        m = json.loads(setfile.read_text())
        out += [(m["logic"], item["path"]) for item in m["tuning"]]
    return out


def make_bundle(path, base_sha, cand_sha, logics):
    """repo: this checkout (tracked + untracked, not ignored), the harness;
    src/<sha>: `git archive` of base and candidate; repo/bench/data: tuning files."""
    with tarfile.open(str(path), "w:gz") as tar:
        listed = git("ls-files", "-z", "--cached", "--others", "--exclude-standard").split(b"\0")
        for rel in listed:
            rel = rel.decode()
            p = REPO / rel
            if rel and p.is_file() and not p.is_symlink():
                tar.add(str(p), arcname="repo/" + rel, recursive=False)
        for sha in sorted({base_sha, cand_sha}):
            data = git("archive", "--format=tar", sha)
            with tarfile.open(fileobj=io.BytesIO(data), mode="r:") as src:
                for m in src.getmembers():
                    f = src.extractfile(m) if m.isfile() else None
                    m.name = f"src/{sha}/{m.name}"
                    tar.addfile(m, f)
        n = 0
        for logic, rel in tuning_files():
            if logic not in logics:
                continue
            p = BENCH / "data" / "non-incremental" / logic / rel
            if not p.exists():
                die(f"missing benchmark {p}")
            tar.add(str(p.resolve()), arcname=f"repo/bench/data/non-incremental/{logic}/{rel}")
            n += 1
        add_bytes(tar, "repo/BUNDLE", f"base {base_sha}\ncand {cand_sha}\n".encode())
    say(f"bundle: {path} ({path.stat().st_size / 1e6:.1f} MB, {n} tuning files, "
        f"base {base_sha[:12]}, cand {cand_sha[:12]})")


# ---------------------------------------------------------------------------------------------
# Commands


def create_pod(args):
    """Create a pod; returns its API record (DRY_POD on a dry run)."""
    if not args.dry_run and not SSH_KEY.exists():
        die(f"no ssh key {SSH_KEY}; run `runpodctl config` once")
    pub = SSH_KEY.with_suffix(".pub").read_text().strip() if SSH_KEY.with_suffix(
        ".pub").exists() else "<public key>"
    for flavor in args.flavor.split(","):
        body = {"name": args.name, "computeType": "CPU", "cpuFlavorIds": [flavor],
                "vcpuCount": args.vcpus, "imageName": IMAGE,
                "containerDiskInGb": getattr(args, "disk_gb", 20),
                "volumeInGb": args.volume_gb, "ports": ["22/tcp"], "env": {"PUBLIC_KEY": pub}}
        if args.dry_run:
            api("POST", "/pods", body, dry=True)
            say("(dry run: no pod created)")
            return dict(DRY_POD, memoryInGb=2 * args.vcpus)
        code, r = api("POST", "/pods", body)
        r = r[0] if isinstance(r, list) and r else r
        if isinstance(r, dict) and r.get("id"):
            say(f"created pod {r['id']} ({flavor}, {r.get('vcpuCount')} vCPU, "
                f"{r.get('memoryInGb')} GB, ${r.get('costPerHr')}/h)")
            say(f"WARNING: it bills until deleted: pod.py delete {r['id']}")
            return r
        say(f"  {flavor}: HTTP {code} {str((r or {}).get('error', r))[:200]}")
    die("no flavor had capacity")


def cmd_create(args):
    print(create_pod(args)["id"])
    return 0


def cmd_list(args):
    if args.dry_run:
        api("GET", "/pods", dry=True)
        return 0
    code, pods = api("GET", "/pods")
    if code != 200:
        die(f"HTTP {code} {pods}")
    for p in pods or []:
        say(f"{p.get('id')}  {p.get('name')}  {p.get('desiredStatus')}  "
            f"{p.get('vcpuCount')} vCPU  ${p.get('costPerHr')}/h")
    if pods:
        say(f"{len(pods)} pod(s) exist and may be billing")
    else:
        say("no pods")
    return 0


def cmd_info(args):
    pod = get_pod(args.pod, args.dry_run)
    say(json.dumps({k: pod.get(k) for k in ("id", "name", "desiredStatus", "vcpuCount",
                                            "memoryInGb", "costPerHr", "publicIp",
                                            "portMappings")}, indent=1))
    return 0


def cmd_ssh(args):
    ep = ssh_endpoint(get_pod(args.pod, args.dry_run))
    if not ep:
        die("the pod has no ssh endpoint yet")
    argv = ssh_base(ep) + args.cmd
    if args.dry_run:
        say("+ " + " ".join(shlex.quote(a) for a in argv))
        return 0
    os.execvp(argv[0], argv)


def cmd_delete(args):
    if args.dry_run:
        api("DELETE", f"/pods/{args.pod}", dry=True)
        return 0
    code, r = api("DELETE", f"/pods/{args.pod}")
    if code not in (200, 204):
        die(f"delete {args.pod}: HTTP {code} {r}; delete it in the console or with "
            f"`runpodctl remove pod {args.pod}`")
    say(f"deleted pod {args.pod}")
    return 0


def fetch(ep, pod_id, dry):
    dest = BENCH / "results" / f"runpod-{pod_id}"
    if dry:
        say(f"+ ssh ... tar -czf - -C {REMOTE}/repo/bench results | tar -xz -C {dest}")
        return dest
    dest.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryFile() as buf:
        rc = remote(ep, f"tar -czf - -C {REMOTE}/repo/bench results", stdout=buf)
        buf.seek(0)
        if rc == 0:
            with tarfile.open(fileobj=buf, mode="r:gz") as tar:
                for m in tar.getmembers():
                    if m.isfile() and not m.name.startswith("/") and ".." not in m.name:
                        tar.extract(m, str(dest), **TAR_FILTER)
    say(f"results downloaded to {dest}")
    return dest


def cmd_fetch(args):
    ep = ssh_endpoint(get_pod(args.pod, args.dry_run))
    if not ep:
        die("the pod has no ssh endpoint")
    fetch(ep, args.pod, args.dry_run)
    return 0


def resolve(ref):
    return git("rev-parse", "--verify", ref + "^{commit}").decode().strip()


def cmd_evaluate(args):
    dry = args.dry_run
    base, cand = resolve(args.base), resolve(args.cand)
    logics = args.logics.split(",") if args.logics else sorted(
        p.stem for p in (BENCH / "sets").glob("*.json"))
    # The guards need git history, which the pod does not get: check them here first.
    p = subprocess.run([sys.executable, str(BENCH / "evaluate.py"), "check", "--ref", cand,
                        "--base-commit", base])
    if p.returncode != 0:
        die("the candidate fails the guards; not starting anything remote")

    work = Path(tempfile.mkdtemp(prefix="smtrex-pod-"))
    bundle = work / "bundle.tar.gz"
    make_bundle(bundle, base, cand, logics)
    rc = 1
    try:
        ep = wait_for_ssh(args.pod, dry)
        say(f"pod {args.pod}: ssh root@{ep[0]} -p {ep[1]}")
        say("upload:")
        if dry:
            say(f"+ ssh ... 'mkdir -p {REMOTE} && tar -xzf - -C {REMOTE}' < {bundle}")
        else:
            with open(str(bundle), "rb") as f:
                if remote(ep, f"mkdir -p {REMOTE} && tar -xzf - -C {REMOTE}", stdin=f) != 0:
                    die("upload failed")
        say("setup:")
        if remote(ep, f"bash {REMOTE}/repo/bench/runpod/setup.sh", dry) != 0:
            die("setup failed")
        opts = ["--jobs", str(args.jobs), "--repeats", str(args.repeats),
                "--fuzz-count", str(args.fuzz_count)]
        if args.logics:
            opts += ["--logics", args.logics]
        if args.fuzz_seed is not None:
            opts += ["--fuzz-seed", str(args.fuzz_seed)]
        margin = ["--margin-rel", str(args.margin_rel), "--margin-abs", str(args.margin_abs)]
        q = " ".join(shlex.quote(o) for o in opts)
        script = f"""
set -eo pipefail
. /opt/smtrex/env.sh
cd {REMOTE}/repo/bench
mkdir -p results
export CARGO_BUILD_JOBS={args.jobs}
python3 evaluate.py measure --src {REMOTE}/src/{base} --label base-{base[:12]} \\
  --commit {base} {q} --out results/pod-base-{base[:12]}.json | tee results/pod-base.log
set +e
python3 evaluate.py run --src {REMOTE}/src/{cand} --label cand-{cand[:12]} --commit {cand} \\
  --baseline results/pod-base-{base[:12]}.json {q} {' '.join(margin)} \\
  --out results/pod-cand-{cand[:12]}.json | tee results/pod-cand.log
"""
        say("evaluate:")
        rc = remote(ep, script, dry)
        if not dry:
            say(f"evaluate.py exited {rc} (0 = ACCEPT, 2 = REJECT, else an error)")
        fetch(ep, args.pod, dry)
    finally:
        shutil.rmtree(str(work), ignore_errors=True)
        if args.delete:
            cmd_delete(argparse.Namespace(pod=args.pod, dry_run=dry))
        else:
            say(f"\nWARNING: pod {args.pod} is still running and billing. Delete it now:\n"
                f"  python3 {(HERE / 'pod.py').relative_to(ROOT)} delete {args.pod}")
    return rc


FULL_SOLVERS = ("smt-rex", "z3", "cvc5")


def cmd_full(args):
    """Create a pod, run every benchmark of one logic with each solver, download, delete."""
    dry = args.dry_run
    sha = resolve(args.ref)
    logic = args.logic
    work = Path(tempfile.mkdtemp(prefix="smtrex-full-"))
    bundle = work / "bundle.tar"
    data = git("archive", "--format=tar", "--prefix=repo/", sha)
    bundle.write_bytes(data)
    say(f"bundle: {sha[:12]} ({len(data) / 1e6:.1f} MB); the pod downloads {logic}")

    pod = create_pod(argparse.Namespace(dry_run=dry, flavor=args.flavor, vcpus=args.vcpus,
                                        name=f"smtrex-full-{logic}", volume_gb=args.volume_gb,
                                        disk_gb=args.disk_gb))
    pod_id = pod["id"]
    jobs = args.jobs or max(1, args.vcpus // 2)  # vCPUs are hyperthreads
    mem_gb = args.mem_gb or max(1, int(0.8 * (pod.get("memoryInGb") or 2 * args.vcpus) / jobs))
    tag = f"full-{logic}-{args.timeout:g}s"
    runs = "\n".join(
        f"BENCH_MEM_GB={mem_gb} python3 bench.py run {s} --logic {logic} --set full "
        f"--timeout {args.timeout:g} --jobs {jobs} --quiet --out results/{tag}-{s}.json "
        f"> results/{tag}-{s}.log 2>&1"
        for s in FULL_SOLVERS)
    script = f"""set -uo pipefail
. /opt/smtrex/env.sh
cd {REMOTE}/repo
echo "{sha}" > bench/results/COMMIT
cargo build --release --quiet || exit 1
cd bench
command -v zstd >/dev/null || DEBIAN_FRONTEND=noninteractive apt-get install -y -qq zstd \
  || exit 1
python3 bench.py fetch {logic} --max-mb {args.max_mb} || exit 1
{runs}
python3 bench.py report results/{tag}-*.json --out results/{tag}.md
test -s results/{tag}.md
"""
    rc = 1
    try:
        ep = wait_for_ssh(pod_id, dry)
        say(f"pod {pod_id}: ssh root@{ep[0]} -p {ep[1]}")
        if dry:
            say(f"+ ssh ... 'mkdir -p {REMOTE} && tar -xf - -C {REMOTE}' < {bundle}")
        else:
            with open(str(bundle), "rb") as f:
                if remote(ep, f"mkdir -p {REMOTE} && tar -xf - -C {REMOTE}", stdin=f) != 0:
                    die("upload failed")
        if remote(ep, f"bash {REMOTE}/repo/bench/runpod/setup.sh > /dev/null", dry) != 0:
            die("setup failed")
        # Detached, so that a dropped connection does not end a run of several hours.
        res = f"{REMOTE}/repo/bench/results"
        launch = (f"mkdir -p {res} && cat > {REMOTE}/full.sh && cd {REMOTE} && "
                  f"{{ setsid nohup bash -c 'bash full.sh > {res}/{tag}.out 2>&1; "
                  f"echo $? > {res}/EXIT' < /dev/null > /dev/null 2>&1 & }}")
        if dry:
            say("+ ssh ... " + launch)
            say(script)
        else:
            if remote(ep, launch, stdin=_pipe(script)) != 0:
                die("launch failed")
            t = time.time()
            fetched = 0
            while True:
                time.sleep(args.poll)
                p = subprocess.run(
                    ssh_base(ep) + ["-o", "BatchMode=yes",
                                    f"cd {res}; echo exit $(cat EXIT 2>/dev/null || echo -); "
                                    f"echo $(ls *.json 2>/dev/null) $(tail -n 1 {tag}.out)"],
                    stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, universal_newlines=True)
                out = p.stdout.strip().splitlines()
                say(f"  {logic} {time.time() - t:.0f}s: " + " | ".join(out))
                done = len(out) > 1 and out[1].count(".json")
                if done and done != fetched:  # a finished solver run: keep it, the pod may vanish
                    fetch(ep, pod_id, dry)
                    fetched = done
                code = out[0].split()[1] if out and out[0].startswith("exit ") else "-"
                if code != "-":
                    rc = int(code) if code.isdigit() else 1
                    break
                if time.time() - t > args.max_hours * 3600:  # e.g. a full disk: no EXIT file
                    say(f"  {logic}: no result after {args.max_hours:g} h; giving up")
                    break
        fetch(ep, pod_id, dry)
    finally:
        shutil.rmtree(str(work), ignore_errors=True)
        cmd_delete(argparse.Namespace(pod=pod_id, dry_run=dry))
    return rc


def _pipe(text):
    """A readable file object for subprocess stdin."""
    f = tempfile.TemporaryFile()
    f.write(text.encode())
    f.seek(0)
    return f


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    sub = ap.add_subparsers(dest="command")
    sub.required = True

    def add(name, func, help):
        p = sub.add_parser(name, help=help)
        p.add_argument("--dry-run", action="store_true", help="print, touch nothing remote")
        p.set_defaults(func=func)
        return p

    p = add("create", cmd_create, "create a CPU pod (bills until deleted)")
    p.add_argument("--vcpus", type=int, default=8)
    p.add_argument("--flavor", default=",".join(FLAVORS), help="CPU flavors to try, in order")
    p.add_argument("--name", default="smtrex-eval")
    p.add_argument("--volume-gb", type=int, default=20)
    add("list", cmd_list, "list pods")
    add("info", cmd_info, "show one pod").add_argument("pod")
    p = add("ssh", cmd_ssh, "ssh into a pod")
    p.add_argument("pod")
    p.add_argument("cmd", nargs=argparse.REMAINDER)
    add("delete", cmd_delete, "delete a pod").add_argument("pod")
    add("fetch", cmd_fetch, "download results from a pod").add_argument("pod")
    p = add("evaluate", cmd_evaluate, "run one evaluation on a pod")
    p.add_argument("pod", help="pod id (use DRYRUN with --dry-run)")
    p.add_argument("--base", required=True, help="baseline git ref")
    p.add_argument("--cand", required=True, help="candidate git ref")
    p.add_argument("--logics")
    p.add_argument("--jobs", type=int, default=6, help="parallel jobs on the pod (8 vCPU: 6)")
    p.add_argument("--repeats", type=int, default=2)
    p.add_argument("--fuzz-count", type=int, default=300)
    p.add_argument("--fuzz-seed", type=int)
    p.add_argument("--margin-rel", type=float, default=0.03)
    p.add_argument("--margin-abs", type=float, default=0.05)
    p.add_argument("--delete", action="store_true", help="delete the pod at the end, always")

    p = add("full", cmd_full, "create a pod, run all of one logic with each solver, delete it")
    p.add_argument("logic")
    p.add_argument("--ref", default="HEAD", help="commit to build and run (default HEAD)")
    p.add_argument("--timeout", type=float, default=10, help="CPU seconds per benchmark")
    p.add_argument("--vcpus", type=int, default=32)
    p.add_argument("--flavor", default=",".join(FLAVORS))
    p.add_argument("--volume-gb", type=int, default=60)
    # CPU pods mount no volume: the benchmarks live on the container disk.
    p.add_argument("--disk-gb", type=int, default=150, help="container disk")
    p.add_argument("--jobs", type=int, help="parallel runs (default vcpus/2)")
    p.add_argument("--mem-gb", type=float, help="memory cap per run (default 80%% of RAM/jobs)")
    p.add_argument("--max-mb", type=float, default=3000, help="largest archive to download")
    p.add_argument("--poll", type=int, default=120, help="seconds between progress checks")
    p.add_argument("--max-hours", type=float, default=12, help="then fetch and delete anyway")

    args = ap.parse_args()
    sys.exit(args.func(args) or 0)


if __name__ == "__main__":
    main()
