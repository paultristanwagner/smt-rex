#!/usr/bin/env bash
# Prepare a RunPod CPU pod (Ubuntu, runpod/base:0.6.2-cpu, as root) for evaluate.py:
# install single-user Nix, realise the exact toolchain/oracle store paths from the binary
# cache, and write /opt/smtrex/env.sh (PATH, Z3, CVC5).
#
#   bash setup.sh [store-paths.txt]          # on the pod; idempotent
#   bash setup.sh --dry-run [store-paths.txt]  # print what would run, change nothing
#
# Run by `pod.py evaluate`; you rarely call it by hand.
set -euo pipefail

DRY=0
if [ "${1:-}" = "--dry-run" ]; then DRY=1; shift; fi
HERE=$(cd "$(dirname "$0")" && pwd)
PATHS_FILE=${1:-$HERE/store-paths.txt}
TOOLS=/opt/smtrex

run() {
  if [ "$DRY" = 1 ]; then echo "+ $*"; else "$@"; fi
}

store_path() {  # store_path NAME -> the store path listed for NAME
  awk -v n="$1" '$1 == n { print $2 }' "$PATHS_FILE"
}

if [ "$DRY" = 0 ] && [ "$(id -u)" != 0 ]; then
  echo "setup.sh: run as root (the RunPod default)" >&2
  exit 1
fi
[ -f "$PATHS_FILE" ] || { echo "setup.sh: no $PATHS_FILE" >&2; exit 1; }

# 1. Nix, single-user, as root.
if [ -e /root/.nix-profile/etc/profile.d/nix.sh ]; then
  echo "nix: already installed"
else
  for tool in curl xz; do
    if ! command -v "$tool" >/dev/null; then
      run apt-get update -qq
      run env DEBIAN_FRONTEND=noninteractive apt-get install -y -qq curl xz-utils ca-certificates
      break
    fi
  done
  # These images have no `nixbld` group, which the installer requires unless
  # build-users-group is set empty before installing.
  run mkdir -p /etc/nix
  if [ "$DRY" = 1 ]; then
    echo "+ write /etc/nix/nix.conf: build-users-group = (empty), cache.nixos.org"
  else
    cat > /etc/nix/nix.conf <<'EOF'
build-users-group =
experimental-features = nix-command flakes
substituters = https://cache.nixos.org/
trusted-public-keys = cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY=
sandbox = false
EOF
  fi
  run curl -fsSL -o /tmp/nix-install https://nixos.org/nix/install
  run env USER=root sh /tmp/nix-install --no-daemon --yes
fi
if [ "$DRY" = 0 ]; then
  # shellcheck disable=SC1091
  . /root/.nix-profile/etc/profile.d/nix.sh
fi

# 2. The exact store paths, from the binary cache (nothing is built).
paths=$(awk '!/^#/ && NF == 2 { print $2 }' "$PATHS_FILE")
# shellcheck disable=SC2086
run nix-store -r $paths

# 3. One bin directory and an env file.
Z3=$(store_path z3)/bin/z3
CVC5=$(store_path cvc5)/bin/cvc5
run mkdir -p "$TOOLS/bin"
for exe in "$Z3" "$CVC5" "$(store_path cargo)/bin/cargo" \
           "$(store_path rustc)/bin/rustc" "$(store_path cc)/bin/cc" \
           "$(store_path cc)/bin/gcc" "$(store_path cc)/bin/ld"; do
  run ln -sfn "$exe" "$TOOLS/bin/$(basename "$exe")"
done
if [ "$DRY" = 1 ]; then
  echo "+ write $TOOLS/env.sh"
else
  cat > "$TOOLS/env.sh" <<EOF
export PATH=$TOOLS/bin:\$PATH
export Z3=$Z3
export CVC5=$CVC5
export CARGO_HOME=/root/.cargo
EOF
  # shellcheck disable=SC1091
  . "$TOOLS/env.sh"
  echo "tools:"
  z3 --version
  cvc5 --version | head -1
  cargo --version
  rustc --version
  python3 --version
fi
echo "setup done; source $TOOLS/env.sh"
