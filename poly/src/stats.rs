//! Opt-in instrumentation for the NRA stack: global counters and a sampling phase profiler.
//!
//! Inert unless [`start`] was called with `SMTREX_NRA_STATS` set; the solver's behaviour never
//! depends on it, and when disabled every call is one relaxed atomic load.
//!
//! - Counters ([`Counter`]) are relaxed atomics: sums via [`add`], maxima via [`max`].
//! - Phases: an algorithmic *outer* phase ([`Outer`]) and an innermost *kernel* ([`Kernel`]),
//!   set by guards that restore the previous phase on drop. A sampler thread histograms the
//!   current (outer, kernel) pair every millisecond, giving the share of wall time per pair.
//! - `SMTREX_NRA_STATS=<seconds>` sets a CPU-time deadline at which the sampler prints the report
//!   and exits the process (status 3), so a timeout still yields a report; otherwise the
//!   front-end calls [`report`] at the end.
//!
//! The report is one line on stderr: `nrastats {json}`.

use std::sync::atomic::{AtomicBool, AtomicU64, AtomicU8, Ordering::Relaxed};
use std::sync::OnceLock;
use std::time::{Duration, Instant};

static ENABLED: AtomicBool = AtomicBool::new(false);
static OUTER: AtomicU8 = AtomicU8::new(0);
static KERNEL: AtomicU8 = AtomicU8::new(0);

macro_rules! enum_names {
    ($name:ident { $($v:ident = $s:literal),* $(,)? }) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        #[repr(u8)]
        pub enum $name { $($v),* }
        impl $name {
            pub const ALL: &'static [$name] = &[$($name::$v),*];
            pub fn name(self) -> &'static str {
                match self { $($name::$v => $s),* }
            }
        }
    };
}

enum_names!(Outer {
    // outside any marked phase
    Other = "other",
    Encode = "encode",
    Sat = "sat",
    Lra = "lra",
    NraPrep = "nra_prep",
    ModelReuse = "model_reuse",
    CovIntervals = "cov_intervals",
    CovSample = "cov_sample",
    CovProject = "cov_project",
    CovCell = "cov_cell",
    CadProject = "cad_project",
    CadLift = "cad_lift",
    SelfCheck = "selfcheck",
});

enum_names!(Kernel {
    None = "-",
    SignInterval = "sign_interval",
    SignAnnihilator = "sign_annihilator",
    CountRoots = "count_roots_psc",
    Candidates = "candidates_resultant",
    RealRoots = "univ_real_roots",
    AlgArith = "alg_arith",
    AlgCmp = "alg_cmp",
    Psc = "psc_resultant",
    Gcd = "gcd_basis",
});

enum_names!(Counter {
    // NRA theory: complete checks and the components they decide
    NraChecks = "nra_checks",
    NraConflicts = "nra_conflicts",
    NraTrivialConflicts = "nra_trivial_conflicts",
    Components = "components",
    ModelReuses = "model_reuses",
    DecidedSat = "decided_sat",
    CompVarsSum = "comp_vars_sum",
    CompVarsMax = "comp_vars_max",
    CompConsSum = "comp_cons_sum",
    CompConsMax = "comp_cons_max",
    CompNonlinSum = "comp_nonlinear_cons_sum",
    CompMaxDeg = "comp_max_deg",
    CoreSum = "core_sum",
    CoreMax = "core_max",
    CoreCompSum = "core_comp_sum",
    // coverings and CAD
    Samples = "samples",
    IrrationalSamples = "irrational_samples",
    SampleDegMax = "sample_deg_max",
    PointGaps = "point_gap_samples",
    IrrationalPointGaps = "point_gap_samples_irrational",
    Characterisations = "characterisations",
    Nullifications = "nullifications",
    Projections = "projections",
    ProjCacheHits = "proj_cache_hits",
    ProjInSum = "proj_in_polys_sum",
    ProjInMax = "proj_in_polys_max",
    ProjOutSum = "proj_out_polys_sum",
    ProjOutMax = "proj_out_polys_max",
    ProjDegMax = "proj_deg_max",
    CadCells = "cad_cells",
    // kernels
    SignAt = "sign_at",
    Annihilators = "annihilators",
    AnnihDegMax = "annihilator_deg_max",
    RootsAt = "roots_at",
    RootsAtIrr = "roots_at_irrational",
    PointDegMax = "point_deg_prod_max",
    CandDegMax = "candidate_deg_max",
    AlgOps = "alg_irr_ops",
    AlgOpDegMax = "alg_op_deg_max",
});

const NC: usize = Counter::ALL.len();
const NO: usize = Outer::ALL.len();
const NK: usize = Kernel::ALL.len();

static COUNTERS: [AtomicU64; NC] = [const { AtomicU64::new(0) }; NC];
static PROFILE: [AtomicU64; NO * NK] = [const { AtomicU64::new(0) }; NO * NK];
static TICKS: AtomicU64 = AtomicU64::new(0);
static START: OnceLock<Instant> = OnceLock::new();

#[inline]
pub fn enabled() -> bool {
    ENABLED.load(Relaxed)
}

#[inline]
pub fn add(c: Counter, n: u64) {
    if enabled() {
        COUNTERS[c as usize].fetch_add(n, Relaxed);
    }
}

#[inline]
pub fn max(c: Counter, n: u64) {
    if enabled() {
        COUNTERS[c as usize].fetch_max(n, Relaxed);
    }
}

fn get(c: Counter) -> u64 {
    COUNTERS[c as usize].load(Relaxed)
}

/// Restores the previous outer phase on drop.
pub struct OuterGuard(Option<u8>);
/// Restores the previous kernel on drop.
pub struct KernelGuard(Option<u8>);

/// Enter an outer phase until the guard is dropped.
#[inline]
pub fn outer(p: Outer) -> OuterGuard {
    if !enabled() {
        return OuterGuard(None);
    }
    OuterGuard(Some(OUTER.swap(p as u8, Relaxed)))
}

/// Enter a kernel until the guard is dropped.
#[inline]
pub fn kernel(k: Kernel) -> KernelGuard {
    if !enabled() {
        return KernelGuard(None);
    }
    KernelGuard(Some(KERNEL.swap(k as u8, Relaxed)))
}

impl Drop for OuterGuard {
    fn drop(&mut self) {
        if let Some(p) = self.0 {
            OUTER.store(p, Relaxed);
        }
    }
}

impl Drop for KernelGuard {
    fn drop(&mut self) {
        if let Some(k) = self.0 {
            KERNEL.store(k, Relaxed);
        }
    }
}

/// CPU seconds (user + system) used by this process, from `/proc/self/stat`.
fn cpu_seconds() -> Option<f64> {
    let s = std::fs::read_to_string("/proc/self/stat").ok()?;
    let rest = &s[s.rfind(')')? + 2..];
    let f: Vec<&str> = rest.split_whitespace().collect();
    // fields 14 and 15 of stat(5) are utime, stime; `rest` starts at field 3
    let ut: f64 = f.get(11)?.parse().ok()?;
    let st: f64 = f.get(12)?.parse().ok()?;
    Some((ut + st) / 100.0)
}

/// Enable the instrumentation if `SMTREX_NRA_STATS` is set (idempotent).
pub fn start() {
    let Some(v) = std::env::var_os("SMTREX_NRA_STATS") else {
        return;
    };
    if ENABLED.swap(true, Relaxed) {
        return;
    }
    START.get_or_init(Instant::now);
    let deadline: Option<f64> = v.to_str().and_then(|s| s.parse().ok());
    std::thread::spawn(move || {
        let mut n: u64 = 0;
        loop {
            std::thread::sleep(Duration::from_millis(1));
            let o = OUTER.load(Relaxed) as usize;
            let k = KERNEL.load(Relaxed) as usize;
            PROFILE[o.min(NO - 1) * NK + k.min(NK - 1)].fetch_add(1, Relaxed);
            TICKS.fetch_add(1, Relaxed);
            n += 1;
            if n.is_multiple_of(50) {
                if let (Some(d), Some(c)) = (deadline, cpu_seconds()) {
                    if c >= d {
                        report("deadline");
                        std::process::exit(3);
                    }
                }
            }
        }
    });
}

/// Print the report line (`nrastats {json}`) to stderr, if enabled.
pub fn report(outcome: &str) {
    if !enabled() {
        return;
    }
    let mut s = String::new();
    s.push_str(&format!("{{\"outcome\":\"{outcome}\""));
    let wall = START.get().map_or(0.0, |t| t.elapsed().as_secs_f64());
    s.push_str(&format!(
        ",\"wall\":{wall:.3},\"cpu\":{:.2}",
        cpu_seconds().unwrap_or(0.0)
    ));
    for c in Counter::ALL {
        s.push_str(&format!(",\"{}\":{}", c.name(), get(*c)));
    }
    s.push_str(&format!(
        ",\"ticks\":{},\"profile\":{{",
        TICKS.load(Relaxed)
    ));
    let mut first = true;
    for o in Outer::ALL {
        for k in Kernel::ALL {
            let v = PROFILE[*o as usize * NK + *k as usize].load(Relaxed);
            if v > 0 {
                if !first {
                    s.push(',');
                }
                first = false;
                s.push_str(&format!("\"{}/{}\":{v}", o.name(), k.name()));
            }
        }
    }
    s.push_str("}}");
    eprintln!("nrastats {s}");
}
