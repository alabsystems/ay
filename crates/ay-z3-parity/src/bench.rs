// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `bench` subcommand — a skeptic-proof differential benchmark campaign.
//!
//! Runs every `.smt2` file under one or more corpus roots through BOTH
//! libraries and reports, per division (= `<root-name>/<top-level-subdir>`):
//! agreement counts, unknown/timeout/crash counts, the sat-vs-unsat DISAGREE
//! count (must be 0; nonzero exit otherwise), and wall-clock ratio statistics
//! (median + geometric mean of AY/z3, decided-by-both files only) with >2x
//! win/loss counts.
//!
//! Isolation model: each (file, solver) pair is evaluated in a fresh child
//! process (the hidden `bench-one` mode). This gives (a) crash isolation — a
//! solver abort cannot take down or bias the campaign, (b) clean hard
//! timeouts — the child is SIGKILLed, so no leaked thread keeps burning CPU
//! and skewing later measurements, and (c) honest timing — the child measures
//! wall time strictly around `Z3_eval_smtlib2_string`, excluding process
//! spawn, `dlopen`, and file I/O.
//!
//! Outputs: a stdout table, a JSON certificate, and a markdown report with an
//! auto-populated "where z3 wins" section. Nothing is sampled or filtered:
//! every `.smt2` under every given root is run and accounted for.

use std::collections::BTreeMap;
use std::io::Read as _;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::{Duration, Instant, SystemTime};

use crate::diff::{verdicts_of, Verdict};
use crate::loader;

/// Minimum wall time (seconds) used when forming AY/z3 ratios, to keep timer
/// granularity on trivially fast files from fabricating huge ratios.
const RATIO_FLOOR_SECS: f64 = 0.0001; // 0.1 ms

/// A >2x speed win/loss is only counted when the SLOWER side took at least
/// this long; below it, both solvers are effectively instant and the ratio is
/// scheduling noise, so the file counts as a tie.
const WIN_LOSS_MIN_SECS: f64 = 0.010; // 10 ms

/// Grace period past the timeout before the child is SIGKILLed. The child
/// self-reports eval-only wall time; any result whose eval time exceeds the
/// budget is recorded as a timeout regardless of the grace.
const KILL_GRACE: Duration = Duration::from_secs(2);

// ---------------------------------------------------------------------------
// Child mode: `bench-one <lib> <file>`
// ---------------------------------------------------------------------------

/// Child-process entry point. Loads ONE library, evaluates ONE script, and
/// prints `AYZ3_WALL_NS <ns>` followed by the solver's raw output. The wall
/// time covers exactly the `Z3_eval_smtlib2_string` call.
///
/// Exit codes: 0 ok, 3 unreadable input, 4 library load failure. Any other
/// termination (signal, abort) is observed by the parent as a solver crash.
pub(crate) fn run_child(lib_path: &Path, file: &Path) -> i32 {
    let lib = match loader::open_local(lib_path) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("bench-one: {e}");
            return 4;
        }
    };
    let api = match loader::load_api(&lib) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("bench-one: {e}");
            return 4;
        }
    };
    let script = match std::fs::read_to_string(file) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("bench-one: read {}: {e}", file.display());
            return 3;
        }
    };
    let Ok(cscript) = std::ffi::CString::new(script) else {
        eprintln!(
            "bench-one: {} contains an interior NUL byte",
            file.display()
        );
        return 3;
    };

    // SAFETY: `api` holds valid function pointers into the library opened
    // above; each is called at its declared signature. The output string is
    // owned by the context and copied out before teardown.
    unsafe {
        let cfg = (api.mk_config)();
        let ctx = (api.mk_context)(cfg);
        let t0 = Instant::now();
        let out_ptr = (api.eval)(ctx, cscript.as_ptr());
        let wall = t0.elapsed();
        let out = if out_ptr.is_null() {
            String::new()
        } else {
            std::ffi::CStr::from_ptr(out_ptr)
                .to_string_lossy()
                .into_owned()
        };
        // Report BEFORE teardown so a teardown crash still surfaces as a
        // nonzero exit (the parent treats any nonzero exit as a crash).
        let mut stdout = std::io::stdout();
        let _ = writeln!(stdout, "AYZ3_WALL_NS {}", wall.as_nanos());
        let _ = stdout.write_all(out.as_bytes());
        let _ = stdout.flush();
        (api.del_context)(ctx);
        (api.del_config)(cfg);
    }
    0
}

// ---------------------------------------------------------------------------
// Parent-side outcome model
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
enum OutcomeKind {
    /// Ordered verdict tokens, one per `(check-sat)`.
    Verdicts(Vec<Verdict>),
    /// Exceeded the wall-clock budget (killed, or self-reported over budget).
    Timeout,
    /// The solver process died (signal / abort / nonzero exit).
    Crash(String),
    /// The harness could not feed the file (unreadable / interior NUL).
    InputError(String),
}

#[derive(Clone, Debug)]
struct BenchOutcome {
    kind: OutcomeKind,
    /// Eval-only wall time as self-reported by the child; for timeouts this
    /// is clamped to the budget, for crashes it is the parent-observed span.
    wall: Duration,
}

impl BenchOutcome {
    fn label(&self) -> String {
        match &self.kind {
            OutcomeKind::Verdicts(v) if v.is_empty() => "-".to_string(),
            OutcomeKind::Verdicts(v) => v.iter().map(|x| x.as_str()).collect::<Vec<_>>().join(","),
            OutcomeKind::Timeout => "timeout".to_string(),
            OutcomeKind::Crash(_) => "crash".to_string(),
            OutcomeKind::InputError(_) => "input-error".to_string(),
        }
    }

    /// Failure detail (crash signal / harness error), `None` for normal runs.
    fn detail(&self) -> Option<&str> {
        match &self.kind {
            OutcomeKind::Crash(d) | OutcomeKind::InputError(d) => Some(d.as_str()),
            _ => None,
        }
    }

    /// Decisive = produced at least one verdict and no `unknown`.
    fn decided(&self) -> bool {
        matches!(&self.kind, OutcomeKind::Verdicts(v)
            if !v.is_empty() && v.iter().all(|x| *x != Verdict::Unknown))
    }

    /// Ran to completion but produced no verdict at all (typically an
    /// `(error ...)`-only output, e.g. an unsupported logic or command).
    fn no_verdict(&self) -> bool {
        matches!(&self.kind, OutcomeKind::Verdicts(v) if v.is_empty())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Category {
    AgreeSat,
    AgreeUnsat,
    /// Both produced the identical multi-check verdict list mixing sat+unsat.
    AgreeMixed,
    /// Verdict lists identical but contain at least one `unknown`.
    BothUnknown,
    /// AY answered `unknown` where z3 decided — AY incompleteness.
    AyUnknownZ3Decided,
    /// z3 answered `unknown` where AY decided — AY strictly stronger here.
    Z3UnknownAyDecided,
    TimeoutAy,
    TimeoutZ3,
    TimeoutBoth,
    CrashAy,
    CrashZ3,
    CrashBoth,
    /// Count mismatch, no verdicts at all, or a harness-side input error.
    Other,
    /// `sat` vs `unsat` — a SOUNDNESS BUG. Must be zero.
    Disagree,
}

impl Category {
    fn label(self) -> &'static str {
        match self {
            Category::AgreeSat => "AGREE-sat",
            Category::AgreeUnsat => "AGREE-unsat",
            Category::AgreeMixed => "AGREE-mixed",
            Category::BothUnknown => "BOTH-unknown",
            Category::AyUnknownZ3Decided => "AY-unknown-z3-decided",
            Category::Z3UnknownAyDecided => "Z3-unknown-ay-decided",
            Category::TimeoutAy => "TIMEOUT-ay",
            Category::TimeoutZ3 => "TIMEOUT-z3",
            Category::TimeoutBoth => "TIMEOUT-both",
            Category::CrashAy => "CRASH-ay",
            Category::CrashZ3 => "CRASH-z3",
            Category::CrashBoth => "CRASH-both",
            Category::Other => "OTHER",
            Category::Disagree => "DISAGREE",
        }
    }
}

/// Classify one file's paired outcomes. Soundness first: any positional
/// sat-vs-unsat conflict is DISAGREE even if other checks also diverged.
fn categorize(ay: &BenchOutcome, z3: &BenchOutcome) -> Category {
    // Disagreement is only observable when both sides produced verdicts.
    if let (OutcomeKind::Verdicts(av), OutcomeKind::Verdicts(zv)) = (&ay.kind, &z3.kind) {
        for (a, z) in av.iter().zip(zv.iter()) {
            if matches!(
                (a, z),
                (Verdict::Sat, Verdict::Unsat) | (Verdict::Unsat, Verdict::Sat)
            ) {
                return Category::Disagree;
            }
        }
    }
    match (&ay.kind, &z3.kind) {
        (OutcomeKind::InputError(_), _) | (_, OutcomeKind::InputError(_)) => {
            return Category::Other
        }
        (OutcomeKind::Crash(_), OutcomeKind::Crash(_)) => return Category::CrashBoth,
        (OutcomeKind::Crash(_), _) => return Category::CrashAy,
        (_, OutcomeKind::Crash(_)) => return Category::CrashZ3,
        (OutcomeKind::Timeout, OutcomeKind::Timeout) => return Category::TimeoutBoth,
        (OutcomeKind::Timeout, _) => return Category::TimeoutAy,
        (_, OutcomeKind::Timeout) => return Category::TimeoutZ3,
        (OutcomeKind::Verdicts(_), OutcomeKind::Verdicts(_)) => {}
    }
    let (OutcomeKind::Verdicts(av), OutcomeKind::Verdicts(zv)) = (&ay.kind, &z3.kind) else {
        unreachable!("all non-verdict combinations returned above");
    };

    if av.is_empty() && zv.is_empty() {
        return Category::Other;
    }
    if av.len() != zv.len() {
        return Category::Other;
    }
    if av == zv {
        if av.iter().any(|v| *v == Verdict::Unknown) {
            return Category::BothUnknown;
        }
        let sat = av.iter().any(|v| *v == Verdict::Sat);
        let unsat = av.iter().any(|v| *v == Verdict::Unsat);
        return match (sat, unsat) {
            (true, false) => Category::AgreeSat,
            (false, true) => Category::AgreeUnsat,
            _ => Category::AgreeMixed,
        };
    }
    // Same length, no sat-vs-unsat conflict, not equal: unknowns on one or
    // both sides. AY incompleteness dominates the classification.
    let ay_unk = av
        .iter()
        .zip(zv.iter())
        .any(|(a, z)| *a == Verdict::Unknown && *z != Verdict::Unknown);
    if ay_unk {
        Category::AyUnknownZ3Decided
    } else {
        Category::Z3UnknownAyDecided
    }
}

// ---------------------------------------------------------------------------
// Running one (file, solver) pair in a child process
// ---------------------------------------------------------------------------

/// Spawn `bench-one` for one (library, file) pair with a hard timebox.
///
/// The child self-reports eval-only wall time on its first stdout line; a
/// result over budget is a timeout even if the child finished in the grace
/// window. A SIGKILLed child is a timeout; any other abnormal exit is a crash.
fn run_one(exe: &Path, lib: &Path, file: &Path, timeout: Duration) -> BenchOutcome {
    let spawn_t0 = Instant::now();
    let mut child = match Command::new(exe)
        .arg("bench-one")
        .arg(lib)
        .arg(file)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
    {
        Ok(c) => c,
        Err(e) => {
            return BenchOutcome {
                kind: OutcomeKind::InputError(format!("spawn failed: {e}")),
                wall: Duration::ZERO,
            }
        }
    };

    // Reader thread drains stdout so a chatty child can never block on a full
    // pipe; the main loop polls for exit and enforces the deadline.
    let mut stdout = child.stdout.take().expect("stdout piped");
    let reader = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = stdout.read_to_end(&mut buf);
        buf
    });

    let deadline = spawn_t0 + timeout + KILL_GRACE;
    let mut killed = false;
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) => {
                if Instant::now() >= deadline && !killed {
                    let _ = child.kill();
                    killed = true;
                }
                std::thread::sleep(Duration::from_millis(2));
            }
            Err(e) => {
                let _ = child.kill();
                let _ = child.wait();
                let _ = reader.join();
                return BenchOutcome {
                    kind: OutcomeKind::InputError(format!("wait failed: {e}")),
                    wall: spawn_t0.elapsed(),
                };
            }
        }
    };
    let bytes = reader.join().unwrap_or_default();
    let text = String::from_utf8_lossy(&bytes);

    if killed {
        return BenchOutcome {
            kind: OutcomeKind::Timeout,
            wall: timeout,
        };
    }
    match status.code() {
        Some(0) => {
            let mut lines = text.splitn(2, '\n');
            let wall_ns: Option<u128> = lines
                .next()
                .and_then(|l| l.strip_prefix("AYZ3_WALL_NS "))
                .and_then(|n| n.trim().parse().ok());
            let output = lines.next().unwrap_or("");
            let wall = wall_ns
                .map(|ns| Duration::from_nanos(u64::try_from(ns).unwrap_or(u64::MAX)))
                .unwrap_or_else(|| spawn_t0.elapsed());
            if wall > timeout {
                // Finished inside the kill grace but over budget: a timeout.
                BenchOutcome {
                    kind: OutcomeKind::Timeout,
                    wall: timeout,
                }
            } else {
                BenchOutcome {
                    kind: OutcomeKind::Verdicts(verdicts_of(output)),
                    wall,
                }
            }
        }
        Some(3) | Some(4) => BenchOutcome {
            kind: OutcomeKind::InputError(format!("bench-one exited {status}")),
            wall: spawn_t0.elapsed(),
        },
        Some(code) => BenchOutcome {
            kind: OutcomeKind::Crash(format!("exit code {code}")),
            wall: spawn_t0.elapsed(),
        },
        None => BenchOutcome {
            kind: OutcomeKind::Crash(format!("killed by signal ({status})")),
            wall: spawn_t0.elapsed(),
        },
    }
}

// ---------------------------------------------------------------------------
// Corpus collection and division mapping
// ---------------------------------------------------------------------------

/// Division of a file relative to its corpus root:
/// `<root-name>/<top-level-subdir>`, or `<root-name>/(top)` for files sitting
/// directly in the root.
fn division_of(root: &Path, file: &Path) -> String {
    let root_name = root
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or("corpus");
    let sub = file
        .strip_prefix(root)
        .ok()
        .and_then(|rel| {
            let mut comps = rel.components();
            let first = comps.next()?;
            // Only a subdirectory (i.e. the file is deeper) names a division.
            comps.next()?;
            first.as_os_str().to_str().map(str::to_string)
        })
        .unwrap_or_else(|| "(top)".to_string());
    format!("{root_name}/{sub}")
}

/// Recursively collect `.smt2` files under each root, tagged with divisions.
fn collect(roots: &[PathBuf]) -> Vec<(String, PathBuf)> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        if dir.is_dir() {
            if let Ok(entries) = std::fs::read_dir(dir) {
                for e in entries.flatten() {
                    walk(&e.path(), out);
                }
            }
        } else if dir.extension().and_then(|e| e.to_str()) == Some("smt2") {
            out.push(dir.to_path_buf());
        }
    }
    let mut tagged = Vec::new();
    for root in roots {
        let mut files = Vec::new();
        walk(root, &mut files);
        files.sort();
        for f in files {
            tagged.push((division_of(root, &f), f));
        }
    }
    tagged
}

// ---------------------------------------------------------------------------
// Statistics
// ---------------------------------------------------------------------------

struct FileRecord {
    division: String,
    file: PathBuf,
    ay: BenchOutcome,
    z3: BenchOutcome,
    category: Category,
    /// AY/z3 wall ratio, present iff decided-by-both (floored at
    /// [`RATIO_FLOOR_SECS`] on both sides).
    ratio: Option<f64>,
}

#[derive(Default)]
struct DivStats {
    files: usize,
    agree_sat: usize,
    agree_unsat: usize,
    agree_mixed: usize,
    both_unknown: usize,
    ay_unknown: usize,
    z3_unknown: usize,
    timeout_ay: usize,
    timeout_z3: usize,
    timeout_both: usize,
    crash_ay: usize,
    crash_z3: usize,
    crash_both: usize,
    other: usize,
    disagree: usize,
    ratios: Vec<f64>,
    ay_wins_2x: usize,
    z3_wins_2x: usize,
}

impl DivStats {
    fn add(&mut self, r: &FileRecord) {
        self.files += 1;
        match r.category {
            Category::AgreeSat => self.agree_sat += 1,
            Category::AgreeUnsat => self.agree_unsat += 1,
            Category::AgreeMixed => self.agree_mixed += 1,
            Category::BothUnknown => self.both_unknown += 1,
            Category::AyUnknownZ3Decided => self.ay_unknown += 1,
            Category::Z3UnknownAyDecided => self.z3_unknown += 1,
            Category::TimeoutAy => self.timeout_ay += 1,
            Category::TimeoutZ3 => self.timeout_z3 += 1,
            Category::TimeoutBoth => self.timeout_both += 1,
            Category::CrashAy => self.crash_ay += 1,
            Category::CrashZ3 => self.crash_z3 += 1,
            Category::CrashBoth => self.crash_both += 1,
            Category::Other => self.other += 1,
            Category::Disagree => self.disagree += 1,
        }
        if let Some(ratio) = r.ratio {
            self.ratios.push(ratio);
            let slower = r.ay.wall.as_secs_f64().max(r.z3.wall.as_secs_f64());
            if slower >= WIN_LOSS_MIN_SECS {
                if ratio < 0.5 {
                    self.ay_wins_2x += 1;
                } else if ratio > 2.0 {
                    self.z3_wins_2x += 1;
                }
            }
        }
    }

    fn merge(&mut self, o: &DivStats) {
        self.files += o.files;
        self.agree_sat += o.agree_sat;
        self.agree_unsat += o.agree_unsat;
        self.agree_mixed += o.agree_mixed;
        self.both_unknown += o.both_unknown;
        self.ay_unknown += o.ay_unknown;
        self.z3_unknown += o.z3_unknown;
        self.timeout_ay += o.timeout_ay;
        self.timeout_z3 += o.timeout_z3;
        self.timeout_both += o.timeout_both;
        self.crash_ay += o.crash_ay;
        self.crash_z3 += o.crash_z3;
        self.crash_both += o.crash_both;
        self.other += o.other;
        self.disagree += o.disagree;
        self.ratios.extend_from_slice(&o.ratios);
        self.ay_wins_2x += o.ay_wins_2x;
        self.z3_wins_2x += o.z3_wins_2x;
    }
}

fn median(sorted: &[f64]) -> Option<f64> {
    if sorted.is_empty() {
        return None;
    }
    let n = sorted.len();
    Some(if n % 2 == 1 {
        sorted[n / 2]
    } else {
        f64::midpoint(sorted[n / 2 - 1], sorted[n / 2])
    })
}

fn geomean(values: &[f64]) -> Option<f64> {
    if values.is_empty() {
        return None;
    }
    let sum: f64 = values.iter().map(|v| v.ln()).sum();
    Some((sum / values.len() as f64).exp())
}

fn ratio_of(ay: &BenchOutcome, z3: &BenchOutcome) -> f64 {
    let a = ay.wall.as_secs_f64().max(RATIO_FLOOR_SECS);
    let z = z3.wall.as_secs_f64().max(RATIO_FLOOR_SECS);
    a / z
}

fn fmt_ratio(r: Option<f64>) -> String {
    match r {
        None => "-".to_string(),
        Some(v) if v >= 100.0 => format!("{v:.0}"),
        Some(v) => format!("{v:.2}"),
    }
}

fn fmt_ms(d: Duration) -> String {
    format!("{:.1}", d.as_secs_f64() * 1000.0)
}

// ---------------------------------------------------------------------------
// Certificate metadata helpers
// ---------------------------------------------------------------------------

/// Parse a benchmark's own `(set-info :status sat|unsat|unknown)` annotation.
/// For disagreements this is ground truth independent of BOTH solvers.
fn parse_declared_status(text: &str) -> Option<&str> {
    let idx = text.find(":status")?;
    text[idx + ":status".len()..]
        .split(|c: char| c.is_whitespace() || c == ')')
        .find(|t| !t.is_empty())
        .filter(|t| matches!(*t, "sat" | "unsat" | "unknown"))
}

/// Declared `:status` of a benchmark file, if annotated.
fn declared_status(file: &Path) -> Option<String> {
    let text = std::fs::read_to_string(file).ok()?;
    parse_declared_status(&text).map(str::to_string)
}

/// SHA-256 of a file via the system `shasum`/`sha256sum` tool — re-runnable
/// by any auditor with the same command.
fn sha256_of(path: &Path) -> Option<String> {
    for (cmd, args) in [("shasum", vec!["-a", "256"]), ("sha256sum", vec![])] {
        let out = Command::new(cmd).args(&args).arg(path).output();
        if let Ok(out) = out {
            if out.status.success() {
                let text = String::from_utf8_lossy(&out.stdout);
                if let Some(tok) = text.split_whitespace().next() {
                    return Some(tok.to_string());
                }
            }
        }
    }
    None
}

/// UTC timestamp `YYYY-MM-DDTHH:MM:SSZ` from the system clock (Howard
/// Hinnant's civil-from-days algorithm; no chrono dependency).
fn utc_now_iso() -> String {
    let secs = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    let days = (secs / 86_400) as i64;
    let rem = secs % 86_400;
    let (h, m, s) = (rem / 3600, (rem % 3600) / 60, rem % 60);
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let mo = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if mo <= 2 { y + 1 } else { y };
    format!("{y:04}-{mo:02}-{d:02}T{h:02}:{m:02}:{s:02}Z")
}

fn host_info() -> serde_json::Value {
    let cpu = Command::new("sysctl")
        .args(["-n", "machdep.cpu.brand_string"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string());
    serde_json::json!({
        "os": std::env::consts::OS,
        "arch": std::env::consts::ARCH,
        "cpu": cpu,
        "logical_cores": std::thread::available_parallelism().map(usize::from).ok(),
    })
}

// ---------------------------------------------------------------------------
// Campaign driver
// ---------------------------------------------------------------------------

pub(crate) struct BenchConfig {
    pub ay: PathBuf,
    pub z3: PathBuf,
    pub roots: Vec<PathBuf>,
    pub timeout_secs: u64,
    pub jobs: usize,
    pub json_stdout: bool,
    pub json_out: PathBuf,
    pub report_out: PathBuf,
}

pub(crate) fn run(cfg: &BenchConfig) -> i32 {
    let files = collect(&cfg.roots);
    if files.is_empty() {
        eprintln!("error: no .smt2 files found under {:?}", cfg.roots);
        return 2;
    }
    let exe = match std::env::current_exe() {
        Ok(p) => p,
        Err(e) => {
            eprintln!("error: cannot locate own executable for child mode: {e}");
            return 2;
        }
    };

    // Preflight: both libraries must load and expose the eval entry points,
    // and we capture their self-reported versions for the certificate.
    let mut versions = Vec::new();
    for (label, path) in [("AY", &cfg.ay), ("z3", &cfg.z3)] {
        match loader::open_local(path) {
            Ok(lib) => {
                if let Err(e) = loader::load_api(&lib) {
                    eprintln!("error ({label} lib): {e}");
                    return 2;
                }
                versions.push(loader::full_version(&lib));
            }
            Err(e) => {
                eprintln!("error ({label} lib): {e}");
                return 2;
            }
        }
    }
    let (ay_version, z3_version) = (versions[0].clone(), versions[1].clone());

    let timeout = Duration::from_secs(cfg.timeout_secs);
    let total = files.len();
    eprintln!(
        "bench: {total} files, timeout {}s, jobs {}, AY={} z3={}",
        cfg.timeout_secs,
        cfg.jobs,
        cfg.ay.display(),
        cfg.z3.display()
    );

    let next = AtomicUsize::new(0);
    let done = AtomicUsize::new(0);
    let slots: Mutex<Vec<Option<FileRecord>>> = Mutex::new((0..total).map(|_| None).collect());
    let campaign_t0 = Instant::now();

    std::thread::scope(|scope| {
        for _ in 0..cfg.jobs.max(1) {
            scope.spawn(|| loop {
                let i = next.fetch_add(1, Ordering::Relaxed);
                if i >= total {
                    break;
                }
                let (division, file) = &files[i];
                let z3 = run_one(&exe, &cfg.z3, file, timeout);
                let ay = run_one(&exe, &cfg.ay, file, timeout);
                let category = categorize(&ay, &z3);
                let ratio = matches!(
                    category,
                    Category::AgreeSat | Category::AgreeUnsat | Category::AgreeMixed
                )
                .then(|| ratio_of(&ay, &z3));
                let n_done = done.fetch_add(1, Ordering::Relaxed) + 1;
                eprintln!(
                    "[{n_done}/{total}] {} {}: z3={} ({}ms) ay={} ({}ms) {}",
                    division,
                    file.file_name().and_then(|n| n.to_str()).unwrap_or("?"),
                    z3.label(),
                    fmt_ms(z3.wall),
                    ay.label(),
                    fmt_ms(ay.wall),
                    category.label()
                );
                slots.lock().expect("slots poisoned")[i] = Some(FileRecord {
                    division: division.clone(),
                    file: file.clone(),
                    ay,
                    z3,
                    category,
                    ratio,
                });
            });
        }
    });

    let records: Vec<FileRecord> = slots
        .into_inner()
        .expect("slots poisoned")
        .into_iter()
        .flatten()
        .collect();
    let campaign_wall = campaign_t0.elapsed();

    let mut divisions: BTreeMap<String, DivStats> = BTreeMap::new();
    for r in &records {
        divisions.entry(r.division.clone()).or_default().add(r);
    }
    let mut totals = DivStats::default();
    for stats in divisions.values() {
        totals.merge(stats);
    }

    // ---- stdout table ----
    let table = render_table(&divisions, &totals);
    if !cfg.json_stdout {
        println!("== ay-z3-parity bench: differential campaign ==");
        println!(
            "  under test (AY):  {}  [{}]",
            cfg.ay.display(),
            ay_version.as_deref().unwrap_or("?")
        );
        println!(
            "  reference (z3):   {}  [{}]",
            cfg.z3.display(),
            z3_version.as_deref().unwrap_or("?")
        );
        println!(
            "  timeout {}s | jobs {} | campaign wall {:.1}s",
            cfg.timeout_secs,
            cfg.jobs,
            campaign_wall.as_secs_f64()
        );
        println!();
        println!("{table}");
    }

    // ---- JSON certificate ----
    let cert = build_certificate(
        cfg,
        &records,
        &divisions,
        &totals,
        ay_version.as_deref(),
        z3_version.as_deref(),
        campaign_wall,
    );
    let cert_text = serde_json::to_string_pretty(&cert).unwrap_or_default();
    if let Some(dir) = cfg.json_out.parent() {
        let _ = std::fs::create_dir_all(dir);
    }
    if let Err(e) = std::fs::write(&cfg.json_out, &cert_text) {
        eprintln!("error: writing {}: {e}", cfg.json_out.display());
        return 2;
    }
    if cfg.json_stdout {
        println!("{cert_text}");
    }

    // ---- markdown report ----
    let report = render_report(
        cfg,
        &records,
        &divisions,
        &totals,
        ay_version.as_deref(),
        z3_version.as_deref(),
        campaign_wall,
    );
    if let Some(dir) = cfg.report_out.parent() {
        let _ = std::fs::create_dir_all(dir);
    }
    if let Err(e) = std::fs::write(&cfg.report_out, report) {
        eprintln!("error: writing {}: {e}", cfg.report_out.display());
        return 2;
    }

    if !cfg.json_stdout {
        println!();
        println!("certificate: {}", cfg.json_out.display());
        println!("report:      {}", cfg.report_out.display());
        println!();
        if totals.disagree == 0 {
            println!(
                "RESULT: PASS — 0 sat-vs-unsat disagreements across {} files.",
                totals.files
            );
        } else {
            println!(
                "RESULT: FAIL — {} SOUNDNESS DISAGREEMENT(S):",
                totals.disagree
            );
            for r in records.iter().filter(|r| r.category == Category::Disagree) {
                println!(
                    "    {}  declared={} z3={} ay={}",
                    r.file.display(),
                    declared_status(&r.file).unwrap_or_else(|| "(none)".into()),
                    r.z3.label(),
                    r.ay.label()
                );
            }
        }
    }

    i32::from(totals.disagree != 0)
}

// ---------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------

fn stats_row(name: &str, s: &DivStats) -> Vec<String> {
    let mut sorted = s.ratios.clone();
    sorted.sort_by(|a, b| a.partial_cmp(b).expect("no NaN ratios"));
    vec![
        name.to_string(),
        s.files.to_string(),
        s.agree_sat.to_string(),
        s.agree_unsat.to_string(),
        s.agree_mixed.to_string(),
        s.both_unknown.to_string(),
        s.ay_unknown.to_string(),
        s.z3_unknown.to_string(),
        format!("{}/{}/{}", s.timeout_ay, s.timeout_z3, s.timeout_both),
        format!(
            "{}/{}",
            s.crash_ay + s.crash_both,
            s.crash_z3 + s.crash_both
        ),
        s.other.to_string(),
        s.disagree.to_string(),
        fmt_ratio(median(&sorted)),
        fmt_ratio(geomean(&s.ratios)),
        format!("{}/{}", s.ay_wins_2x, s.z3_wins_2x),
    ]
}

const HEADERS: [&str; 15] = [
    "DIVISION",
    "FILES",
    "A-SAT",
    "A-UNSAT",
    "A-MIX",
    "BOTH-UNK",
    "AY-UNK",
    "Z3-UNK",
    "T/O a/z/b",
    "CRASH a/z",
    "OTHER",
    "DISAGREE",
    "MED ay/z3",
    "GEO ay/z3",
    "W/L 2x",
];

fn render_table(divisions: &BTreeMap<String, DivStats>, totals: &DivStats) -> String {
    let mut rows: Vec<Vec<String>> = vec![HEADERS.iter().map(|h| h.to_string()).collect()];
    for (name, s) in divisions {
        rows.push(stats_row(name, s));
    }
    rows.push(stats_row("TOTAL", totals));

    let cols = HEADERS.len();
    let mut widths = vec![0usize; cols];
    for row in &rows {
        for (i, cell) in row.iter().enumerate() {
            widths[i] = widths[i].max(cell.len());
        }
    }
    let mut out = String::new();
    for (ri, row) in rows.iter().enumerate() {
        let line: Vec<String> = row
            .iter()
            .enumerate()
            .map(|(i, cell)| {
                if i == 0 {
                    format!("{cell:<width$}", width = widths[i])
                } else {
                    format!("{cell:>width$}", width = widths[i])
                }
            })
            .collect();
        out.push_str(line.join("  ").trim_end());
        out.push('\n');
        // Rule under the header and above the TOTAL row.
        if ri == 0 || ri + 2 == rows.len() {
            out.push_str(&"-".repeat(widths.iter().sum::<usize>() + 2 * (cols - 1)));
            out.push('\n');
        }
    }
    out
}

fn md_row(cells: &[String]) -> String {
    format!("| {} |", cells.join(" | "))
}

fn build_certificate(
    cfg: &BenchConfig,
    records: &[FileRecord],
    divisions: &BTreeMap<String, DivStats>,
    totals: &DivStats,
    ay_version: Option<&str>,
    z3_version: Option<&str>,
    campaign_wall: Duration,
) -> serde_json::Value {
    let div_json = |name: &str, s: &DivStats| {
        let mut sorted = s.ratios.clone();
        sorted.sort_by(|a, b| a.partial_cmp(b).expect("no NaN ratios"));
        serde_json::json!({
            "name": name,
            "files": s.files,
            "agree_sat": s.agree_sat,
            "agree_unsat": s.agree_unsat,
            "agree_mixed": s.agree_mixed,
            "both_unknown": s.both_unknown,
            "ay_unknown_z3_decided": s.ay_unknown,
            "z3_unknown_ay_decided": s.z3_unknown,
            "timeout_ay": s.timeout_ay,
            "timeout_z3": s.timeout_z3,
            "timeout_both": s.timeout_both,
            "crash_ay": s.crash_ay,
            "crash_z3": s.crash_z3,
            "crash_both": s.crash_both,
            "other": s.other,
            "disagree": s.disagree,
            "decided_by_both": s.ratios.len(),
            "median_wall_ratio_ay_over_z3": median(&sorted),
            "geomean_wall_ratio_ay_over_z3": geomean(&s.ratios),
            "ay_wins_2x": s.ay_wins_2x,
            "z3_wins_2x": s.z3_wins_2x,
        })
    };
    let files_json: Vec<_> = records
        .iter()
        .map(|r| {
            serde_json::json!({
                "file": r.file.display().to_string(),
                "division": r.division,
                "z3": { "outcome": r.z3.label(), "wall_ms": r.z3.wall.as_secs_f64() * 1000.0, "detail": r.z3.detail() },
                "ay": { "outcome": r.ay.label(), "wall_ms": r.ay.wall.as_secs_f64() * 1000.0, "detail": r.ay.detail() },
                "category": r.category.label(),
                "wall_ratio_ay_over_z3": r.ratio,
            })
        })
        .collect();
    let disagree_files: Vec<serde_json::Value> = records
        .iter()
        .filter(|r| r.category == Category::Disagree)
        .map(|r| {
            serde_json::json!({
                "file": r.file.display().to_string(),
                "z3": r.z3.label(),
                "ay": r.ay.label(),
                "declared_status": declared_status(&r.file),
            })
        })
        .collect();
    serde_json::json!({
        "kind": "ay-z3-bench-certificate",
        "format_version": 1,
        "generated_utc": utc_now_iso(),
        "invocation": std::env::args().collect::<Vec<_>>().join(" "),
        "host": host_info(),
        "ay_lib": {
            "path": cfg.ay.display().to_string(),
            "sha256": sha256_of(&cfg.ay),
            "full_version": ay_version,
        },
        "z3_lib": {
            "path": cfg.z3.display().to_string(),
            "sha256": sha256_of(&cfg.z3),
            "full_version": z3_version,
        },
        "timeout_secs": cfg.timeout_secs,
        "jobs": cfg.jobs,
        "roots": cfg.roots.iter().map(|r| r.display().to_string()).collect::<Vec<_>>(),
        "campaign_wall_secs": campaign_wall.as_secs_f64(),
        "methodology": {
            "isolation": "each (file, solver) pair runs in a fresh child process; wall time measured inside the child strictly around Z3_eval_smtlib2_string (excludes spawn/dlopen/file-read)",
            "timeout": "hard SIGKILL at timeout + 2s grace; any eval wall over the budget is recorded as timeout",
            "ratio_floor_secs": RATIO_FLOOR_SECS,
            "win_loss_min_secs": WIN_LOSS_MIN_SECS,
            "decided_by_both": "verdict lists equal, nonempty, no unknown, no timeout/crash — the only files entering ratio statistics",
        },
        "divisions": divisions.iter().map(|(n, s)| div_json(n, s)).collect::<Vec<_>>(),
        "totals": div_json("TOTAL", totals),
        "files": files_json,
        "disagree_files": disagree_files,
        "pass": totals.disagree == 0,
    })
}

#[allow(clippy::too_many_lines)]
fn render_report(
    cfg: &BenchConfig,
    records: &[FileRecord],
    divisions: &BTreeMap<String, DivStats>,
    totals: &DivStats,
    ay_version: Option<&str>,
    z3_version: Option<&str>,
    campaign_wall: Duration,
) -> String {
    use std::fmt::Write as _;
    let mut md = String::new();
    let _ = writeln!(md, "# AY vs z3 — differential benchmark report");
    let _ = writeln!(md);
    let _ = writeln!(
        md,
        "Generated {} by `ay-z3-parity bench`. Every number below is mechanically",
        utc_now_iso()
    );
    let _ = writeln!(
        md,
        "derived from the run recorded in the JSON certificate next to this file;"
    );
    let _ = writeln!(
        md,
        "nothing is hand-edited. No file under any corpus root was skipped or sampled."
    );
    let _ = writeln!(md);
    let _ = writeln!(md, "## Reproduce");
    let _ = writeln!(md);
    let _ = writeln!(md, "```sh");
    let _ = writeln!(
        md,
        "# 1. build the solver library under test (release) and this tool"
    );
    let _ = writeln!(md, "cargo build --release -p ay-ffi");
    let _ = writeln!(md, "cargo build --release -p ay-z3-parity");
    let _ = writeln!(
        md,
        "# 2. fetch the SMT-LIB samples (see benchmarks/smtlib-sample/MANIFEST.md"
    );
    let _ = writeln!(
        md,
        "#    for URLs, checksums, and the deterministic sampling rule)"
    );
    let _ = writeln!(md, "# 3. run the campaign (exact invocation of this run):");
    let _ = writeln!(md, "{}", std::env::args().collect::<Vec<_>>().join(" "));
    let _ = writeln!(md, "```");
    let _ = writeln!(md);
    let _ = writeln!(md, "| | |");
    let _ = writeln!(md, "|---|---|");
    let _ = writeln!(md, "| AY library | `{}` |", cfg.ay.display());
    let _ = writeln!(
        md,
        "| AY sha256 | `{}` |",
        sha256_of(&cfg.ay).unwrap_or_else(|| "?".into())
    );
    let _ = writeln!(
        md,
        "| AY `Z3_get_full_version` | {} |",
        ay_version.unwrap_or("?")
    );
    let _ = writeln!(md, "| z3 library | `{}` |", cfg.z3.display());
    let _ = writeln!(
        md,
        "| z3 sha256 | `{}` |",
        sha256_of(&cfg.z3).unwrap_or_else(|| "?".into())
    );
    let _ = writeln!(
        md,
        "| z3 `Z3_get_full_version` | {} |",
        z3_version.unwrap_or("?")
    );
    let _ = writeln!(
        md,
        "| timeout per (file, solver) | {} s |",
        cfg.timeout_secs
    );
    let _ = writeln!(md, "| parallel jobs | {} |", cfg.jobs);
    let _ = writeln!(
        md,
        "| campaign wall time | {:.1} s |",
        campaign_wall.as_secs_f64()
    );
    let _ = writeln!(md, "| host | {} |", host_info());
    let _ = writeln!(md);

    // Soundness verdict, first and prominent.
    let _ = writeln!(md, "## Soundness: sat-vs-unsat disagreements");
    let _ = writeln!(md);
    if totals.disagree == 0 {
        let _ = writeln!(
            md,
            "**DISAGREE = 0** across {} files. On every instance both solvers decided,",
            totals.files
        );
        let _ = writeln!(md, "the verdicts matched.");
    } else {
        let _ = writeln!(
            md,
            "**DISAGREE = {} — SOUNDNESS BUG(S). This run FAILS.**",
            totals.disagree
        );
        let _ = writeln!(md);
        let _ = writeln!(
            md,
            "The \"declared\" column is the benchmark's own `(set-info :status ...)`"
        );
        let _ = writeln!(
            md,
            "annotation — ground truth independent of both solvers. A solver whose"
        );
        let _ = writeln!(md, "verdict contradicts it has the wrong answer.");
        let _ = writeln!(md);
        let _ = writeln!(md, "| file | declared | z3 | AY |");
        let _ = writeln!(md, "|---|---|---|---|");
        for r in records.iter().filter(|r| r.category == Category::Disagree) {
            let _ = writeln!(
                md,
                "| `{}` | {} | {} | {} |",
                r.file.display(),
                declared_status(&r.file).unwrap_or_else(|| "(none)".into()),
                r.z3.label(),
                r.ay.label()
            );
        }
    }
    let _ = writeln!(md);

    // Per-division table.
    let _ = writeln!(md, "## Per-division results");
    let _ = writeln!(md);
    let _ = writeln!(
        md,
        "{}",
        md_row(&HEADERS.iter().map(|h| h.to_string()).collect::<Vec<_>>())
    );
    let _ = writeln!(md, "|{}", "---|".repeat(HEADERS.len()));
    for (name, s) in divisions {
        let _ = writeln!(md, "{}", md_row(&stats_row(name, s)));
    }
    let _ = writeln!(md, "{}", md_row(&stats_row("**TOTAL**", totals)));
    let _ = writeln!(md);
    let _ = writeln!(
        md,
        "Column key: A-SAT/A-UNSAT/A-MIX = both solvers produced identical decisive"
    );
    let _ = writeln!(
        md,
        "verdicts; BOTH-UNK = identical verdicts containing `unknown`; AY-UNK = AY"
    );
    let _ = writeln!(
        md,
        "`unknown` where z3 decided (AY incompleteness); Z3-UNK = the reverse;"
    );
    let _ = writeln!(
        md,
        "T/O a/z/b = timeouts (AY only / z3 only / both); CRASH a/z = solver process"
    );
    let _ = writeln!(
        md,
        "died (either alone or both); OTHER = verdict-count mismatch or no verdicts;"
    );
    let _ = writeln!(
        md,
        "MED/GEO = median / geometric-mean wall ratio AY/z3 over decided-by-both"
    );
    let _ = writeln!(
        md,
        "files (ratio < 1 means AY is faster); W/L 2x = files where AY / z3 was more"
    );
    let _ = writeln!(
        md,
        "than 2x faster and the slower side took at least {} ms.",
        (WIN_LOSS_MIN_SECS * 1000.0) as u64
    );
    let _ = writeln!(md);

    // ---- Where z3 wins (auto-populated, honest) ----
    let _ = writeln!(md, "## Where z3 wins");
    let _ = writeln!(md);
    let mut z3_wins_any = false;

    let ay_crashes: Vec<&FileRecord> = records
        .iter()
        .filter(|r| matches!(r.category, Category::CrashAy | Category::CrashBoth))
        .collect();
    if !ay_crashes.is_empty() {
        z3_wins_any = true;
        let _ = writeln!(md, "### AY crashes ({})", ay_crashes.len());
        let _ = writeln!(md);
        for r in ay_crashes.iter().take(30) {
            let detail = r.ay.detail().unwrap_or("?");
            let _ = writeln!(
                md,
                "- `{}` — {} (z3: {})",
                r.file.display(),
                detail,
                r.z3.label()
            );
        }
        if ay_crashes.len() > 30 {
            let _ = writeln!(
                md,
                "- … and {} more (see certificate)",
                ay_crashes.len() - 30
            );
        }
        let _ = writeln!(md);
    }

    let ay_to_z3_decided: Vec<&FileRecord> = records
        .iter()
        .filter(|r| r.category == Category::TimeoutAy && r.z3.decided())
        .collect();
    if !ay_to_z3_decided.is_empty() {
        z3_wins_any = true;
        let _ = writeln!(
            md,
            "### AY timed out where z3 decided ({} files)",
            ay_to_z3_decided.len()
        );
        let _ = writeln!(md);
        let _ = writeln!(md, "| file | z3 verdict | z3 ms |");
        let _ = writeln!(md, "|---|---|---|");
        for r in ay_to_z3_decided.iter().take(20) {
            let _ = writeln!(
                md,
                "| `{}` | {} | {} |",
                r.file.display(),
                r.z3.label(),
                fmt_ms(r.z3.wall)
            );
        }
        if ay_to_z3_decided.len() > 20 {
            let _ = writeln!(
                md,
                "| … and {} more (see certificate) | | |",
                ay_to_z3_decided.len() - 20
            );
        }
        let _ = writeln!(md);
    }

    if totals.ay_unknown > 0 {
        z3_wins_any = true;
        let _ = writeln!(
            md,
            "### AY answered `unknown` where z3 decided ({} files)",
            totals.ay_unknown
        );
        let _ = writeln!(md);
        for (name, s) in divisions {
            if s.ay_unknown == 0 {
                continue;
            }
            let _ = writeln!(md, "- **{name}**: {} of {} files", s.ay_unknown, s.files);
            for r in records
                .iter()
                .filter(|r| r.division == *name && r.category == Category::AyUnknownZ3Decided)
                .take(8)
            {
                let _ = writeln!(
                    md,
                    "  - `{}` (z3: {} in {} ms)",
                    r.file.display(),
                    r.z3.label(),
                    fmt_ms(r.z3.wall)
                );
            }
            if s.ay_unknown > 8 {
                let _ = writeln!(md, "  - … and {} more (see certificate)", s.ay_unknown - 8);
            }
        }
        let _ = writeln!(md);
    }

    let ay_no_verdict: Vec<&FileRecord> = records
        .iter()
        .filter(|r| r.category == Category::Other && r.ay.no_verdict() && r.z3.decided())
        .collect();
    if !ay_no_verdict.is_empty() {
        z3_wins_any = true;
        let _ = writeln!(
            md,
            "### AY produced no verdict where z3 decided ({} files)",
            ay_no_verdict.len()
        );
        let _ = writeln!(md);
        let _ = writeln!(
            md,
            "AY ran to completion but emitted no `sat`/`unsat` token — typically an"
        );
        let _ = writeln!(
            md,
            "`(error ...)`-only reply such as an unsupported logic or command in the"
        );
        let _ = writeln!(
            md,
            "`Z3_eval_smtlib2_string` path. These count as OTHER in the table."
        );
        let _ = writeln!(md);
        for r in ay_no_verdict.iter().take(15) {
            let _ = writeln!(
                md,
                "- `{}` (z3: {} in {} ms)",
                r.file.display(),
                r.z3.label(),
                fmt_ms(r.z3.wall)
            );
        }
        if ay_no_verdict.len() > 15 {
            let _ = writeln!(
                md,
                "- … and {} more (see certificate)",
                ay_no_verdict.len() - 15
            );
        }
        let _ = writeln!(md);
    }

    let mut slowdowns: Vec<&FileRecord> = records
        .iter()
        .filter(|r| {
            r.ratio.is_some_and(|x| x > 2.0)
                && r.ay.wall.as_secs_f64().max(r.z3.wall.as_secs_f64()) >= WIN_LOSS_MIN_SECS
        })
        .collect();
    slowdowns.sort_by(|a, b| b.ratio.partial_cmp(&a.ratio).expect("no NaN ratios"));
    if !slowdowns.is_empty() {
        z3_wins_any = true;
        let _ = writeln!(
            md,
            "### z3 more than 2x faster (decided-by-both; {} files, top 20 by ratio)",
            slowdowns.len()
        );
        let _ = writeln!(md);
        let _ = writeln!(md, "| file | verdict | z3 ms | AY ms | AY/z3 |");
        let _ = writeln!(md, "|---|---|---|---|---|");
        for r in slowdowns.iter().take(20) {
            let _ = writeln!(
                md,
                "| `{}` | {} | {} | {} | {} |",
                r.file.display(),
                r.z3.label(),
                fmt_ms(r.z3.wall),
                fmt_ms(r.ay.wall),
                fmt_ratio(r.ratio)
            );
        }
        let _ = writeln!(md);
    }

    if !z3_wins_any {
        let _ = writeln!(
            md,
            "No z3 advantage observed on this corpus: no AY crashes, no AY-only"
        );
        let _ = writeln!(
            md,
            "timeouts on z3-decided files, no AY-unknowns where z3 decided, and no"
        );
        let _ = writeln!(
            md,
            "decided-by-both file where z3 was more than 2x faster (with the slower"
        );
        let _ = writeln!(md, "side over {} ms).", (WIN_LOSS_MIN_SECS * 1000.0) as u64);
        let _ = writeln!(md);
    }

    // ---- Where AY wins (same rules, reversed) ----
    let _ = writeln!(md, "## Where AY wins");
    let _ = writeln!(md);
    let mut ay_wins_any = false;
    let z3_to_ay_decided = records
        .iter()
        .filter(|r| r.category == Category::TimeoutZ3 && r.ay.decided())
        .count();
    if z3_to_ay_decided > 0 {
        ay_wins_any = true;
        let _ = writeln!(
            md,
            "- z3 timed out where AY decided: {z3_to_ay_decided} files"
        );
    }
    if totals.z3_unknown > 0 {
        ay_wins_any = true;
        let _ = writeln!(
            md,
            "- z3 answered `unknown` where AY decided: {} files",
            totals.z3_unknown
        );
    }
    let speedups = records
        .iter()
        .filter(|r| {
            r.ratio.is_some_and(|x| x < 0.5)
                && r.ay.wall.as_secs_f64().max(r.z3.wall.as_secs_f64()) >= WIN_LOSS_MIN_SECS
        })
        .count();
    if speedups > 0 {
        ay_wins_any = true;
        let _ = writeln!(
            md,
            "- AY more than 2x faster (decided-by-both, slower side ≥ {} ms): {} files",
            (WIN_LOSS_MIN_SECS * 1000.0) as u64,
            speedups
        );
    }
    let z3_no_verdict = records
        .iter()
        .filter(|r| r.category == Category::Other && r.z3.no_verdict() && r.ay.decided())
        .count();
    if z3_no_verdict > 0 {
        ay_wins_any = true;
        let _ = writeln!(
            md,
            "- z3 produced no verdict where AY decided: {z3_no_verdict} files"
        );
    }
    let z3_crashes = records
        .iter()
        .filter(|r| matches!(r.category, Category::CrashZ3 | Category::CrashBoth))
        .count();
    if z3_crashes > 0 {
        ay_wins_any = true;
        let _ = writeln!(md, "- z3 crashes: {z3_crashes} files");
    }
    if !ay_wins_any {
        let _ = writeln!(
            md,
            "No AY advantage observed on this corpus under the same rules."
        );
    }
    let _ = writeln!(md);

    let _ = writeln!(md, "## Methodology");
    let _ = writeln!(md);
    let _ = writeln!(
        md,
        "- Both libraries are `dlopen`ed by path; each (file, solver) pair runs in a"
    );
    let _ = writeln!(
        md,
        "  fresh child process (`ay-z3-parity bench-one <lib> <file>`), so a crash or"
    );
    let _ = writeln!(md, "  runaway solve cannot bias any other measurement.");
    let _ = writeln!(
        md,
        "- Wall time is measured inside the child strictly around"
    );
    let _ = writeln!(
        md,
        "  `Z3_eval_smtlib2_string` — process spawn, `dlopen`, and file reading are"
    );
    let _ = writeln!(md, "  excluded, identically for both solvers.");
    let _ = writeln!(
        md,
        "- Timeout: the child is SIGKILLed {}s after the {}s budget; a child that",
        KILL_GRACE.as_secs(),
        cfg.timeout_secs
    );
    let _ = writeln!(
        md,
        "  finishes in the grace window but whose eval time exceeded the budget is"
    );
    let _ = writeln!(md, "  still recorded as a timeout.");
    let _ = writeln!(
        md,
        "- Verdicts are the ordered whole-word `sat`/`unsat`/`unknown` tokens of each"
    );
    let _ = writeln!(
        md,
        "  solver's output; `sat` never substring-matches `unsat`."
    );
    let _ = writeln!(
        md,
        "- Ratio statistics use only decided-by-both files (identical decisive verdict"
    );
    let _ = writeln!(
        md,
        "  lists), with each side floored at {} ms to keep timer granularity from",
        RATIO_FLOOR_SECS * 1000.0
    );
    let _ = writeln!(md, "  fabricating extreme ratios on trivial files.");
    let _ = writeln!(
        md,
        "- z3 is run first, then AY, for every file; ordering is identical across the"
    );
    let _ = writeln!(md, "  corpus and both solvers see the exact same bytes.");
    md
}

// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn verdicts(v: &[Verdict]) -> BenchOutcome {
        BenchOutcome {
            kind: OutcomeKind::Verdicts(v.to_vec()),
            wall: Duration::from_millis(5),
        }
    }
    fn timeout() -> BenchOutcome {
        BenchOutcome {
            kind: OutcomeKind::Timeout,
            wall: Duration::from_secs(20),
        }
    }
    fn crash() -> BenchOutcome {
        BenchOutcome {
            kind: OutcomeKind::Crash("signal 6".into()),
            wall: Duration::from_millis(1),
        }
    }

    #[test]
    fn categorize_soundness_dominates() {
        use Verdict::*;
        assert_eq!(
            categorize(&verdicts(&[Sat]), &verdicts(&[Unsat])),
            Category::Disagree
        );
        // Disagreement at any position wins over unknown noise elsewhere.
        assert_eq!(
            categorize(&verdicts(&[Unknown, Sat]), &verdicts(&[Sat, Unsat])),
            Category::Disagree
        );
    }

    #[test]
    fn categorize_agreement_classes() {
        use Verdict::*;
        assert_eq!(
            categorize(&verdicts(&[Sat]), &verdicts(&[Sat])),
            Category::AgreeSat
        );
        assert_eq!(
            categorize(&verdicts(&[Unsat]), &verdicts(&[Unsat])),
            Category::AgreeUnsat
        );
        assert_eq!(
            categorize(&verdicts(&[Sat, Unsat]), &verdicts(&[Sat, Unsat])),
            Category::AgreeMixed
        );
        assert_eq!(
            categorize(&verdicts(&[Sat, Unknown]), &verdicts(&[Sat, Unknown])),
            Category::BothUnknown
        );
    }

    #[test]
    fn categorize_unknown_sides() {
        use Verdict::*;
        assert_eq!(
            categorize(&verdicts(&[Unknown]), &verdicts(&[Sat])),
            Category::AyUnknownZ3Decided
        );
        assert_eq!(
            categorize(&verdicts(&[Unsat]), &verdicts(&[Unknown])),
            Category::Z3UnknownAyDecided
        );
        // AY incompleteness dominates when both directions occur.
        assert_eq!(
            categorize(&verdicts(&[Unknown, Sat]), &verdicts(&[Sat, Unknown])),
            Category::AyUnknownZ3Decided
        );
    }

    #[test]
    fn categorize_timeouts_and_crashes() {
        use Verdict::*;
        assert_eq!(
            categorize(&timeout(), &verdicts(&[Sat])),
            Category::TimeoutAy
        );
        assert_eq!(
            categorize(&verdicts(&[Sat]), &timeout()),
            Category::TimeoutZ3
        );
        assert_eq!(categorize(&timeout(), &timeout()), Category::TimeoutBoth);
        assert_eq!(categorize(&crash(), &verdicts(&[Sat])), Category::CrashAy);
        assert_eq!(categorize(&verdicts(&[Sat]), &crash()), Category::CrashZ3);
        assert_eq!(categorize(&crash(), &crash()), Category::CrashBoth);
        assert_eq!(categorize(&crash(), &timeout()), Category::CrashAy);
    }

    #[test]
    fn categorize_count_mismatch_and_empty() {
        use Verdict::*;
        assert_eq!(categorize(&verdicts(&[]), &verdicts(&[])), Category::Other);
        assert_eq!(
            categorize(&verdicts(&[Sat]), &verdicts(&[Sat, Sat])),
            Category::Other
        );
    }

    #[test]
    fn median_and_geomean() {
        assert_eq!(median(&[]), None);
        assert_eq!(median(&[2.0]), Some(2.0));
        assert_eq!(median(&[1.0, 2.0, 4.0]), Some(2.0));
        assert_eq!(median(&[1.0, 2.0, 3.0, 4.0]), Some(2.5));
        let g = geomean(&[0.5, 2.0]).expect("nonempty");
        assert!(
            (g - 1.0).abs() < 1e-12,
            "geomean of reciprocal pair is 1, got {g}"
        );
        assert_eq!(geomean(&[]), None);
    }

    #[test]
    fn ratio_floor_damps_trivial_files() {
        let fast = BenchOutcome {
            kind: OutcomeKind::Verdicts(vec![Verdict::Sat]),
            wall: Duration::from_nanos(200),
        };
        let slow = BenchOutcome {
            kind: OutcomeKind::Verdicts(vec![Verdict::Sat]),
            wall: Duration::from_micros(20),
        };
        // Both below the floor: ratio clamps to 1 rather than 100x.
        assert!((ratio_of(&slow, &fast) - 1.0).abs() < 1e-9);
    }

    #[test]
    fn win_loss_requires_meaningful_time() {
        let mut s = DivStats::default();
        let mk = |ms: u64| BenchOutcome {
            kind: OutcomeKind::Verdicts(vec![Verdict::Sat]),
            wall: Duration::from_millis(ms),
        };
        // 1ms vs 4ms: 4x apart but both trivial — a tie, not a win.
        let ay = mk(1);
        let z3 = mk(4);
        s.add(&FileRecord {
            division: "d".into(),
            file: PathBuf::from("a.smt2"),
            ratio: Some(ratio_of(&ay, &z3)),
            ay,
            z3,
            category: Category::AgreeSat,
        });
        assert_eq!((s.ay_wins_2x, s.z3_wins_2x), (0, 0));
        // 5ms vs 25ms: real 5x win for AY.
        let ay = mk(5);
        let z3 = mk(25);
        s.add(&FileRecord {
            division: "d".into(),
            file: PathBuf::from("b.smt2"),
            ratio: Some(ratio_of(&ay, &z3)),
            ay,
            z3,
            category: Category::AgreeSat,
        });
        assert_eq!((s.ay_wins_2x, s.z3_wins_2x), (1, 0));
    }

    #[test]
    fn division_mapping() {
        let root = PathBuf::from("benchmarks/smt");
        assert_eq!(
            division_of(&root, &root.join("QF_LIA/x.smt2")),
            "smt/QF_LIA"
        );
        assert_eq!(
            division_of(&root, &root.join("QF_LIA/deep/x.smt2")),
            "smt/QF_LIA"
        );
        assert_eq!(division_of(&root, &root.join("top.smt2")), "smt/(top)");
    }

    #[test]
    fn utc_timestamp_shape() {
        let t = utc_now_iso();
        assert_eq!(t.len(), 20, "{t}");
        assert!(t.ends_with('Z'));
        assert_eq!(&t[4..5], "-");
        assert_eq!(&t[10..11], "T");
    }

    #[test]
    fn declared_status_parsing() {
        assert_eq!(
            parse_declared_status("(set-info :status unsat)\n(check-sat)"),
            Some("unsat")
        );
        assert_eq!(parse_declared_status("(set-info :status sat)"), Some("sat"));
        assert_eq!(
            parse_declared_status("(set-info :status unknown)"),
            Some("unknown")
        );
        assert_eq!(parse_declared_status("(set-logic QF_AX)"), None);
        assert_eq!(parse_declared_status("(set-info :status bogus)"), None);
    }

    #[test]
    fn decided_requires_no_unknown() {
        use Verdict::*;
        assert!(verdicts(&[Sat, Unsat]).decided());
        assert!(!verdicts(&[Sat, Unknown]).decided());
        assert!(!verdicts(&[]).decided());
        assert!(!timeout().decided());
    }
}
