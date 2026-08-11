// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `scoreboard` subcommand — a per-division progress tracker for the AY↔z3
//! parity campaign, on THREE metrics at once:
//!
//! * the **z3-agreement** metric (does AY decide what z3 decides, and agree),
//! * the **declared-status** metric (does AY contradict the benchmark's own
//!   `(set-info :status sat|unsat)`) — the only wrong-answer detector that
//!   still works when z3 fails to decide the file, and
//! * AY's own **self-certification** metric (of the answers AY gives, how many
//!   can AY prove to *itself* via the fail-closed `ay solve --self-check`
//!   gate) — the campaign's real, z3-independent north star.
//!
//! For every division subdir under a corpus root, every `.smt2` file is run
//! through AY (via the FFI dylib), z3 (via libz3), and `ay --self-check` (via
//! a CLI binary proved to come from the same clean source revision as the FFI
//! library). Each run is a stopped-exec, resource-enveloped child process,
//! reusing the exact isolation/timing plumbing of the `bench` subcommand, so
//! no crashing or runaway solve can bias or abort the campaign.
//!
//! Output is a compact per-division table plus a persisted JSON certificate
//! carrying all raw per-division and per-file data. Given a prior certificate
//! via `--baseline`, a DELTA column tracks solved% / selfcert% / rating changes
//! across runs. Three things are wrong answers, each surfaced as a prominent
//! WARNING and each forcing a nonzero exit: a `sat`-vs-`unsat` DISAGREE (AY vs
//! z3), a DECLARED-CONFLICT (AY contradicts the file's own `:status`), and a
//! self-check answer that contradicts AY's own eval.
//!
//! The declared-status gate exists because the z3 comparison has a blind spot
//! it cannot see past: when z3 times out there is no DISAGREE to raise, so a
//! wrong AY answer used to be credited as a "beyond z3" win. The benchmark's own
//! annotation catches exactly that case, and `beyond_z3` credit is additionally
//! split into self-certified and unverified so an unproved claim cannot read as
//! demonstrated capability.

use std::collections::{BTreeMap, HashMap};
use std::ffi::OsString;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::{Duration, Instant};

use ay_bench::{PlannedResources, ResourcePlan};

use crate::bench::{
    self, categorize, geomean, host_info, median, ratio_of, resource_evidence, run_one,
    run_selfcheck, sha256_of, spawn_timeboxed, utc_now_iso, BenchOutcome, Category, DeclaredStatus,
    OutcomeKind, SelfCheck, WIN_LOSS_MIN_SECS,
};
use crate::diff::Verdict;
use crate::loader;

/// Schema version of the JSON certificate this build writes.
///
/// * 3 — added the declared-`:status` oracle: per-file `declared` /
///   `declared_conflict`, per-division and total `declared_conflict` (a gate
///   alongside `disagree`), and the `beyond_z3` split into
///   `beyond_z3_self_certified` / `beyond_z3_unverified`.
/// * 2 — the rating ladder (`rating` / `rating_ladder`).
///
/// Older certificates stay readable: the only reader in this crate is
/// [`load_baseline`], which looks every field up by name and degrades a missing
/// one to `new` / `-` in the DELTA column, so a v2 baseline still produces a
/// DELTA for the metrics it does carry.
const FORMAT_VERSION: u64 = 3;

// ---------------------------------------------------------------------------
// Rating-ladder noise floors (documented; see `DivStats::rating`)
// ---------------------------------------------------------------------------

/// WALL noise floor for the rating ladder: a decided-by-both file only enters
/// a speed comparison when the SLOWER side (i.e. `max(ay_wall, z3_wall)`) is at
/// least this long. Below it, both solvers are effectively instant and any
/// ratio is timer/scheduler granularity, not a real speed difference. Equal to
/// [`WIN_LOSS_MIN_SECS`] by construction so the ladder and the >2x win/loss
/// counters agree on what "meaningfully timed" means.
const WALL_FLOOR_SECS: f64 = WIN_LOSS_MIN_SECS; // 10 ms

/// PEAK-RSS noise floor for the rating ladder: a decided-by-both file only
/// enters a memory comparison when the LARGER peak (`max(ay_rss, z3_rss)`) is
/// at least this many bytes. Below it the figure is dominated by the fixed
/// process + dylib baseline both children pay, not by solver working set.
const RSS_FLOOR_BYTES: f64 = 5.0 * 1024.0 * 1024.0; // 5 MB

pub(crate) struct ScoreboardConfig {
    pub ay: PathBuf,
    pub ay_cli: Option<PathBuf>,
    pub z3: PathBuf,
    pub root: PathBuf,
    pub timeout_secs: u64,
    pub jobs: usize,
    pub json_out: PathBuf,
    pub baseline: Option<PathBuf>,
    pub divisions: Option<Vec<String>>,
    /// Append-only per-file journal, written as each file completes. Defaults to
    /// `<json_out>.checkpoint.jsonl`; the certificate is only written at the very
    /// end, so without this a crash at hour 40 of a multi-day corpus run loses
    /// everything.
    pub checkpoint: Option<PathBuf>,
    /// Reuse completed files from the checkpoint instead of re-running them.
    /// Opt-in: silently reusing a stale journal would fabricate results.
    pub resume: bool,
    /// Files sampled PER DIVISION. `None` runs every file. A full SMT-LIB pass
    /// is 438k files (~300h at 20s/file across three solvers), so a bounded
    /// per-track sample is what makes this runnable on a schedule.
    pub sample: Option<usize>,
    /// Sampling seed. The selection is a pure function of (seed, division,
    /// relative path), so the same seed always yields the same set and two runs
    /// are comparable; a different seed is an independent sample of the track.
    pub seed: u64,
    /// Periodically-rewritten JSON status file: done/total, rate, ETA, and
    /// per-division progress. This is how a long run is observed without
    /// tailing a million-line stderr log.
    pub progress: Option<PathBuf>,
}

// ---------------------------------------------------------------------------
// Seeded per-division sampling
// ---------------------------------------------------------------------------

/// FNV-1a 64. Chosen over `DefaultHasher` because the sample must be stable
/// across toolchain versions and machines — a benchmark selection that silently
/// reshuffles when the compiler updates is not reproducible evidence.
fn fnv1a64(seed: u64, bytes: &[u8]) -> u64 {
    let mut h = 0xcbf2_9ce4_8422_2325 ^ seed;
    for b in bytes {
        h ^= u64::from(*b);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

/// Take at most `n` files from EACH division, chosen by hashing (seed, path).
///
/// Hash-ranked rather than evenly-spaced-by-index because the corpus grows: an
/// index rule reshuffles the whole sample when files are added, while the hash
/// rule keeps previously-selected files selected, so a track's numbers stay
/// comparable across corpus refreshes. Execution order is restored to sorted
/// path order afterwards so the run itself stays deterministic.
fn sample_per_division(
    files: Vec<(String, PathBuf)>,
    n: usize,
    seed: u64,
) -> (Vec<(String, PathBuf)>, BTreeMap<String, (usize, usize)>) {
    let mut by_div: BTreeMap<String, Vec<PathBuf>> = BTreeMap::new();
    for (div, f) in files {
        by_div.entry(div).or_default().push(f);
    }
    let mut kept = Vec::new();
    let mut census = BTreeMap::new();
    for (div, mut paths) in by_div {
        let available = paths.len();
        paths.sort_by_cached_key(|p| (fnv1a64(seed, p.as_os_str().as_encoded_bytes()), p.clone()));
        paths.truncate(n);
        paths.sort();
        census.insert(div.clone(), (paths.len(), available));
        kept.extend(paths.into_iter().map(|p| (div.clone(), p)));
    }
    kept.sort();
    (kept, census)
}

// ---------------------------------------------------------------------------
// Checkpoint journal
// ---------------------------------------------------------------------------
//
// One JSON object per line, flushed as each file completes, so a killed or
// crashed run can resume instead of restarting. Only RAW per-solver outcomes are
// persisted; `category` and `ratio` are DERIVED and are recomputed on resume, so
// a journal can never disagree with the current classifier.
//
// Line 0 is a header fingerprinting the run (corpus root, timeout, and the
// sha256 of every binary involved). `--resume` refuses a journal whose header
// does not match the current run, because mixing results from two different
// binaries or timeouts produces a certificate that describes neither.

/// Reconstruct a verdict token written by `Verdict::as_str`.
fn verdict_from_str(s: &str) -> Option<Verdict> {
    match s {
        "sat" => Some(Verdict::Sat),
        "unsat" => Some(Verdict::Unsat),
        "unknown" => Some(Verdict::Unknown),
        _ => None,
    }
}

fn outcome_to_json(o: &BenchOutcome) -> serde_json::Value {
    let (kind, verdicts, detail) = match &o.kind {
        OutcomeKind::Verdicts(v) => (
            "verdicts",
            Some(v.iter().map(|x| x.as_str()).collect::<Vec<_>>()),
            None,
        ),
        OutcomeKind::Timeout => ("timeout", None, None),
        OutcomeKind::MemoryLimit => ("memout", None, None),
        OutcomeKind::Crash(d) => ("crash", None, Some(d.clone())),
        OutcomeKind::InputError(d) => ("input-error", None, Some(d.clone())),
    };
    serde_json::json!({
        "kind": kind,
        "verdicts": verdicts,
        "detail": detail,
        "wall_ns": o.wall.as_nanos() as u64,
        "peak_rss": o.peak_rss,
    })
}

fn outcome_from_json(v: &serde_json::Value) -> Option<BenchOutcome> {
    let detail = || v.get("detail")?.as_str().map(str::to_string);
    let kind = match v.get("kind")?.as_str()? {
        "verdicts" => OutcomeKind::Verdicts(
            v.get("verdicts")?
                .as_array()?
                .iter()
                .map(|x| x.as_str().and_then(verdict_from_str))
                .collect::<Option<Vec<_>>>()?,
        ),
        "timeout" => OutcomeKind::Timeout,
        "memout" => OutcomeKind::MemoryLimit,
        "crash" => OutcomeKind::Crash(detail().unwrap_or_default()),
        "input-error" => OutcomeKind::InputError(detail().unwrap_or_default()),
        _ => return None,
    };
    Some(BenchOutcome {
        kind,
        wall: Duration::from_nanos(v.get("wall_ns")?.as_u64()?),
        peak_rss: v.get("peak_rss").and_then(serde_json::Value::as_u64),
    })
}

fn selfcheck_to_json(s: &SelfCheck) -> serde_json::Value {
    let (kind, verdicts, detail) = match s {
        SelfCheck::Verdicts(v) => (
            "verdicts",
            Some(v.iter().map(|x| x.as_str()).collect::<Vec<_>>()),
            None,
        ),
        SelfCheck::Timeout => ("timeout", None, None),
        SelfCheck::MemoryLimit => ("memout", None, None),
        SelfCheck::Crash(d) => ("crash", None, Some(d.clone())),
        SelfCheck::Error(d) => ("error", None, Some(d.clone())),
    };
    serde_json::json!({ "kind": kind, "verdicts": verdicts, "detail": detail })
}

fn selfcheck_from_json(v: &serde_json::Value) -> Option<SelfCheck> {
    let detail = || {
        v.get("detail")
            .and_then(serde_json::Value::as_str)
            .unwrap_or_default()
            .to_string()
    };
    Some(match v.get("kind")?.as_str()? {
        "verdicts" => SelfCheck::Verdicts(
            v.get("verdicts")?
                .as_array()?
                .iter()
                .map(|x| x.as_str().and_then(verdict_from_str))
                .collect::<Option<Vec<_>>>()?,
        ),
        "timeout" => SelfCheck::Timeout,
        "memout" => SelfCheck::MemoryLimit,
        "crash" => SelfCheck::Crash(detail()),
        "error" => SelfCheck::Error(detail()),
        _ => return None,
    })
}

/// Identity of a run. A journal may only be resumed into an identical one.
fn checkpoint_header(cfg: &ScoreboardConfig, ay_sha: &str, z3_sha: &str) -> serde_json::Value {
    serde_json::json!({
        "checkpoint_schema": 1,
        "root": cfg.root.display().to_string(),
        "timeout_secs": cfg.timeout_secs,
        "divisions": cfg.divisions,
        "ay_sha256": ay_sha,
        "z3_sha256": z3_sha,
    })
}

/// Completed per-file outcomes from a prior run, keyed by file path.
type ResumeMap = HashMap<PathBuf, (BenchOutcome, Option<BenchOutcome>, SelfCheck)>;

/// Load a journal, fail-closed. Returns `Err` when the header is absent or
/// describes a different run; a truncated final line (the normal shape of a
/// crash) is dropped and everything before it is kept.
fn load_checkpoint(path: &Path, expected_header: &serde_json::Value) -> Result<ResumeMap, String> {
    let text = std::fs::read_to_string(path)
        .map_err(|e| format!("cannot read checkpoint {}: {e}", path.display()))?;
    let mut lines = text.lines();
    let header: serde_json::Value = lines
        .next()
        .ok_or_else(|| format!("checkpoint {} is empty", path.display()))
        .and_then(|l| serde_json::from_str(l).map_err(|e| format!("bad checkpoint header: {e}")))?;
    if &header != expected_header {
        return Err(format!(
            "checkpoint {} describes a different run and cannot be resumed.\n  \
             journal: {header}\n  current: {expected_header}",
            path.display()
        ));
    }
    let mut out = ResumeMap::new();
    for line in lines {
        // A crash mid-write leaves a partial last line; skip anything unparsable
        // rather than inventing a record for it.
        let Ok(v) = serde_json::from_str::<serde_json::Value>(line) else {
            continue;
        };
        let (Some(file), Some(ay)) = (
            v.get("file").and_then(serde_json::Value::as_str),
            v.get("ay").and_then(outcome_from_json),
        ) else {
            continue;
        };
        let z3 = v.get("z3").and_then(outcome_from_json);
        let Some(selfcheck) = v.get("self").and_then(selfcheck_from_json) else {
            continue;
        };
        out.insert(PathBuf::from(file), (ay, z3, selfcheck));
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Corpus collection: division = the top-level subdir name under the root.
// ---------------------------------------------------------------------------

/// Division of a file = the first path component under the corpus root (its
/// division subdir), or `(root)` for a file sitting directly in the root.
fn division_of(root: &Path, file: &Path) -> String {
    file.strip_prefix(root)
        .ok()
        .and_then(|rel| {
            let mut comps = rel.components();
            let first = comps.next()?;
            comps.next()?; // only a real subdirectory names a division
            first.as_os_str().to_str().map(str::to_string)
        })
        .unwrap_or_else(|| "(root)".to_string())
}

/// Recursively collect `.smt2` files under `root`, tagged with their division,
/// optionally filtered to a set of division names.
fn collect(root: &Path, only: Option<&[String]>) -> Result<Vec<(String, PathBuf)>, String> {
    /// Hidden directories are never corpus content. `ay-z3-parity fetch` stages
    /// each division through `.{div}.fetch-staging-*` and `.{div}.fetch-backup-*`
    /// siblings inside the corpus root; if one leaks (APFS `remove_dir_all` can
    /// fail with ENOTEMPTY), walking it silently DOUBLE-COUNTS that division's
    /// files under a bogus division name. That happened on the 2026-07-24 full
    /// fetch — the scoreboard started scoring `.AUFDTLIRA.fetch-backup-...` as a
    /// division. Skipping dot-directories makes the scan immune to it.
    fn is_hidden_dir(path: &Path) -> bool {
        path.file_name()
            .and_then(|n| n.to_str())
            .is_some_and(|n| n.starts_with('.'))
    }

    fn walk(path: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
        let metadata = std::fs::symlink_metadata(path)?;
        if metadata.is_dir() {
            let mut entries = std::fs::read_dir(path)?.collect::<Result<Vec<_>, _>>()?;
            entries.sort_by_key(std::fs::DirEntry::path);
            for entry in entries {
                let child = entry.path();
                if child.is_dir() && is_hidden_dir(&child) {
                    continue;
                }
                walk(&child, out)?;
            }
        } else if (metadata.is_file()
            || (metadata.file_type().is_symlink() && std::fs::metadata(path)?.is_file()))
            && path.extension().and_then(|e| e.to_str()) == Some("smt2")
        {
            out.push(path.to_path_buf());
        }
        Ok(())
    }
    let mut files = Vec::new();
    walk(root, &mut files)
        .map_err(|e| format!("cannot enumerate corpus {}: {e}", root.display()))?;
    files.sort();
    Ok(files
        .into_iter()
        .map(|f| (division_of(root, &f), f))
        .filter(|(div, _)| only.map_or(true, |set| set.iter().any(|d| d == div)))
        .collect())
}

// ---------------------------------------------------------------------------
// Per-file record
// ---------------------------------------------------------------------------

struct FileRecord {
    division: String,
    file: PathBuf,
    ay: BenchOutcome,
    /// `None` when z3 is unavailable (AY stands on self-cert alone).
    z3: Option<BenchOutcome>,
    selfcheck: SelfCheck,
    /// The benchmark's own `(set-info :status ...)`. DERIVED from the file on
    /// disk, like `category` and `ratio`, so it is never journalled.
    declared: DeclaredStatus,
    /// AY-vs-z3 category; `None` when z3 is unavailable.
    category: Option<Category>,
    /// AY/z3 wall ratio, present iff decided-by-both.
    ratio: Option<f64>,
}

impl FileRecord {
    fn ay_decided(&self) -> bool {
        self.ay.decided()
    }
    fn z3_decided(&self) -> bool {
        self.z3.as_ref().is_some_and(BenchOutcome::decided)
    }
    fn disagree(&self) -> bool {
        self.category == Some(Category::Disagree)
    }
    fn agree(&self) -> bool {
        matches!(
            self.category,
            Some(Category::AgreeSat | Category::AgreeUnsat | Category::AgreeMixed)
        )
    }
    /// AY's decided answer contradicts the benchmark's OWN declared `:status` —
    /// a wrong answer proved without z3.
    ///
    /// This is the gate z3 cannot supply. When z3 times out there is no
    /// DISAGREE to raise, yet the file itself already states the answer, so
    /// without this check a wrong verdict on a z3-timeout file is invisible —
    /// and worse, gets counted as a `beyond_z3` win.
    fn declared_conflict(&self) -> bool {
        let Some(oracle) = self.declared.decided() else {
            return false;
        };
        let Some(verdicts) = self.ay.verdicts() else {
            return false;
        };
        self.ay_decided() && verdicts.iter().any(|v| verdict_contradicts(*v, oracle))
    }

    /// AY's decided answer matches the benchmark's declared `sat`/`unsat`. The
    /// positive counterpart of [`Self::declared_conflict`]: on a file z3 does
    /// not decide, this is what turns a claim into evidence.
    fn declared_confirmed(&self) -> bool {
        let Some(oracle) = self.declared.decided() else {
            return false;
        };
        self.ay_decided()
            && self
                .ay
                .verdicts()
                .is_some_and(|vs| vs.iter().all(|v| *v == oracle))
    }

    /// AY decides where z3 does not (z3 unknown / timeout / crash / no-verdict).
    ///
    /// A file whose answer is already known wrong is NOT capability: both an
    /// AY-vs-z3 disagreement and a contradiction of the file's own `:status`
    /// disqualify it, so a z3 timeout can no longer convert a wrong answer into
    /// a credit.
    fn beyond_z3(&self) -> bool {
        self.z3.is_some()
            && self.ay_decided()
            && !self.z3_decided()
            && !self.disagree()
            && !self.declared_conflict()
    }
    /// A PAR coverage loss: z3 decides this file but AY does not.
    fn loss(&self) -> bool {
        self.z3_decided() && !self.ay_decided()
    }
    /// Both solvers returned only decisive answers, but their verdict-list
    /// shapes differ (for example one answer versus two). This is not a proved
    /// sat-vs-unsat conflict, but it is not agreement and therefore blocks a
    /// PAR coverage claim.
    fn verdict_shape_mismatch(&self) -> bool {
        self.z3_decided() && self.ay_decided() && self.category == Some(Category::Other)
    }
    /// A PAR wall blocker: decided by both, AY slower than z3 with
    /// the (slower) AY side above the 10 ms noise floor.
    fn wall_slower_than_z3(&self) -> bool {
        if !self.agree() {
            return false;
        }
        let Some(z3) = &self.z3 else { return false };
        let ay = self.ay.wall.as_secs_f64();
        let z = z3.wall.as_secs_f64();
        ay > z && ay >= WIN_LOSS_MIN_SECS
    }
    /// AY self-certifies its own decided answer (self-check emits the same
    /// decisive verdict AY's eval produced).
    fn self_certified(&self) -> bool {
        match (self.ay.verdicts(), self.selfcheck.verdicts()) {
            (Some(a), Some(s)) => a == s,
            _ => false,
        }
    }
    /// AY's self-check contradicts AY's own eval verdict (sat vs unsat) — an
    /// internal soundness alarm, surfaced like a DISAGREE. A verdict-list
    /// shape mismatch is also an alarm: both lanes executed the same input,
    /// so they must observe the same number of check commands.
    fn self_conflict(&self) -> bool {
        match (self.ay.verdicts(), self.selfcheck.verdicts()) {
            (Some(a), Some(s)) => a.len() != s.len() || verdicts_conflict(a, s),
            _ => false,
        }
    }
}

fn verdicts_conflict(a: &[Verdict], b: &[Verdict]) -> bool {
    a.iter()
        .zip(b.iter())
        .any(|(x, y)| verdict_contradicts(*x, *y))
}

/// `sat` against `unsat` — the only pair that proves someone is wrong. An
/// `unknown` on either side contradicts nothing.
fn verdict_contradicts(a: Verdict, b: Verdict) -> bool {
    matches!(
        (a, b),
        (Verdict::Sat, Verdict::Unsat) | (Verdict::Unsat, Verdict::Sat)
    )
}

/// AY/z3 peak-RSS ratio for one file (< 1 = AY leaner), present only when BOTH
/// children reported a peak. Used for the per-file JSON; the division MEM
/// geomean is computed separately over the RSS-floor-eligible subset.
fn rss_ratio(ay: &BenchOutcome, z3: Option<&BenchOutcome>) -> Option<f64> {
    let ay_rss = ay.peak_rss? as f64;
    let z3_rss = z3?.peak_rss? as f64;
    Some(ay_rss / z3_rss.max(1.0))
}

// ---------------------------------------------------------------------------
// Per-division statistics
// ---------------------------------------------------------------------------

#[derive(Default, Clone)]
struct DivStats {
    files: usize,
    z3_decided: usize,
    ay_decided: usize,
    ay_agree: usize,
    disagree: usize,
    beyond: usize,
    /// Among `beyond`: files AY also self-certified. The only part of the
    /// beyond-z3 credit backed by a second AY-independent-of-itself run.
    beyond_certified: usize,
    /// Among `beyond`: files nothing corroborated. Reported separately so an
    /// unverified claim can never be read as demonstrated capability.
    beyond_unverified: usize,
    losses: usize,
    verdict_shape_mismatches: usize,
    self_cert: usize,
    self_conflict: usize,
    /// Files declaring a decided `(set-info :status sat|unsat)` — the
    /// denominator of the declared-status oracle.
    declared_decided: usize,
    /// Among `declared_decided`: AY's decided answer matches the declaration.
    declared_confirmed: usize,
    /// Among `declared_decided`: AY's decided answer CONTRADICTS the
    /// declaration. A wrong answer; must be 0, counted whether or not z3
    /// decided the file.
    declared_conflict: usize,
    /// `ay_wall / z3_wall` over EVERY decided-by-both file, each side floored
    /// at [`bench::RATIO_FLOOR_SECS`] (0.1 ms) — NOT at [`WALL_FLOOR_SECS`].
    /// On a file both solvers finish in microseconds this is timer granularity,
    /// not a speed difference, so the geomean of this vector is dominated by
    /// noise wherever a division is mostly trivial files. Kept for continuity
    /// with published scoreboards; read [`Self::geo_ratio_timed`] instead.
    ratios: Vec<f64>,
    /// `ay_wall / z3_wall` restricted to files whose SLOWER side clears
    /// [`WALL_FLOOR_SECS`] — the same eligibility rule the rating ladder and
    /// the 2x win/loss counters already use. This is the honest speed headline.
    ratios_timed: Vec<f64>,
    /// Σ of AY / z3 wall over decided-by-both files, in seconds. The
    /// aggregate-cost view: unlike any geomean it is not distorted by a long
    /// tail of trivial files, and it answers "how much longer does the whole
    /// division take", which is what a replacement claim actually rests on.
    sum_ay_wall: f64,
    sum_z3_wall: f64,
    ay_wins_2x: usize,
    z3_wins_2x: usize,
    // --- rating-ladder accumulators --------------------------------------
    // "decided-by-both" = files where AY and z3 BOTH returned a decisive
    // sat/unsat (agreement, disagreement, or verdict-shape mismatch alike).
    /// decided-by-both files (the denominator of the speed/memory ladder).
    both_decided: usize,
    /// decided-by-both files whose slower side clears [`WALL_FLOOR_SECS`]
    /// (the only files a speed comparison is drawn on).
    wall_cmp: usize,
    /// among `wall_cmp`: AY strictly slower than z3 — breaks PAR's wall bar.
    wall_losses: usize,
    /// among `wall_cmp`: AY not >= 2x faster (`ay_wall > 0.5 * z3_wall`) —
    /// breaks SUPERIOR's speed bar.
    wall_not_2x: usize,
    /// decided-by-both files whose larger peak clears [`RSS_FLOOR_BYTES`]
    /// (the only files a memory comparison is drawn on).
    rss_cmp: usize,
    /// Among `rss_cmp`: AY not below 80% of z3's peak (`ay_rss >= 0.8 *
    /// z3_rss`) — breaks SUPERIOR's memory bar.
    rss_not_80: usize,
    /// Decided-by-both files lacking either peak-RSS measurement. Missing
    /// evidence fails closed and prevents a SUPERIOR/PERFECT claim.
    rss_missing: usize,
    /// `ay_rss / z3_rss` over `rss_cmp` files (the MEM geomean column).
    rss_ratios: Vec<f64>,
}

impl DivStats {
    fn add(&mut self, r: &FileRecord) {
        self.files += 1;
        if r.z3_decided() {
            self.z3_decided += 1;
        }
        if r.ay_decided() {
            self.ay_decided += 1;
        }
        if r.agree() {
            self.ay_agree += 1;
        }
        if r.disagree() {
            self.disagree += 1;
        }
        if r.beyond_z3() {
            self.beyond += 1;
            if r.self_certified() {
                self.beyond_certified += 1;
            } else {
                self.beyond_unverified += 1;
            }
        }
        if r.declared.decided().is_some() {
            self.declared_decided += 1;
        }
        if r.declared_confirmed() {
            self.declared_confirmed += 1;
        }
        if r.declared_conflict() {
            self.declared_conflict += 1;
        }
        if r.loss() {
            self.losses += 1;
        }
        if r.verdict_shape_mismatch() {
            self.verdict_shape_mismatches += 1;
        }
        if r.self_certified() {
            self.self_cert += 1;
        }
        if r.self_conflict() {
            self.self_conflict += 1;
        }
        if let Some(ratio) = r.ratio {
            self.ratios.push(ratio);
            if let Some(z3) = &r.z3 {
                self.sum_ay_wall += r.ay.wall.as_secs_f64();
                self.sum_z3_wall += z3.wall.as_secs_f64();
                let slower = r.ay.wall.as_secs_f64().max(z3.wall.as_secs_f64());
                if slower >= WIN_LOSS_MIN_SECS {
                    // Same eligibility rule as the ladder: below the floor the
                    // ratio is timer granularity, so it must not reach a
                    // headline speed statistic.
                    self.ratios_timed.push(ratio);
                    if ratio < 0.5 {
                        self.ay_wins_2x += 1;
                    } else if ratio > 2.0 {
                        self.z3_wins_2x += 1;
                    }
                }
            }
        }

        // Rating-ladder accumulation over the decided-by-both set.
        if let Some(z3) = &r.z3 {
            if r.ay_decided() && z3.decided() {
                self.both_decided += 1;

                // --- WALL comparison (both walls always present) ---
                let ay_w = r.ay.wall.as_secs_f64();
                let z_w = z3.wall.as_secs_f64();
                if ay_w.max(z_w) >= WALL_FLOOR_SECS {
                    self.wall_cmp += 1;
                    if ay_w > z_w {
                        self.wall_losses += 1;
                    }
                    // Misses the 2x bar: ay_wall > 0.5*z3_wall (i.e. not >= 2x).
                    if ay_w > 0.5 * z_w {
                        self.wall_not_2x += 1;
                    }
                }

                // --- PEAK-RSS comparison ---
                match (r.ay.peak_rss, z3.peak_rss) {
                    (Some(ay_rss), Some(z_rss)) => {
                        let ay_r = ay_rss as f64;
                        let z_r = z_rss as f64;
                        if ay_r.max(z_r) >= RSS_FLOOR_BYTES {
                            self.rss_cmp += 1;
                            self.rss_ratios.push(ay_r / z_r.max(1.0));
                            // Misses the memory bar: ay_rss >= 0.8*z3_rss (not < 80%).
                            if ay_r >= 0.8 * z_r {
                                self.rss_not_80 += 1;
                            }
                        }
                    }
                    _ => {
                        // Without both peaks we cannot know that the pair is
                        // below the floor or that AY satisfies the <80% bar.
                        self.rss_missing += 1;
                    }
                }
            }
        }
    }

    fn merge(&mut self, o: &DivStats) {
        self.files += o.files;
        self.z3_decided += o.z3_decided;
        self.ay_decided += o.ay_decided;
        self.ay_agree += o.ay_agree;
        self.disagree += o.disagree;
        self.beyond += o.beyond;
        self.beyond_certified += o.beyond_certified;
        self.beyond_unverified += o.beyond_unverified;
        self.losses += o.losses;
        self.verdict_shape_mismatches += o.verdict_shape_mismatches;
        self.self_cert += o.self_cert;
        self.self_conflict += o.self_conflict;
        self.declared_decided += o.declared_decided;
        self.declared_confirmed += o.declared_confirmed;
        self.declared_conflict += o.declared_conflict;
        self.ratios.extend_from_slice(&o.ratios);
        self.ratios_timed.extend_from_slice(&o.ratios_timed);
        self.sum_ay_wall += o.sum_ay_wall;
        self.sum_z3_wall += o.sum_z3_wall;
        self.ay_wins_2x += o.ay_wins_2x;
        self.z3_wins_2x += o.z3_wins_2x;
        self.both_decided += o.both_decided;
        self.wall_cmp += o.wall_cmp;
        self.wall_losses += o.wall_losses;
        self.wall_not_2x += o.wall_not_2x;
        self.rss_cmp += o.rss_cmp;
        self.rss_not_80 += o.rss_not_80;
        self.rss_missing += o.rss_missing;
        self.rss_ratios.extend_from_slice(&o.rss_ratios);
    }

    /// solved% = ay-agree / z3-decided, `None` when z3 decided nothing (or z3
    /// is unavailable, in which case `z3_decided` is 0).
    fn solved_pct(&self) -> Option<f64> {
        (self.z3_decided > 0).then(|| 100.0 * self.ay_agree as f64 / self.z3_decided as f64)
    }

    /// self-cert% = self-certified / AY-decided, `None` when AY decided nothing.
    fn selfcert_pct(&self) -> Option<f64> {
        (self.ay_decided > 0).then(|| 100.0 * self.self_cert as f64 / self.ay_decided as f64)
    }

    fn geo_ratio(&self) -> Option<f64> {
        geomean(&self.ratios)
    }

    /// Geomean WALL ratio over the noise-floor-eligible subset only (slower
    /// side >= [`WALL_FLOOR_SECS`]). Prefer this over [`Self::geo_ratio`]: the
    /// unrestricted one floors each side at 0.1 ms and so reports timer
    /// granularity as a speed difference on trivially fast files.
    fn geo_ratio_timed(&self) -> Option<f64> {
        geomean(&self.ratios_timed)
    }

    /// Σay/Σz3 wall over decided-by-both files — the aggregate-cost ratio.
    /// `None` when z3 spent no measurable time.
    fn total_ratio(&self) -> Option<f64> {
        (self.sum_z3_wall > 0.0).then(|| self.sum_ay_wall / self.sum_z3_wall)
    }

    fn median_ratio(&self) -> Option<f64> {
        let mut s = self.ratios.clone();
        s.sort_by(|a, b| a.partial_cmp(b).expect("no NaN ratios"));
        median(&s)
    }

    /// Files in this division AY does NOT solve (no decisive sat/unsat) — the
    /// gap between SUPERIOR and PERFECT.
    fn unsolved(&self) -> usize {
        self.files - self.ay_decided
    }

    /// The HIGHEST rating tier this division reaches (see [`Rating`]).
    ///
    /// The three tiers are the owner's definitions, encoded exactly:
    ///
    /// * **PAR** — DISAGREE = 0 and DECLARED_CONFLICT = 0 (no wrong answers by
    ///   either oracle), AND AY returns a decisive verdict matching z3's on
    ///   every file z3 decides (0 undecided losses, 0 verdict-shape mismatches),
    ///   AND on every decided-by-both file above `WALL_FLOOR`
    ///   `ay_wall <= z3_wall` (0 wall losses).
    /// * **SUPERIOR** — all of PAR, AND on every decided-by-both file above
    ///   `WALL_FLOOR` `ay_wall <= 0.5*z3_wall` (>= 2x faster; 0 `wall_not_2x`),
    ///   AND complete peak-RSS evidence, with every decided-by-both file above
    ///   `RSS_FLOOR` satisfying `ay_rss < 0.8*z3_rss` (< 80% peak memory; 0
    ///   `rss_not_80` and 0 `rss_missing`).
    /// * **PERFECT** — all of SUPERIOR, AND AY solves EVERY file in the
    ///   division (decisive on 100% of the track, not merely what z3 decides).
    ///
    /// `n/a` (`Rating::NotApplicable`) when z3 is absent or decided nothing
    /// here — there is then nothing to rate AY against, EXCEPT that a nonzero
    /// `declared_conflict` is below par outright: that wrong answer was proved
    /// by the benchmark itself and needs no reference solver.
    fn rating(&self, z3_available: bool) -> Rating {
        // A wrong answer proved by the benchmark's own `:status` is never
        // "nothing to rate against": it needed no reference solver. Checked
        // BEFORE the n/a case so a division z3 could not decide at all cannot
        // hide a wrong answer behind `n/a`.
        if self.declared_conflict > 0 {
            return Rating::BelowPar;
        }
        if !z3_available || self.z3_decided == 0 {
            return Rating::NotApplicable;
        }
        let par = self.disagree == 0
            && self.declared_conflict == 0
            && self.losses == 0
            && self.verdict_shape_mismatches == 0
            && self.wall_losses == 0;
        if !par {
            return Rating::BelowPar;
        }
        let superior = self.wall_not_2x == 0 && self.rss_not_80 == 0 && self.rss_missing == 0;
        if !superior {
            return Rating::Par;
        }
        if self.unsolved() == 0 {
            Rating::Perfect
        } else {
            Rating::Superior
        }
    }

    /// The RATING table cell: the tier word plus its compact blocker counts.
    fn rating_cell(&self, z3_available: bool) -> String {
        match self.rating(z3_available) {
            Rating::NotApplicable => "n/a".to_string(),
            Rating::BelowPar => {
                // uN undecided losses, sM slower-than-z3, dK disagreements,
                // wL declared-status contradictions, mJ verdict-shape mismatches.
                let mut parts = Vec::new();
                if self.losses > 0 {
                    parts.push(format!("u{}", self.losses));
                }
                if self.wall_losses > 0 {
                    parts.push(format!("s{}", self.wall_losses));
                }
                if self.disagree > 0 {
                    parts.push(format!("d{}", self.disagree));
                }
                if self.declared_conflict > 0 {
                    parts.push(format!("w{}", self.declared_conflict));
                }
                if self.verdict_shape_mismatches > 0 {
                    parts.push(format!("m{}", self.verdict_shape_mismatches));
                }
                format!("below({})", parts.join(","))
            }
            // xN miss 2x speed, mN miss <80% memory, rN lack RSS evidence.
            Rating::Par => format!(
                "PAR(x{},m{},r{})",
                self.wall_not_2x, self.rss_not_80, self.rss_missing
            ),
            // uN track files AY does not solve.
            Rating::Superior => format!("SUPERIOR(u{})", self.unsolved()),
            Rating::Perfect => "PERFECT".to_string(),
        }
    }

    /// MEM column: geomean of `ay_rss / z3_rss` over decided-by-both files
    /// above `RSS_FLOOR` (< 1 = AY uses less peak memory). `None` when no file
    /// was memory-comparable.
    fn mem_geo(&self) -> Option<f64> {
        geomean(&self.rss_ratios)
    }
}

/// The rating ladder for a division (or the TOTAL row). Ordered so that a
/// higher tier compares greater. `NotApplicable` is z3-absent / z3-decided-0.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Rating {
    NotApplicable,
    BelowPar,
    Par,
    Superior,
    Perfect,
}

impl Rating {
    /// The bare tier word, as persisted in JSON and compared across baselines.
    fn word(self) -> &'static str {
        match self {
            Rating::NotApplicable => "n/a",
            Rating::BelowPar => "below",
            Rating::Par => "PAR",
            Rating::Superior => "SUPERIOR",
            Rating::Perfect => "PERFECT",
        }
    }
}

// ---------------------------------------------------------------------------
// ay CLI + z3 resolution
// ---------------------------------------------------------------------------

/// Resolve the `ay` CLI binary used for `--self-check`: the explicit
/// `--ay-cli`, else a sibling `ay` next to the FFI dylib, else
/// `target/release/ay`. `None` when none exists (self-cert then reported n/a).
fn resolve_ay_cli(cfg: &ScoreboardConfig) -> Option<PathBuf> {
    if let Some(p) = &cfg.ay_cli {
        return Some(p.clone());
    }
    if let Some(dir) = cfg.ay.parent() {
        let sibling = dir.join("ay");
        if sibling.exists() {
            return Some(sibling);
        }
    }
    let fallback = PathBuf::from("target/release/ay");
    fallback.exists().then_some(fallback)
}

#[derive(Debug)]
struct AyCliIdentity {
    path: PathBuf,
    sha256: Option<String>,
    version_output: Option<String>,
    build_stamp: Option<String>,
    build_commit: Option<String>,
    source_coherent: bool,
    issue: Option<String>,
}

fn build_field(output: &str, name: &str) -> Option<String> {
    output.lines().find_map(|line| {
        let (key, value) = line.trim().split_once('=')?;
        (key == name && !value.trim().is_empty()).then(|| value.trim().to_string())
    })
}

fn stamp_from_version_output(output: &str) -> Option<String> {
    build_field(output, "build.stamp").or_else(|| {
        output
            .lines()
            .map(str::trim)
            .find(|line| !line.is_empty())
            .and_then(|line| line.split_whitespace().last())
            .filter(|value| value.contains("+build.") && value.contains('@'))
            .map(str::to_string)
    })
}

/// Extract the source commit from AY's
/// `<version>+build.<increment>.<commit>@<utc>` build stamp.
fn commit_from_build_stamp(stamp: &str) -> Option<String> {
    let before_time = stamp.split_once('@')?.0;
    let commit = before_time.rsplit_once('.')?.1.trim();
    (!commit.is_empty() && commit != "unknown").then(|| commit.to_string())
}

fn source_coherence_error(
    ffi_build_stamp: Option<&str>,
    cli_build_stamp: Option<&str>,
) -> Option<String> {
    let ffi_commit = ffi_build_stamp.and_then(commit_from_build_stamp);
    let cli_commit = cli_build_stamp.and_then(commit_from_build_stamp);
    match (
        ffi_build_stamp,
        ffi_commit.as_deref(),
        cli_build_stamp,
        cli_commit.as_deref(),
    ) {
        (None, _, _, _) => Some("AY FFI library does not expose `ay_version`".to_string()),
        (_, None, _, _) => Some("AY FFI build stamp has no usable source commit".to_string()),
        (_, _, None, _) => Some("`ay --version` has no usable build stamp".to_string()),
        (_, _, _, None) => Some("`ay --version` has no usable source commit".to_string()),
        (Some(_), Some(ffi_source), Some(_), Some(cli_source)) if ffi_source != cli_source => Some(
            format!("source mismatch: AY FFI is {ffi_source}, ay CLI is {cli_source}"),
        ),
        (_, Some(source), _, _) if source.ends_with("-dirty") => {
            Some("dirty AY FFI/CLI builds cannot prove identical source content".to_string())
        }
        _ => None,
    }
}

fn probe_ay_cli(
    resources: &PlannedResources,
    path: PathBuf,
    ffi_build_stamp: Option<&str>,
) -> AyCliIdentity {
    const VERSION_TIMEOUT: Duration = Duration::from_secs(5);

    let sha256 = sha256_of(&path);
    let raw = spawn_timeboxed(
        resources,
        &path,
        &[OsString::from("--version")],
        VERSION_TIMEOUT,
        "ay-z3-parity version probe",
    );

    let probe_error = if let Some(error) = raw.harness_error {
        Some(error)
    } else if raw.output_truncated {
        Some("`ay --version` exceeded the fixed stdout capture limit".to_string())
    } else if raw.memout {
        Some("`ay --version` exceeded its RSS envelope".to_string())
    } else if raw.killed || raw.observed > VERSION_TIMEOUT {
        Some("`ay --version` timed out".to_string())
    } else {
        match raw.code {
            Some(0) => None,
            Some(code) => Some(format!("`ay --version` exited {code} ({})", raw.status_str)),
            None => Some(format!(
                "`ay --version` was killed by signal ({})",
                raw.status_str
            )),
        }
    };

    let version_output = probe_error
        .is_none()
        .then(|| String::from_utf8_lossy(&raw.stdout).trim().to_string())
        .filter(|output| !output.is_empty());
    let build_stamp = version_output
        .as_deref()
        .and_then(stamp_from_version_output);
    let build_commit = build_stamp.as_deref().and_then(commit_from_build_stamp);

    let coherence_error =
        probe_error.or_else(|| source_coherence_error(ffi_build_stamp, build_stamp.as_deref()));

    AyCliIdentity {
        path,
        sha256,
        version_output,
        build_stamp,
        build_commit,
        source_coherent: coherence_error.is_none(),
        issue: coherence_error,
    }
}

// ---------------------------------------------------------------------------
// Campaign driver
// ---------------------------------------------------------------------------

pub(crate) fn run(cfg: &ScoreboardConfig) -> i32 {
    let files = match collect(&cfg.root, cfg.divisions.as_deref()) {
        Ok(files) => files,
        Err(error) => {
            eprintln!("error: {error}");
            return 2;
        }
    };
    let available_total = files.len();
    let (files, sample_census) = match cfg.sample {
        Some(n) if n > 0 => {
            let (kept, census) = sample_per_division(files, n, cfg.seed);
            eprintln!(
                "scoreboard: SAMPLED {} of {} files — {} per division, seed {} \
                 (reproducible: same seed + corpus = same set)",
                kept.len(),
                available_total,
                n,
                cfg.seed
            );
            (kept, Some(census))
        }
        _ => (files, None),
    };
    if files.is_empty() {
        eprintln!(
            "error: no .smt2 files found under {}{}",
            cfg.root.display(),
            cfg.divisions
                .as_ref()
                .map(|d| format!(" (divisions filter: {})", d.join(",")))
                .unwrap_or_default()
        );
        return 2;
    }

    let exe = match std::env::current_exe() {
        Ok(p) => p,
        Err(e) => {
            eprintln!("error: cannot locate own executable for child mode: {e}");
            return 2;
        }
    };

    // Preflight AY (mandatory) and z3 (optional — AY must stand on its own).
    let (ay_version, ay_build_stamp) = match loader::open_local(&cfg.ay) {
        Ok(lib) => match loader::load_api(&lib) {
            Ok(_) => (loader::full_version(&lib), loader::ay_build_stamp(&lib)),
            Err(e) => {
                eprintln!("error (AY lib): {e}");
                return 2;
            }
        },
        Err(e) => {
            eprintln!("error (AY lib): {e}");
            return 2;
        }
    };

    let mut z3_available = false;
    let mut z3_version = None;
    match loader::open_local(&cfg.z3) {
        Ok(lib) => match loader::load_api(&lib) {
            Ok(_) => {
                z3_available = true;
                z3_version = loader::full_version(&lib);
            }
            Err(e) => eprintln!(
                "warning: z3 lib {} loaded but has no eval entry ({e}); \
                 running AY-only (self-cert still reported)",
                cfg.z3.display()
            ),
        },
        Err(e) => eprintln!(
            "warning: z3 lib {} unavailable ({e}); running AY-only \
             (self-cert still reported)",
            cfg.z3.display()
        ),
    }

    let timeout = Duration::from_secs(cfg.timeout_secs);
    let resources = match PlannedResources::plan(
        &ay_bench::runner::repo_root_public(),
        cfg.jobs,
        "ay-z3-parity scoreboard",
    ) {
        Ok(resources) => resources,
        Err(error) => {
            eprintln!("error: resource planning failed: {error}");
            return 2;
        }
    };
    let ay_cli_path = resolve_ay_cli(cfg);
    let ay_cli_identity =
        ay_cli_path.map(|path| probe_ay_cli(&resources, path, ay_build_stamp.as_deref()));
    let ay_cli = ay_cli_identity
        .as_ref()
        .filter(|identity| identity.source_coherent)
        .map(|identity| identity.path.clone());
    let resource_evidence = match resource_evidence(&resources.plan, timeout, ay_cli.is_some()) {
        Ok(evidence) => evidence,
        Err(error) => {
            eprintln!("error: resource envelope failed: {error}");
            return 2;
        }
    };
    match &ay_cli_identity {
        None => eprintln!(
            "warning: no `ay` CLI binary found (pass --ay-cli, or build \
             target/release/ay); no answers can be self-certified"
        ),
        Some(identity) if !identity.source_coherent => eprintln!(
            "warning: refusing `{}` for self-certification: {}; no answers \
             can be self-certified",
            identity.path.display(),
            identity.issue.as_deref().unwrap_or("unverified identity")
        ),
        Some(_) => {}
    }

    let total = files.len();
    eprintln!(
        "scoreboard: {total} files, timeout {}s, jobs requested/effective {}/{}, memory {}MiB/child, NBCORE {}, AY={} z3={} ay-cli={}",
        cfg.timeout_secs,
        cfg.jobs,
        resources.plan.jobs,
        resources.plan.memlimit_mb_per_child,
        resources.plan.nbcore_per_child,
        cfg.ay.display(),
        if z3_available {
            cfg.z3.display().to_string()
        } else {
            "(absent)".to_string()
        },
        ay_cli_identity
            .as_ref()
            .map(|identity| identity.path.display().to_string())
            .unwrap_or_else(|| "(none)".to_string()),
    );

    // Checkpoint journal. Always on: the certificate is written only at the very
    // end, so an unjournalled multi-day corpus run loses everything to a crash.
    let checkpoint_path = cfg.checkpoint.clone().unwrap_or_else(|| {
        let mut p = cfg.json_out.clone().into_os_string();
        p.push(".checkpoint.jsonl");
        PathBuf::from(p)
    });
    let header = checkpoint_header(
        cfg,
        sha256_of(&cfg.ay).as_deref().unwrap_or("(unhashed)"),
        &if z3_available {
            sha256_of(&cfg.z3).unwrap_or_else(|| "(unhashed)".to_string())
        } else {
            "(absent)".to_string()
        },
    );
    let resumed: ResumeMap = if cfg.resume {
        match load_checkpoint(&checkpoint_path, &header) {
            Ok(map) => {
                eprintln!(
                    "scoreboard: resuming — {} file(s) reused from {}",
                    map.len(),
                    checkpoint_path.display()
                );
                map
            }
            Err(error) => {
                eprintln!("error: --resume refused: {error}");
                return 2;
            }
        }
    } else {
        ResumeMap::new()
    };
    let fresh_journal = resumed.is_empty();
    let journal = match std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .truncate(false)
        .open(&checkpoint_path)
    {
        Ok(mut f) => {
            if fresh_journal {
                // Overwrite any unusable prior journal with a header for THIS run.
                if let Err(error) = std::fs::write(&checkpoint_path, format!("{header}\n")) {
                    eprintln!(
                        "error: cannot write checkpoint {}: {error}",
                        checkpoint_path.display()
                    );
                    return 2;
                }
                f = match std::fs::OpenOptions::new()
                    .append(true)
                    .open(&checkpoint_path)
                {
                    Ok(f) => f,
                    Err(error) => {
                        eprintln!("error: cannot reopen checkpoint: {error}");
                        return 2;
                    }
                };
            }
            Mutex::new(f)
        }
        Err(error) => {
            eprintln!(
                "error: cannot open checkpoint {}: {error}",
                checkpoint_path.display()
            );
            return 2;
        }
    };
    eprintln!(
        "scoreboard: checkpoint {} ({} per completed file; rerun with --resume after a crash)",
        checkpoint_path.display(),
        if fresh_journal { "fresh" } else { "appending" }
    );

    let next = AtomicUsize::new(0);
    let done = AtomicUsize::new(0);
    let reused = AtomicUsize::new(0);
    let slots: Mutex<Vec<Option<FileRecord>>> = Mutex::new((0..total).map(|_| None).collect());
    let campaign_t0 = Instant::now();

    // Progress file: rewritten atomically (tmp + rename) so a reader always sees
    // a complete document, never a half-written one.
    let progress_path = cfg.progress.clone();
    let write_progress = |done_n: usize, reused_n: usize, elapsed: Duration, final_: bool| {
        let Some(path) = progress_path.as_ref() else {
            return;
        };
        let fresh = done_n.saturating_sub(reused_n);
        let per_min = if elapsed.as_secs_f64() > 0.0 {
            fresh as f64 / (elapsed.as_secs_f64() / 60.0)
        } else {
            0.0
        };
        let remaining = total.saturating_sub(done_n);
        let eta_hours = if per_min > 0.0 {
            remaining as f64 / per_min / 60.0
        } else {
            f64::NAN
        };
        let doc = serde_json::json!({
            "generated_utc": utc_now_iso(),
            "state": if final_ { "finished" } else { "running" },
            "pid": std::process::id(),
            "done": done_n,
            "total": total,
            "reused_from_checkpoint": reused_n,
            "percent": (done_n as f64 * 100.0 / total.max(1) as f64 * 100.0).round() / 100.0,
            "files_per_min": (per_min * 100.0).round() / 100.0,
            "eta_hours": if eta_hours.is_finite() {
                serde_json::json!((eta_hours * 100.0).round() / 100.0)
            } else {
                serde_json::Value::Null
            },
            "elapsed_secs": elapsed.as_secs(),
            "corpus_root": cfg.root.display().to_string(),
            "sample_per_division": cfg.sample,
            "seed": cfg.seed,
            "timeout_secs": cfg.timeout_secs,
            "jobs": resources.plan.jobs,
            "checkpoint": checkpoint_path.display().to_string(),
        });
        let tmp = path.with_extension("tmp");
        if std::fs::write(&tmp, format!("{doc}\n")).is_ok() {
            let _ = std::fs::rename(&tmp, path);
        }
    };
    if let Some(p) = progress_path.as_ref() {
        eprintln!("scoreboard: progress {}", p.display());
    }

    std::thread::scope(|scope| {
        // Ticker: keeps the status file fresh even while every worker is parked
        // on a 20s solver timeout, so "is it alive?" is answerable at a glance.
        // Self-terminating: `thread::scope` joins at the END of this closure, so
        // a flag set here would fire before the workers ever run. The ticker
        // instead exits once every file is accounted for.
        scope.spawn(|| {
            while done.load(Ordering::Relaxed) < total {
                write_progress(
                    done.load(Ordering::Relaxed),
                    reused.load(Ordering::Relaxed),
                    campaign_t0.elapsed(),
                    false,
                );
                for _ in 0..50 {
                    if done.load(Ordering::Relaxed) >= total {
                        break;
                    }
                    std::thread::sleep(Duration::from_millis(100));
                }
            }
        });
        for _ in 0..resources.plan.jobs {
            scope.spawn(|| loop {
                let i = next.fetch_add(1, Ordering::Relaxed);
                if i >= total {
                    break;
                }
                let (division, file) = &files[i];
                // Reused files are NOT re-journalled: the line is already there,
                // and appending it twice would inflate a later resume.
                let from_journal = resumed.get(file).cloned();
                let replayed = from_journal.is_some();
                let (ay, z3, selfcheck) = match from_journal {
                    Some((ay, z3, selfcheck)) => (ay, z3, selfcheck),
                    None => {
                        let z3 = z3_available.then(|| {
                            run_one(
                                &resources,
                                &exe,
                                &cfg.z3,
                                file,
                                timeout,
                                "ay-z3-parity scoreboard z3",
                            )
                        });
                        let ay = run_one(
                            &resources,
                            &exe,
                            &cfg.ay,
                            file,
                            timeout,
                            "ay-z3-parity scoreboard AY",
                        );
                        let selfcheck = match &ay_cli {
                            Some(cli) => run_selfcheck(&resources, cli, file, timeout),
                            None => SelfCheck::Error("no ay CLI".to_string()),
                        };
                        // Journal BEFORE the record is published, so anything the
                        // certificate can report is already durable.
                        let line = serde_json::json!({
                            "file": file.display().to_string(),
                            "division": division,
                            "ay": outcome_to_json(&ay),
                            "z3": z3.as_ref().map(outcome_to_json),
                            "self": selfcheck_to_json(&selfcheck),
                        });
                        {
                            let mut f = journal.lock().expect("journal poisoned");
                            if let Err(error) = writeln!(f, "{line}").and_then(|()| f.flush()) {
                                eprintln!("warning: checkpoint write failed: {error}");
                            }
                        }
                        (ay, z3, selfcheck)
                    }
                };
                let category = z3.as_ref().map(|z| categorize(&ay, z));
                let ratio = matches!(
                    category,
                    Some(Category::AgreeSat | Category::AgreeUnsat | Category::AgreeMixed)
                )
                .then(|| ratio_of(&ay, z3.as_ref().expect("agree implies z3 present")));
                // Derived from the file on disk, never journalled — so a resumed
                // run re-reads the annotation and can never carry a stale one.
                let declared = bench::declared_status_of_file(file);
                let record = FileRecord {
                    division: division.clone(),
                    file: file.clone(),
                    ay,
                    z3,
                    selfcheck,
                    declared,
                    category,
                    ratio,
                };
                if replayed {
                    reused.fetch_add(1, Ordering::Relaxed);
                }
                let n_done = done.fetch_add(1, Ordering::Relaxed) + 1;
                eprintln!(
                    "[{n_done}/{total}]{} {division} {}: z3={} ay={} self={} decl={} {}{}",
                    if replayed { " (resumed)" } else { "" },
                    file.file_name().and_then(|n| n.to_str()).unwrap_or("?"),
                    record
                        .z3
                        .as_ref()
                        .map(BenchOutcome::label)
                        .unwrap_or_else(|| "-".into()),
                    record.ay.label(),
                    record.selfcheck.label(),
                    declared.as_str(),
                    record.category.map(Category::label).unwrap_or(""),
                    // A wrong answer must be visible the moment it happens, not
                    // only in the summary 40 hours later.
                    if record.declared_conflict() {
                        " !! DECLARED-CONFLICT"
                    } else {
                        ""
                    },
                );
                slots.lock().expect("slots poisoned")[i] = Some(record);
            });
        }
    });
    write_progress(
        done.load(Ordering::Relaxed),
        reused.load(Ordering::Relaxed),
        campaign_t0.elapsed(),
        true,
    );

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

    // Baseline for the DELTA column (best-effort; a bad baseline is a warning).
    let baseline = cfg.baseline.as_ref().and_then(|p| load_baseline(p));

    // ---- stdout table ----
    println!("== ay-z3-parity scoreboard: AY vs z3 + AY self-certification ==");
    println!(
        "  under test (AY):  {}  [{}]",
        cfg.ay.display(),
        ay_version.as_deref().unwrap_or("?")
    );
    if z3_available {
        println!(
            "  reference (z3):   {}  [{}]",
            cfg.z3.display(),
            z3_version.as_deref().unwrap_or("?")
        );
    } else {
        println!("  reference (z3):   (absent) — z3-agreement columns are n/a");
    }
    println!(
        "  self-check (ay):  {}",
        match &ay_cli_identity {
            Some(identity) if identity.source_coherent => format!(
                "{}  [source {}]",
                identity.path.display(),
                identity.build_commit.as_deref().unwrap_or("?")
            ),
            Some(identity) => format!(
                "{} — REJECTED ({})",
                identity.path.display(),
                identity.issue.as_deref().unwrap_or("unverified identity")
            ),
            None => "(none) — 0 self-certified".to_string(),
        }
    );
    println!(
        "  corpus root:      {}  ({} files, timeout {}s, jobs requested/effective {}/{}, memory {}MiB/child, NBCORE {}, wall {:.1}s)",
        cfg.root.display(),
        total,
        cfg.timeout_secs,
        cfg.jobs,
        resources.plan.jobs,
        resources.plan.memlimit_mb_per_child,
        resources.plan.nbcore_per_child,
        campaign_wall.as_secs_f64()
    );
    if let Some(b) = &baseline {
        println!("  baseline:         {}  (DELTA column vs this)", b.path);
    }
    println!();
    print!(
        "{}",
        render_table(&divisions, &totals, z3_available, baseline.as_ref())
    );
    println!();

    // ---- JSON certificate ----
    let cert = build_certificate(
        cfg,
        &records,
        &divisions,
        &totals,
        ay_version.as_deref(),
        ay_build_stamp.as_deref(),
        z3_version.as_deref(),
        z3_available,
        ay_cli_identity.as_ref(),
        campaign_wall,
        &resources.plan,
        &resource_evidence,
        available_total,
        sample_census.as_ref(),
    );
    let cert_text = serde_json::to_string_pretty(&cert).unwrap_or_default();
    if let Some(dir) = cfg.json_out.parent() {
        let _ = std::fs::create_dir_all(dir);
    }
    if let Err(e) = std::fs::write(&cfg.json_out, &cert_text) {
        eprintln!("error: writing {}: {e}", cfg.json_out.display());
        return 2;
    }
    println!("certificate: {}", cfg.json_out.display());
    println!();

    // ---- soundness verdict + exit code ----
    let disagrees: Vec<&FileRecord> = records.iter().filter(|r| r.disagree()).collect();
    let declared_conflicts: Vec<&FileRecord> =
        records.iter().filter(|r| r.declared_conflict()).collect();
    let conflicts: Vec<&FileRecord> = records.iter().filter(|r| r.self_conflict()).collect();
    // A file can trip more than one detector; count FILES, so the headline is a
    // count of wrong answers and not of alarms.
    let unsound = records
        .iter()
        .filter(|r| r.disagree() || r.declared_conflict() || r.self_conflict())
        .count();
    if unsound == 0 {
        println!(
            "RESULT: PASS — 0 sat-vs-unsat disagreements (AY vs z3), 0 \
             contradictions of a declared :status, and 0 self-check \
             contradictions across {} files.",
            totals.files
        );
    } else {
        println!("{}", "!".repeat(72));
        println!(
            "WARNING: {unsound} WRONG ANSWER(S) — {} AY-vs-z3 DISAGREE, {} \
             DECLARED-CONFLICT, {} self-check contradiction(s). THIS RUN FAILS.",
            disagrees.len(),
            declared_conflicts.len(),
            conflicts.len()
        );
        println!("{}", "!".repeat(72));
        for r in &disagrees {
            println!(
                "  DISAGREE  {}  declared={} z3={} ay={}",
                r.file.display(),
                r.declared.as_str(),
                r.z3.as_ref().map(BenchOutcome::label).unwrap_or_default(),
                r.ay.label()
            );
        }
        // z3's verdict is printed here precisely because it is usually absent:
        // these are the wrong answers the z3 comparison cannot see.
        for r in &declared_conflicts {
            println!(
                "  DECLARED-CONFLICT  {}  declared={} ay={} z3={} z3-decided={}",
                r.file.display(),
                r.declared.as_str(),
                r.ay.label(),
                r.z3.as_ref()
                    .map(BenchOutcome::label)
                    .unwrap_or_else(|| "(absent)".into()),
                r.z3_decided()
            );
        }
        for r in &conflicts {
            println!(
                "  SELF-CONFLICT  {}  ay-eval={} ay-self-check={}",
                r.file.display(),
                r.ay.label(),
                r.selfcheck.label()
            );
        }
    }

    i32::from(unsound != 0)
}

// ---------------------------------------------------------------------------
// Baseline / DELTA
// ---------------------------------------------------------------------------

struct BaselineDiv {
    solved_pct: Option<f64>,
    selfcert_pct: Option<f64>,
    /// The rating tier word (`PAR` / `SUPERIOR` / `PERFECT` / `below` / `n/a`)
    /// from a prior scoreboard JSON. `None` for a pre-rating baseline.
    rating: Option<String>,
}

struct Baseline {
    path: String,
    divisions: BTreeMap<String, BaselineDiv>,
}

/// Load a prior certificate for the DELTA column. Version-tolerant by
/// construction: every field is looked up by name, so a `format_version` 2
/// baseline (written before the declared-`:status` fields existed) still yields
/// a DELTA for solved% / selfcert% / rating, and a field it lacks degrades to
/// `new` / `-` instead of failing the run.
fn load_baseline(path: &Path) -> Option<Baseline> {
    let text = match std::fs::read_to_string(path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!(
                "warning: baseline {} unreadable ({e}); no DELTA",
                path.display()
            );
            return None;
        }
    };
    let json: serde_json::Value = match serde_json::from_str(&text) {
        Ok(v) => v,
        Err(e) => {
            eprintln!(
                "warning: baseline {} is not JSON ({e}); no DELTA",
                path.display()
            );
            return None;
        }
    };
    let mut divisions = BTreeMap::new();
    let rows = json
        .get("divisions")
        .and_then(|d| d.as_array())
        .into_iter()
        .flatten()
        .chain(json.get("totals"));
    for row in rows {
        let Some(name) = row.get("name").and_then(|n| n.as_str()) else {
            continue;
        };
        divisions.insert(
            name.to_string(),
            BaselineDiv {
                solved_pct: row.get("solved_pct").and_then(serde_json::Value::as_f64),
                selfcert_pct: row.get("selfcert_pct").and_then(serde_json::Value::as_f64),
                rating: row
                    .get("rating")
                    .and_then(serde_json::Value::as_str)
                    .map(str::to_string),
            },
        );
    }
    Some(Baseline {
        path: path.display().to_string(),
        divisions,
    })
}

/// Render the DELTA cell for one division vs the baseline.
fn delta_cell(name: &str, s: &DivStats, z3_available: bool, base: &Baseline) -> String {
    let Some(b) = base.divisions.get(name) else {
        return "(new)".to_string();
    };
    let dp = |now: Option<f64>, was: Option<f64>| -> String {
        match (now, was) {
            (Some(n), Some(w)) => format!("{:+.1}", n - w),
            (Some(_), None) => "new".to_string(),
            (None, Some(_)) => "gone".to_string(),
            (None, None) => "-".to_string(),
        }
    };
    let rating_now = s.rating(z3_available).word();
    let rating_delta = match b.rating.as_deref() {
        Some(was) if was == rating_now => "=".to_string(),
        Some(was) => format!("{was}->{rating_now}"),
        None => "new".to_string(),
    };
    format!(
        "s{} c{} {}",
        dp(s.solved_pct(), b.solved_pct),
        dp(s.selfcert_pct(), b.selfcert_pct),
        rating_delta
    )
}

// ---------------------------------------------------------------------------
// Table rendering
// ---------------------------------------------------------------------------

fn pct_cell(pct: Option<f64>, num: usize, den: usize) -> String {
    match pct {
        Some(p) => format!("{p:.1}% ({num}/{den})"),
        None => "n/a".to_string(),
    }
}

fn stats_row(
    name: &str,
    s: &DivStats,
    z3_available: bool,
    baseline: Option<&Baseline>,
) -> Vec<String> {
    let mut row = vec![
        name.to_string(),
        s.files.to_string(),
        if z3_available {
            pct_cell(s.solved_pct(), s.ay_agree, s.z3_decided)
        } else {
            "n/a".to_string()
        },
        pct_cell(s.selfcert_pct(), s.self_cert, s.ay_decided),
        if z3_available {
            // Certified/unverified inline: an unverified claim must never be
            // readable as demonstrated capability.
            format!(
                "{} ({}c/{}u)",
                s.beyond, s.beyond_certified, s.beyond_unverified
            )
        } else {
            "n/a".to_string()
        },
        if z3_available {
            bench::fmt_ratio(s.geo_ratio())
        } else {
            "n/a".to_string()
        },
        if z3_available {
            bench::fmt_ratio(s.mem_geo())
        } else {
            "n/a".to_string()
        },
        s.rating_cell(z3_available),
        s.disagree.to_string(),
        s.declared_conflict.to_string(),
    ];
    if let Some(b) = baseline {
        row.push(delta_cell(name, s, z3_available, b));
    }
    row
}

fn render_table(
    divisions: &BTreeMap<String, DivStats>,
    totals: &DivStats,
    z3_available: bool,
    baseline: Option<&Baseline>,
) -> String {
    let mut headers = vec![
        "DIVISION",
        "FILES",
        "SOLVED%",
        "SELFCERT%",
        "BEYOND",
        "GEO ay/z3",
        "MEM ay/z3",
        "RATING",
        "DISAGREE",
        "DECL-CONF",
    ];
    if baseline.is_some() {
        headers.push("DELTA s/c/rating");
    }
    let mut rows: Vec<Vec<String>> = vec![headers.iter().map(|h| h.to_string()).collect()];
    for (name, s) in divisions {
        rows.push(stats_row(name, s, z3_available, baseline));
    }
    rows.push(stats_row("TOTAL", totals, z3_available, baseline));

    let cols = headers.len();
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
        if ri == 0 || ri + 2 == rows.len() {
            out.push_str(&"-".repeat(widths.iter().sum::<usize>() + 2 * (cols - 1)));
            out.push('\n');
        }
    }
    out.push_str(
        "\nSOLVED% = ay-agree / z3-decided | SELFCERT% = ay-self-certified / ay-decided\n\
         BEYOND = files AY decides but z3 does not, as total (Nc self-certified / Nu unverified);\n\
         \x20 a wrong answer is never credited, so a DECL-CONF file is excluded\n\
         DISAGREE = positional sat-vs-unsat, AY vs z3 (needs z3 to have decided the file)\n\
         DECL-CONF = AY's decided answer contradicts the file's own (set-info :status sat|unsat),\n\
         \x20 counted even when z3 did not decide it — the wrong answers DISAGREE cannot see\n\
         GEO ay/z3 = geomean WALL ratio over decided-by-both (<1 = AY faster)\n\
         MEM ay/z3 = geomean PEAK-RSS ratio over decided-by-both above 5MB (<1 = AY leaner)\n\
         RATING (per division; floors: WALL 10ms, RSS 5MB):\n\
         \x20 PAR      = DISAGREE 0 and DECL-CONF 0, AY decides every z3 decision, ay_wall <= z3_wall on every decided-by-both file > 10ms\n\
         \x20 SUPERIOR = PAR + ay_wall <= 0.5*z3_wall (>=2x) on every such file + complete RSS evidence + ay_rss < 0.8*z3_rss on every decided-by-both file > 5MB; missing RSS blocks\n\
         \x20 PERFECT  = SUPERIOR + AY decides 100% of the track's files\n\
         \x20 below(uN,sM,dK,wL,mJ) = N undecided losses, M slower-than-z3, K disagreements, L declared-status contradictions, J verdict-shape mismatches\n\
         \x20 PAR(xN,mM,rK) = N miss 2x speed, M miss <80% memory, K lack RSS evidence | SUPERIOR(uN) = N track files AY doesn't solve\n",
    );
    if baseline.is_some() {
        out.push_str(
            "DELTA = change vs baseline: s<solved pp> c<selfcert pp> <rating change, e.g. PAR->SUPERIOR>.\n",
        );
    }
    out
}

// ---------------------------------------------------------------------------
// JSON certificate
// ---------------------------------------------------------------------------

#[allow(clippy::too_many_arguments)]
fn build_certificate(
    cfg: &ScoreboardConfig,
    records: &[FileRecord],
    divisions: &BTreeMap<String, DivStats>,
    totals: &DivStats,
    ay_version: Option<&str>,
    ay_build_stamp: Option<&str>,
    z3_version: Option<&str>,
    z3_available: bool,
    ay_cli: Option<&AyCliIdentity>,
    campaign_wall: Duration,
    resource_plan: &ResourcePlan,
    resource_evidence: &serde_json::Value,
    available_total: usize,
    sample_census: Option<&BTreeMap<String, (usize, usize)>>,
) -> serde_json::Value {
    let div_json = |name: &str, s: &DivStats| {
        serde_json::json!({
            "name": name,
            "files": s.files,
            "z3_decided": s.z3_decided,
            "ay_decided": s.ay_decided,
            "ay_agree": s.ay_agree,
            "disagree": s.disagree,
            "beyond_z3": s.beyond,
            // The beyond-z3 credit, split so an unverified claim cannot be read
            // as demonstrated capability. certified + unverified == beyond_z3.
            "beyond_z3_self_certified": s.beyond_certified,
            "beyond_z3_unverified": s.beyond_unverified,
            // The z3-independent oracle: the benchmarks' own :status.
            "declared_decided": s.declared_decided,
            "declared_confirmed": s.declared_confirmed,
            "declared_conflict": s.declared_conflict,
            "self_certified": s.self_cert,
            "self_conflict": s.self_conflict,
            "solved_pct": s.solved_pct(),
            "selfcert_pct": s.selfcert_pct(),
            "decided_by_both": s.both_decided,
            "wall_ratio_sample_count": s.ratios.len(),
            "geomean_wall_ratio_ay_over_z3": s.geo_ratio(),
            "median_wall_ratio_ay_over_z3": s.median_ratio(),
            // The honest speed headline: same eligibility rule as the ladder
            // (slower side >= wall_floor_secs), so timer granularity on
            // trivially fast files cannot reach it. Read this one.
            "wall_ratio_timed_sample_count": s.ratios_timed.len(),
            "geomean_wall_ratio_timed_ay_over_z3": s.geo_ratio_timed(),
            // Aggregate cost: Σay/Σz3 over decided-by-both. Undistorted by a
            // long tail of trivial files.
            "total_wall_ratio_ay_over_z3": s.total_ratio(),
            "sum_ay_wall_secs": s.sum_ay_wall,
            "sum_z3_wall_secs": s.sum_z3_wall,
            "ay_wins_2x": s.ay_wins_2x,
            "z3_wins_2x": s.z3_wins_2x,
            // --- rating ladder (PAR / SUPERIOR / PERFECT / below / n/a) ---
            "rating": s.rating(z3_available).word(),
            "mem_geomean_ay_over_z3": s.mem_geo(),
            "rating_ladder": {
                "decided_by_both": s.both_decided,
                "wall_compared": s.wall_cmp,
                "rss_compared": s.rss_cmp,
                "rss_missing": s.rss_missing,
                // PAR blockers
                "undecided_losses": s.losses,
                "verdict_shape_mismatches": s.verdict_shape_mismatches,
                "wall_slower_than_z3": s.wall_losses,
                "disagree": s.disagree,
                "declared_conflict": s.declared_conflict,
                // SUPERIOR blockers
                "wall_below_2x": s.wall_not_2x,
                "rss_at_or_above_80pct": s.rss_not_80,
                // PERFECT blocker
                "unsolved_files": s.unsolved(),
            },
        })
    };
    let files_json: Vec<_> = records
        .iter()
        .map(|r| {
            serde_json::json!({
                "file": r.file.display().to_string(),
                "division": r.division,
                "ay": { "outcome": r.ay.label(), "wall_ms": r.ay.wall.as_secs_f64() * 1000.0, "peak_rss_bytes": r.ay.peak_rss, "detail": r.ay.detail(), "decided": r.ay_decided() },
                "z3": r.z3.as_ref().map(|z| serde_json::json!({ "outcome": z.label(), "wall_ms": z.wall.as_secs_f64() * 1000.0, "peak_rss_bytes": z.peak_rss, "detail": z.detail(), "decided": z.decided() })),
                "self_check": r.selfcheck.label(),
                "self_check_detail": r.selfcheck.detail(),
                "self_certified": r.self_certified(),
                "category": r.category.map(Category::label),
                // The file's own (set-info :status ...): "sat" | "unsat" |
                // "unknown" | "absent". `absent` (no annotation) is deliberately
                // distinct from a declared `unknown`.
                "declared": r.declared.as_str(),
                "declared_conflict": r.declared_conflict(),
                "declared_confirmed": r.declared_confirmed(),
                "beyond_z3": r.beyond_z3(),
                "loss": r.loss(),
                "verdict_shape_mismatch": r.verdict_shape_mismatch(),
                "wall_slower_than_z3": r.wall_slower_than_z3(),
                "wall_ratio_ay_over_z3": r.ratio,
                "rss_ratio_ay_over_z3": rss_ratio(&r.ay, r.z3.as_ref()),
            })
        })
        .collect();
    let disagree_files: Vec<_> = records
        .iter()
        .filter(|r| r.disagree())
        .map(|r| {
            serde_json::json!({
                "file": r.file.display().to_string(),
                // Kept `null` for an unannotated file, as in format 2; the
                // four-state token lives in the per-file `declared` field.
                "declared_status": bench::declared_status(&r.file),
                "declared": r.declared.as_str(),
                "z3": r.z3.as_ref().map(BenchOutcome::label),
                "ay": r.ay.label(),
            })
        })
        .collect();
    // The wrong answers the z3 comparison structurally cannot see: `z3_decided`
    // is false for most of these, which is exactly why they need their own list.
    let declared_conflict_files: Vec<_> = records
        .iter()
        .filter(|r| r.declared_conflict())
        .map(|r| {
            serde_json::json!({
                "file": r.file.display().to_string(),
                "division": r.division,
                "declared": r.declared.as_str(),
                "ay": r.ay.label(),
                "z3": r.z3.as_ref().map(BenchOutcome::label),
                "z3_decided": r.z3_decided(),
                "self_check": r.selfcheck.label(),
                "self_certified": r.self_certified(),
            })
        })
        .collect();
    let self_conflict_files: Vec<_> = records
        .iter()
        .filter(|r| r.self_conflict())
        .map(|r| {
            serde_json::json!({
                "file": r.file.display().to_string(),
                "ay_eval": r.ay.label(),
                "ay_self_check": r.selfcheck.label(),
            })
        })
        .collect();
    // Which verdict oracles sat this run out. Each conflict counter is
    // vacuously 0 when its oracle did not run, so this list is what keeps
    // `pass` from being computed off silence. See the `pass` key below.
    let mut gates_not_run: Vec<&str> = Vec::new();
    if !z3_available {
        gates_not_run.push("z3_agreement");
    }
    if totals.self_cert == 0 {
        gates_not_run.push("self_certification");
    }
    if totals.declared_decided == 0 {
        gates_not_run.push("declared_status");
    }
    serde_json::json!({
        "kind": "ay-z3-scoreboard",
        "format_version": FORMAT_VERSION,
        "generated_utc": utc_now_iso(),
        "invocation": std::env::args().collect::<Vec<_>>().join(" "),
        "host": host_info(),
        "ay_lib": {
            "path": cfg.ay.display().to_string(),
            "sha256": sha256_of(&cfg.ay),
            "full_version": ay_version,
            "build_stamp": ay_build_stamp,
        },
        "ay_cli": ay_cli
            .filter(|identity| identity.source_coherent)
            .map(|identity| identity.path.display().to_string()),
        "self_certification_available": ay_cli.is_some_and(|identity| identity.source_coherent),
        "ay_cli_identity": ay_cli.map(|identity| serde_json::json!({
            "path": identity.path.display().to_string(),
            "sha256": identity.sha256.as_deref(),
            "version_output": identity.version_output.as_deref(),
            "build_stamp": identity.build_stamp.as_deref(),
            "build_commit": identity.build_commit.as_deref(),
            "source_coherent_with_ay_lib": identity.source_coherent,
            "rejection_reason": identity.issue.as_deref(),
        })),
        "z3_lib": { "path": cfg.z3.display().to_string(), "available": z3_available, "sha256": sha256_of(&cfg.z3), "full_version": z3_version },
        "z3_available": z3_available,
        "corpus_root": cfg.root.display().to_string(),
        "divisions_filter": cfg.divisions,
        // A score is meaningless without what it was measured on (standing rule
        // 12). `mode` is "all" or "seeded-per-division"; the census records, per
        // track, how many files were selected out of how many exist, so a
        // sampled number can never be read as a full-corpus one.
        "sampling": {
            "mode": if cfg.sample.is_some() { "seeded-per-division" } else { "all" },
            "per_division": cfg.sample,
            "seed": cfg.seed,
            "selected_files": records.len(),
            "available_files": available_total,
            "census": sample_census.map(|c| c.iter()
                .map(|(d, (sel, avail))| (d.clone(), serde_json::json!({"selected": sel, "available": avail})))
                .collect::<serde_json::Map<_, _>>()),
        },
        "timeout_secs": cfg.timeout_secs,
        "jobs": resource_plan.jobs,
        "requested_jobs": resource_plan.requested_jobs,
        "resource": resource_evidence,
        "campaign_wall_secs": campaign_wall.as_secs_f64(),
        "baseline": cfg.baseline.as_ref().map(|p| p.display().to_string()),
        "methodology": {
            "z3_agreement": "solved% = ay-agree / z3-decided; DISAGREE = positional sat-vs-unsat (AY vs z3), must be 0. This metric is BLIND wherever z3 did not decide the file — see declared_status, which covers exactly that gap",
            "declared_status": "each input's own (set-info :status sat|unsat|unknown) is parsed (skipping ; comments, |quoted symbols| and \"strings\", so the prose in a :source blob is never mistaken for the annotation) and reported per file as declared = sat|unsat|absent|unknown, where absent (no annotation) is distinct from a declared unknown. DECLARED_CONFLICT = declared is sat|unsat AND AY decided AND AY's verdict contradicts it: a wrong answer proved without z3, counted even when z3 timed out or crashed on the file. Must be 0; it gates the run exactly as DISAGREE does",
            "beyond_z3": "files AY decides that z3 does not, split into beyond_z3_self_certified and beyond_z3_unverified so an unverified claim cannot be read as demonstrated capability. A file whose answer is already known wrong (DISAGREE or DECLARED_CONFLICT) is never credited as beyond_z3",
            "self_certification": "selfcert% = files AY self-certifies (a source-coherent ay solve --self-check exits cleanly within the deadline and emits the same decisive verdict AY's eval gives) / files AY decides; the z3-independent metric",
            "rating_ladder": "per division, highest tier reached. decided-by-both = files AY and z3 both decide. PAR = DISAGREE 0 AND DECLARED_CONFLICT 0 AND AY returns a decisive verdict matching z3 on every file z3 decides (0 undecided losses + 0 verdict-shape mismatches) AND ay_wall <= z3_wall on every decided-by-both file above the WALL floor. SUPERIOR = PAR AND ay_wall <= 0.5*z3_wall on every such file (>=2x) AND complete peak-RSS evidence with ay_rss < 0.8*z3_rss on every decided-by-both file above the RSS floor (<80% peak). Missing RSS caps the rating at PAR. PERFECT = SUPERIOR AND AY decides 100% of the track's files. n/a when z3 is absent or decided nothing.",
            "peak_rss": "each successful bench-one child self-reports getrusage(RUSAGE_SELF).ru_maxrss in BYTES after solver teardown; Darwin reports bytes, Linux kilobytes (normalized to bytes with cfg(target_os)); missing evidence fails closed for SUPERIOR/PERFECT",
            "isolation": "each (file, solver) pair and each self-check runs in a stopped-exec process group with a pre-exec zero-grace RSS watchdog, bounded stdout, and residual-descendant teardown before leader reap",
            "speed_statistics": "THREE wall statistics are published and they do NOT share a noise floor. geomean_wall_ratio_ay_over_z3 is taken over EVERY decided-by-both file with each side floored at ratio_floor_secs (0.1 ms), so on a division of trivially fast files it reports timer granularity as a speed difference — it is retained only for continuity with previously published scoreboards. geomean_wall_ratio_timed_ay_over_z3 applies the SAME eligibility rule as the rating ladder and the 2x win/loss counters (slower side >= wall_floor_secs) and is the statistic to read; its denominator is wall_ratio_timed_sample_count, which may be far smaller than wall_ratio_sample_count. total_wall_ratio_ay_over_z3 is Σay/Σz3 over decided-by-both and answers the aggregate-cost question a replacement claim actually rests on.",
            "ratio_floor_secs": bench::RATIO_FLOOR_SECS,
            "win_loss_min_secs": WIN_LOSS_MIN_SECS,
            "wall_floor_secs": WALL_FLOOR_SECS,
            "rss_floor_bytes": RSS_FLOOR_BYTES,
        },
        "divisions": divisions.iter().map(|(n, s)| div_json(n, s)).collect::<Vec<_>>(),
        "totals": div_json("TOTAL", totals),
        "files": files_json,
        "disagree_files": disagree_files,
        "declared_conflict_files": declared_conflict_files,
        "self_conflict_files": self_conflict_files,
        // WHICH ORACLES ACTUALLY RAN. Each conflict counter is vacuously 0 when
        // its oracle did not run, so `pass` computed from the counters alone
        // reports success for a run that checked nothing. Measured on
        // 2026-08-03: the z3 dylib defaulted to a python site-packages path that
        // does not exist on this host, and the ay CLI failed the harness's own
        // source-identity check, so the z3-agreement gate and the
        // self-certification gate BOTH sat out — and the certificate still said
        // `pass: true` off `disagree == 0` and `self_conflict == 0`.
        "gates": {
            "z3_agreement": z3_available,
            // Self-certification ran iff it certified something; the harness
            // refuses the CLI outright on a source mismatch, which yields 0.
            "self_certification": totals.self_cert > 0,
            // The z3-independent oracle: it ran iff some file carried a decided
            // `(set-info :status)`.
            "declared_status": totals.declared_decided > 0,
        },
        "gates_not_run": gates_not_run,
        // Every wrong answer gates the run, whichever oracle proved it wrong —
        // AND a gate that did not run cannot contribute a pass. FAIL-CLOSED:
        // absent evidence is not evidence of absence.
        "pass": totals.disagree == 0
            && totals.declared_conflict == 0
            && totals.self_conflict == 0
            && z3_available
            && totals.self_cert > 0
            && totals.declared_decided > 0,
    })
}

// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bench::OutcomeKind;

    fn ay(kind: OutcomeKind, ms: u64) -> BenchOutcome {
        BenchOutcome {
            kind,
            wall: Duration::from_millis(ms),
            peak_rss: None,
        }
    }
    fn ay_rss(kind: OutcomeKind, ms: u64, rss: Option<u64>) -> BenchOutcome {
        BenchOutcome {
            kind,
            wall: Duration::from_millis(ms),
            peak_rss: rss,
        }
    }
    fn v(vs: &[Verdict]) -> OutcomeKind {
        OutcomeKind::Verdicts(vs.to_vec())
    }

    /// Build a `FileRecord` from fully-specified AY / z3 outcomes (used by the
    /// rating-ladder tests that need to drive wall AND peak-RSS bars). The file
    /// declares nothing; [`declared`] attaches an annotation.
    fn rec_out(ay_o: BenchOutcome, z3_o: Option<BenchOutcome>, sc: SelfCheck) -> FileRecord {
        let category = z3_o.as_ref().map(|z| categorize(&ay_o, z));
        let ratio = matches!(
            category,
            Some(Category::AgreeSat | Category::AgreeUnsat | Category::AgreeMixed)
        )
        .then(|| ratio_of(&ay_o, z3_o.as_ref().unwrap()));
        FileRecord {
            division: "D".into(),
            file: PathBuf::from("f.smt2"),
            ay: ay_o,
            z3: z3_o,
            selfcheck: sc,
            declared: DeclaredStatus::Absent,
            category,
            ratio,
        }
    }

    /// Attach a benchmark's own `(set-info :status ...)` to a record.
    fn declared(mut r: FileRecord, d: DeclaredStatus) -> FileRecord {
        r.declared = d;
        r
    }

    fn rec(
        ayk: OutcomeKind,
        ay_ms: u64,
        z3k: Option<OutcomeKind>,
        z3_ms: u64,
        sc: SelfCheck,
    ) -> FileRecord {
        rec_out(ay(ayk, ay_ms), z3k.map(|k| ay(k, z3_ms)), sc)
    }

    /// A convenient MB constant for RSS-bar tests (all above the 5 MB floor).
    const MB: u64 = 1024 * 1024;

    fn test_cfg() -> ScoreboardConfig {
        ScoreboardConfig {
            ay: PathBuf::from("missing-ay-lib"),
            ay_cli: None,
            z3: PathBuf::from("missing-z3-lib"),
            root: PathBuf::from("missing-corpus"),
            timeout_secs: 20,
            jobs: 8,
            json_out: PathBuf::from("unused.json"),
            baseline: None,
            divisions: None,
            checkpoint: None,
            resume: false,
            sample: None,
            seed: 0,
            progress: None,
        }
    }

    fn test_plan() -> ResourcePlan {
        ResourcePlan {
            requested_jobs: 8,
            jobs: 3,
            memlimit_mb_per_child: 2048,
            nbcore_per_child: 2,
            headroom_mb: 16_384,
            planner: "scripts/_oom_guard.py".to_string(),
        }
    }

    /// Build the JSON certificate for a set of records, as a real run would.
    fn certificate_of(
        records: &[FileRecord],
        divisions: &BTreeMap<String, DivStats>,
        totals: &DivStats,
    ) -> serde_json::Value {
        let cfg = test_cfg();
        let plan = test_plan();
        let evidence =
            resource_evidence(&plan, Duration::from_secs(20), true).expect("resource evidence");
        build_certificate(
            &cfg,
            records,
            divisions,
            totals,
            None,
            None,
            None,
            true,
            None,
            Duration::from_secs(1),
            &plan,
            &evidence,
            records.len(),
            None,
        )
    }

    #[test]
    fn certificate_uses_true_decided_by_both_and_persists_resource_plan() {
        use Verdict::*;
        let record = rec(
            v(&[Sat]),
            20,
            Some(v(&[Sat, Sat])),
            30,
            SelfCheck::Verdicts(vec![Sat]),
        );
        let mut stats = DivStats::default();
        stats.add(&record);
        assert_eq!(stats.both_decided, 1);
        assert!(stats.ratios.is_empty());
        let mut divisions = BTreeMap::new();
        divisions.insert("D".to_string(), stats.clone());
        let cert = certificate_of(&[record], &divisions, &stats);
        assert_eq!(cert["format_version"], 3);
        assert_eq!(cert["totals"]["decided_by_both"], 1);
        assert_eq!(cert["totals"]["wall_ratio_sample_count"], 0);
        assert_eq!(cert["totals"]["rating_ladder"]["decided_by_both"], 1);
        assert!(
            cert["totals"].get("strict_superiority").is_none(),
            "the certificate must expose the documented rating ladder, not the retired strict metric",
        );
        assert_eq!(cert["jobs"], 3);
        assert_eq!(cert["requested_jobs"], 8);
        assert_eq!(cert["resource"]["memlimit_mb_per_child"], 2048);
    }

    #[test]
    fn agree_counts_and_solved_pct() {
        use Verdict::*;
        let mut s = DivStats::default();
        // both decide unsat, AY faster: agree, self-certified.
        s.add(&rec(
            v(&[Unsat]),
            5,
            Some(v(&[Unsat])),
            8,
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        // z3 decides sat, AY unknown: a loss (not agree, not beyond).
        s.add(&rec(
            v(&[Unknown]),
            5,
            Some(v(&[Sat])),
            8,
            SelfCheck::Verdicts(vec![Unknown]),
        ));
        assert_eq!(s.files, 2);
        assert_eq!(s.z3_decided, 2);
        assert_eq!(s.ay_decided, 1);
        assert_eq!(s.ay_agree, 1);
        assert_eq!(s.losses, 1);
        assert_eq!(s.solved_pct(), Some(50.0));
        assert_eq!(s.self_cert, 1);
        assert_eq!(s.selfcert_pct(), Some(100.0));
        assert_eq!(s.rating(true), Rating::BelowPar); // 1 loss
    }

    #[test]
    fn beyond_z3_when_ay_decides_and_z3_unknown() {
        use Verdict::*;
        let r = rec(
            v(&[Sat]),
            5,
            Some(v(&[Unknown])),
            8,
            SelfCheck::Verdicts(vec![Sat]),
        );
        assert!(r.beyond_z3());
        assert!(!r.loss());
        let mut s = DivStats::default();
        s.add(&r);
        assert_eq!(s.beyond, 1);
    }

    #[test]
    fn disagree_is_flagged_and_breaks_par() {
        use Verdict::*;
        let r = rec(
            v(&[Sat]),
            5,
            Some(v(&[Unsat])),
            8,
            SelfCheck::Verdicts(vec![Sat]),
        );
        assert!(r.disagree());
        let mut s = DivStats::default();
        s.add(&r);
        assert_eq!(s.disagree, 1);
        assert_eq!(s.rating(true), Rating::BelowPar);
    }

    // ----------------------------------------------------------------------
    // The declared-`:status` oracle: the wrong answers z3 cannot see
    // ----------------------------------------------------------------------

    /// The confirmed hole (scoreboard-2026-07-29-s50): on
    /// `…UFBV…fixpoint__sdlx-fixpoint-5.smt2` the file declares `unsat`, AY
    /// answered `sat`, and z3 TIMED OUT. With the gate defined only against z3
    /// there was no DISAGREE to raise, the run PASSED, and the wrong answer was
    /// even credited as a `beyond_z3` win. A declared conflict must be counted
    /// with z3 undecided — that is the entire point of the metric.
    #[test]
    fn declared_conflict_counts_when_z3_did_not_decide() {
        use Verdict::*;
        let r = declared(
            rec(
                v(&[Sat]),
                500,
                Some(OutcomeKind::Timeout),
                20_000,
                SelfCheck::Timeout,
            ),
            DeclaredStatus::Unsat,
        );
        assert!(!r.z3_decided(), "premise: z3 decided nothing");
        assert!(!r.disagree(), "z3 gave no verdict, so there is no DISAGREE");
        assert!(r.declared_conflict(), "the file itself says AY is wrong");
        assert!(!r.beyond_z3(), "a wrong answer is not capability");

        let mut s = DivStats::default();
        s.add(&r);
        assert_eq!(s.declared_conflict, 1);
        assert_eq!(s.disagree, 0, "the z3-based metric still reads 0 here");
        assert_eq!(
            s.beyond, 0,
            "the wrong answer must lose its beyond_z3 credit"
        );
        assert_eq!(s.declared_decided, 1);
        assert_eq!(s.declared_confirmed, 0);
        // It gates the rating exactly as a disagreement does, and cannot hide
        // behind `n/a` just because z3 decided nothing in this division.
        assert_eq!(s.rating(true), Rating::BelowPar);
        assert_eq!(s.rating(false), Rating::BelowPar);
        assert!(
            s.rating_cell(true).contains("w1"),
            "{}",
            s.rating_cell(true)
        );
    }

    /// A declared conflict is reported and fails the run's pass/fail gate, in
    /// the same certificate that reports the z3-based `disagree` (0 here).
    #[test]
    fn certificate_reports_declared_conflicts_and_fails_the_gate() {
        use Verdict::*;
        let record = declared(
            rec(
                v(&[Sat]),
                500,
                Some(OutcomeKind::Timeout),
                20_000,
                SelfCheck::Timeout,
            ),
            DeclaredStatus::Unsat,
        );
        let mut stats = DivStats::default();
        stats.add(&record);
        let mut divisions = BTreeMap::new();
        divisions.insert("UFBV".to_string(), stats.clone());
        let cert = certificate_of(&[record], &divisions, &stats);

        assert_eq!(cert["format_version"], 3);
        assert_eq!(cert["totals"]["declared_conflict"], 1);
        assert_eq!(cert["divisions"][0]["declared_conflict"], 1);
        assert_eq!(cert["totals"]["rating_ladder"]["declared_conflict"], 1);
        assert_eq!(cert["totals"]["disagree"], 0);
        assert_eq!(cert["files"][0]["declared"], "unsat");
        assert_eq!(cert["files"][0]["declared_conflict"], true);
        assert_eq!(
            cert["files"][0]["beyond_z3"], false,
            "a wrong answer must not read as capability"
        );
        assert_eq!(
            cert["declared_conflict_files"].as_array().map(Vec::len),
            Some(1)
        );
        assert_eq!(
            cert["declared_conflict_files"][0]["z3_decided"], false,
            "the entire point: z3 never decided this file"
        );
        assert_eq!(cert["disagree_files"].as_array().map(Vec::len), Some(0));
        assert_eq!(
            cert["pass"], false,
            "a wrong answer must fail the run whichever oracle proved it"
        );
    }

    /// `absent` (no annotation) and a declared `unknown` are not oracles and
    /// must accuse nobody — and neither can an `unknown` from AY.
    #[test]
    fn absent_or_unknown_declaration_accuses_nobody() {
        use Verdict::*;
        for d in [DeclaredStatus::Absent, DeclaredStatus::Unknown] {
            let r = declared(
                rec(
                    v(&[Sat]),
                    5,
                    Some(OutcomeKind::Timeout),
                    20_000,
                    SelfCheck::Timeout,
                ),
                d,
            );
            assert!(!r.declared_conflict(), "{d:?} is not an oracle");
            assert!(!r.declared_confirmed(), "{d:?} confirms nothing");
            assert!(r.beyond_z3(), "an uncontradicted answer still counts");
            let mut s = DivStats::default();
            s.add(&r);
            assert_eq!(s.declared_decided, 0, "{d:?} is not a decided declaration");
        }
        // AY answering `unknown` contradicts nothing, however the file is marked.
        let r = declared(
            rec(
                v(&[Unknown]),
                5,
                None,
                0,
                SelfCheck::Verdicts(vec![Unknown]),
            ),
            DeclaredStatus::Unsat,
        );
        assert!(!r.declared_conflict());
        assert!(!r.declared_confirmed());
    }

    /// The positive side of the oracle: AY's answer matching the declaration is
    /// what turns a beyond-z3 claim into evidence.
    #[test]
    fn declared_confirmed_when_ay_matches_the_annotation() {
        use Verdict::*;
        let r = declared(
            rec(
                v(&[Unsat]),
                500,
                Some(OutcomeKind::Timeout),
                20_000,
                SelfCheck::Timeout,
            ),
            DeclaredStatus::Unsat,
        );
        assert!(r.declared_confirmed());
        assert!(!r.declared_conflict());
        assert!(r.beyond_z3());
        let mut s = DivStats::default();
        s.add(&r);
        assert_eq!(s.declared_decided, 1);
        assert_eq!(s.declared_confirmed, 1);
        assert_eq!(s.declared_conflict, 0);
    }

    /// Beyond-z3 credit is split by whether AY re-proved the answer to itself.
    /// 119 beyond-z3 files of which 66 were uncorroborated read as capability
    /// while the split was invisible.
    #[test]
    fn beyond_z3_credit_is_split_into_certified_and_unverified() {
        use Verdict::*;
        let mut s = DivStats::default();
        // AY decides where z3 is unknown, and re-proves it via --self-check.
        s.add(&rec(
            v(&[Unsat]),
            5,
            Some(v(&[Unknown])),
            8,
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        // AY decides where z3 times out, with nothing corroborating the answer.
        s.add(&rec(
            v(&[Sat]),
            5,
            Some(OutcomeKind::Timeout),
            20_000,
            SelfCheck::Timeout,
        ));
        assert_eq!(s.beyond, 2);
        assert_eq!(s.beyond_certified, 1);
        assert_eq!(s.beyond_unverified, 1);
        assert_eq!(s.beyond_certified + s.beyond_unverified, s.beyond);

        let mut divisions = BTreeMap::new();
        divisions.insert("D".to_string(), s.clone());
        let cert = certificate_of(&[], &divisions, &s);
        assert_eq!(cert["totals"]["beyond_z3"], 2);
        assert_eq!(cert["totals"]["beyond_z3_self_certified"], 1);
        assert_eq!(cert["totals"]["beyond_z3_unverified"], 1);
        // And the table cell states the split rather than one flattering number.
        let row = stats_row("D", &s, true, None);
        assert!(row.contains(&"2 (1c/1u)".to_string()), "{row:?}");
    }

    #[test]
    fn matching_faster_run_reaches_par_without_rss_evidence() {
        use Verdict::*;
        let mut s = DivStats::default();
        // AY strictly faster on a meaningful (>10ms) file.
        s.add(&rec(
            v(&[Unsat]),
            20,
            Some(v(&[Unsat])),
            50,
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        assert_eq!(s.rating(true), Rating::Par);
        assert_eq!(s.rating(false), Rating::NotApplicable);
    }

    #[test]
    fn decisive_verdict_count_mismatch_blocks_par() {
        use Verdict::*;
        let r = rec(
            v(&[Sat]),
            5,
            Some(v(&[Sat, Sat])),
            8,
            SelfCheck::Verdicts(vec![Sat]),
        );
        assert!(r.ay_decided());
        assert!(r.z3_decided());
        assert!(r.verdict_shape_mismatch());
        let mut s = DivStats::default();
        s.add(&r);
        assert_eq!(s.losses, 0);
        assert_eq!(s.verdict_shape_mismatches, 1);
        // A verdict-shape mismatch is a PAR coverage blocker: below par, shown m1.
        assert_eq!(s.rating(true), Rating::BelowPar);
        assert!(s.rating_cell(true).contains("m1"));
    }

    #[test]
    fn slower_blocks_par_only_above_floor() {
        use Verdict::*;
        // AY 50ms vs z3 20ms, both agree unsat: AY slower and above 10ms floor.
        let mut s = DivStats::default();
        s.add(&rec(
            v(&[Unsat]),
            50,
            Some(v(&[Unsat])),
            20,
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        assert_eq!(s.wall_losses, 1);
        assert_eq!(s.rating(true), Rating::BelowPar);

        // AY 3ms vs z3 1ms: slower but under the 10ms floor -> not a blocker.
        let mut s2 = DivStats::default();
        s2.add(&rec(
            v(&[Unsat]),
            3,
            Some(v(&[Unsat])),
            1,
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        assert_eq!(s2.wall_losses, 0);
        assert_eq!(s2.rating(true), Rating::Par);
    }

    #[test]
    fn self_conflict_detected() {
        use Verdict::*;
        // AY eval says unsat, self-check says sat: an internal soundness alarm.
        let r = rec(v(&[Unsat]), 5, None, 0, SelfCheck::Verdicts(vec![Sat]));
        assert!(r.self_conflict());
        assert!(!r.self_certified());
    }

    #[test]
    fn selfcheck_verdict_shape_mismatch_is_a_conflict() {
        use Verdict::*;
        let r = rec(
            v(&[Unsat]),
            5,
            None,
            0,
            SelfCheck::Verdicts(vec![Unsat, Unsat]),
        );
        assert!(r.self_conflict());
        assert!(!r.self_certified());
    }

    #[test]
    fn selfcert_denominator_is_ay_decided() {
        use Verdict::*;
        let mut s = DivStats::default();
        // AY unknown, self-check unknown: not decided, not certified.
        s.add(&rec(
            v(&[Unknown]),
            5,
            None,
            0,
            SelfCheck::Verdicts(vec![Unknown]),
        ));
        // AY decides unsat but self-check can't certify (unknown): decided, not certified.
        s.add(&rec(
            v(&[Unsat]),
            5,
            None,
            0,
            SelfCheck::Verdicts(vec![Unknown]),
        ));
        assert_eq!(s.ay_decided, 1);
        assert_eq!(s.self_cert, 0);
        assert_eq!(s.selfcert_pct(), Some(0.0));
    }

    #[test]
    fn z3_absent_makes_z3_columns_na() {
        use Verdict::*;
        let mut s = DivStats::default();
        s.add(&rec(
            v(&[Unsat]),
            5,
            None,
            0,
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        assert_eq!(s.solved_pct(), None); // z3_decided == 0
        assert_eq!(s.selfcert_pct(), Some(100.0));
        assert_eq!(s.rating(false), Rating::NotApplicable);
    }

    #[test]
    fn division_of_uses_subdir_name() {
        let root = PathBuf::from("corpus");
        assert_eq!(division_of(&root, &root.join("QF_UF/x.smt2")), "QF_UF");
        assert_eq!(division_of(&root, &root.join("QF_UF/deep/x.smt2")), "QF_UF");
        assert_eq!(division_of(&root, &root.join("top.smt2")), "(root)");
    }

    #[test]
    fn build_identity_parsers_accept_structured_and_clap_version_output() {
        let stamp = "0.10.0+build.424.0123456789abcdef@2026-07-22T12:34:56Z";
        let structured =
            format!("ay {stamp}\nbuild.commit=0123456789abcdef\nbuild.stamp={stamp}\n");
        assert_eq!(
            stamp_from_version_output(&structured).as_deref(),
            Some(stamp)
        );
        assert_eq!(
            commit_from_build_stamp(stamp).as_deref(),
            Some("0123456789abcdef")
        );
        assert_eq!(
            stamp_from_version_output(&format!("ay {stamp}\n")).as_deref(),
            Some(stamp)
        );
        assert_eq!(commit_from_build_stamp("not-a-build-stamp"), None);
    }

    #[test]
    fn selfcert_source_coherence_is_fail_closed() {
        let ffi = "0.10.0+build.424.0123456789abcdef@2026-07-22T12:34:56Z";
        let same_source = "0.10.0+build.424.0123456789abcdef@2026-07-22T12:35:01Z";
        let other_source = "0.10.0+build.425.fedcba9876543210@2026-07-22T12:35:01Z";
        let dirty = "0.10.0+build.424.0123456789abcdef-dirty@2026-07-22T12:35:01Z";

        assert_eq!(source_coherence_error(Some(ffi), Some(same_source)), None);
        assert!(source_coherence_error(Some(ffi), Some(other_source))
            .unwrap()
            .contains("source mismatch"));
        assert!(source_coherence_error(Some(dirty), Some(dirty))
            .unwrap()
            .contains("dirty"));
        assert!(source_coherence_error(None, Some(same_source)).is_some());
        assert!(source_coherence_error(Some(ffi), None).is_some());
    }

    /// `ay-z3-parity fetch` stages divisions through `.{div}.fetch-backup-*`
    /// siblings inside the corpus root. One leaked on the 2026-07-24 full fetch
    /// and the scoreboard scored `.AUFDTLIRA.fetch-backup-...` as a division,
    /// double-counting 218 files. Hidden directories are never corpus content.
    #[test]
    fn corpus_collection_skips_hidden_staging_and_backup_dirs() {
        let root = std::env::temp_dir().join(format!(
            "ay-z3-scoreboard-hidden-{}-{}",
            std::process::id(),
            utc_now_iso().replace([':', '-', '.'], "")
        ));
        let real = root.join("QF_UF");
        let leaked = root.join(".QF_UF.fetch-backup-1-2");
        std::fs::create_dir_all(&real).expect("mkdir real");
        std::fs::create_dir_all(&leaked).expect("mkdir leaked");
        std::fs::write(real.join("a.smt2"), b"(check-sat)").expect("write real");
        std::fs::write(leaked.join("a.smt2"), b"(check-sat)").expect("write leaked");

        let found = collect(&root, None).expect("collect");
        assert_eq!(
            found.len(),
            1,
            "leaked backup must not be walked: {found:?}"
        );
        assert_eq!(found[0].0, "QF_UF");
        let _ = std::fs::remove_dir_all(&root);
    }

    fn outcome(kind: OutcomeKind, ms: u64, rss: Option<u64>) -> BenchOutcome {
        BenchOutcome {
            kind,
            wall: Duration::from_millis(ms),
            peak_rss: rss,
        }
    }

    /// Every outcome shape must survive the journal, including the timing and
    /// RSS the certificate's geomean columns are computed from — a journal that
    /// loses those would silently change the result on resume.
    #[test]
    fn checkpoint_round_trips_every_outcome_shape() {
        let cases = vec![
            outcome(
                OutcomeKind::Verdicts(vec![Verdict::Sat, Verdict::Unsat]),
                1234,
                Some(9_000),
            ),
            outcome(OutcomeKind::Verdicts(vec![]), 1, None),
            outcome(OutcomeKind::Timeout, 20_000, None),
            outcome(OutcomeKind::MemoryLimit, 500, Some(1)),
            outcome(OutcomeKind::Crash("SIGSEGV".into()), 7, None),
            outcome(OutcomeKind::InputError("bad sort".into()), 3, Some(42)),
        ];
        for c in cases {
            let back = outcome_from_json(&outcome_to_json(&c)).expect("round trip");
            assert_eq!(back.label(), c.label());
            assert_eq!(back.detail(), c.detail());
            assert_eq!(back.wall, c.wall, "wall must survive: {}", c.label());
            assert_eq!(back.peak_rss, c.peak_rss, "rss must survive: {}", c.label());
        }
        for s in [
            SelfCheck::Verdicts(vec![Verdict::Unsat]),
            SelfCheck::Timeout,
            SelfCheck::MemoryLimit,
            SelfCheck::Crash("SIGKILL".into()),
            SelfCheck::Error("no ay CLI".into()),
        ] {
            let back = selfcheck_from_json(&selfcheck_to_json(&s)).expect("round trip");
            assert_eq!(back.label(), s.label());
            assert_eq!(back.detail(), s.detail());
        }
    }

    /// Resuming across a different binary, timeout, or corpus would produce a
    /// certificate describing neither run, so a header mismatch is fatal. A
    /// truncated last line is the normal shape of a crash and must be tolerated.
    #[test]
    fn checkpoint_refuses_foreign_header_and_tolerates_a_torn_tail() {
        let dir = std::env::temp_dir().join(format!(
            "ay-z3-scoreboard-ckpt-{}-{}",
            std::process::id(),
            utc_now_iso().replace([':', '-', '.'], "")
        ));
        std::fs::create_dir_all(&dir).expect("mkdir");
        let path = dir.join("c.jsonl");

        let header = serde_json::json!({"checkpoint_schema": 1, "timeout_secs": 20});
        let rec = serde_json::json!({
            "file": "/corpus/QF_UF/a.smt2",
            "division": "QF_UF",
            "ay": outcome_to_json(&outcome(OutcomeKind::Verdicts(vec![Verdict::Unsat]), 5, None)),
            "z3": serde_json::Value::Null,
            "self": selfcheck_to_json(&SelfCheck::Verdicts(vec![Verdict::Unsat])),
        });
        // Third line is deliberately torn, as a SIGKILL mid-write leaves it.
        std::fs::write(&path, format!("{header}\n{rec}\n{{\"file\": \"/corpus/QF")).expect("write");

        let loaded = load_checkpoint(&path, &header).expect("matching header loads");
        assert_eq!(loaded.len(), 1, "torn tail must be dropped, not invented");
        assert!(loaded.contains_key(Path::new("/corpus/QF_UF/a.smt2")));

        let foreign = serde_json::json!({"checkpoint_schema": 1, "timeout_secs": 10});
        let err = load_checkpoint(&path, &foreign).expect_err("foreign header must be refused");
        assert!(err.contains("different run"), "{err}");

        let _ = std::fs::remove_dir_all(&dir);
    }

    fn corpus(divs: &[(&str, usize)]) -> Vec<(String, PathBuf)> {
        let mut v = Vec::new();
        for (d, n) in divs {
            for i in 0..*n {
                v.push((
                    (*d).to_string(),
                    PathBuf::from(format!("/c/{d}/f{i:04}.smt2")),
                ));
            }
        }
        v
    }

    /// The sample is the unit of comparability for a continuously-run
    /// benchmark, so it must be a pure function of (seed, path): same seed →
    /// same set, every time, on every machine and toolchain.
    #[test]
    fn sampling_is_deterministic_per_seed_and_bounded_per_division() {
        let c = corpus(&[("QF_UF", 100), ("QF_AX", 3), ("QF_BV", 100)]);
        let (a, census) = sample_per_division(c.clone(), 10, 42);
        let (b, _) = sample_per_division(c.clone(), 10, 42);
        assert_eq!(a, b, "same seed must reproduce the same sample");

        // Bounded PER DIVISION, and a small division is taken whole rather than
        // padded — every track stays represented.
        assert_eq!(census["QF_UF"], (10, 100));
        assert_eq!(census["QF_BV"], (10, 100));
        assert_eq!(census["QF_AX"], (3, 3));
        assert_eq!(a.len(), 23);

        // A different seed is an independent sample, not the same one.
        let (d, _) = sample_per_division(c.clone(), 10, 43);
        assert_ne!(a, d, "a different seed must select differently");

        // Execution order is sorted, so the run itself is deterministic too.
        let mut sorted = a.clone();
        sorted.sort();
        assert_eq!(a, sorted);
    }

    /// Hash-ranked, not index-spaced: a file's rank depends only on (seed,
    /// path), never on how many other files exist. So growing the corpus can
    /// only displace a selected file by out-ranking it — it cannot reshuffle the
    /// selection wholesale, which is what an index rule (`i*total/n`) does. That
    /// keeps a track's numbers comparable across corpus refreshes.
    ///
    /// Doubling the corpus is expected to retain ~N/2 of the sample; asserted
    /// loosely because this is one draw, and the exact invariant (rank is
    /// corpus-independent) is checked directly below it.
    #[test]
    fn sampling_is_stable_when_the_corpus_grows() {
        let before = corpus(&[("QF_UF", 200)]);
        let after = corpus(&[("QF_UF", 400)]);
        let (a, _) = sample_per_division(before, 100, 7);
        let (b, _) = sample_per_division(after, 100, 7);
        let kept = a.iter().filter(|f| b.contains(f)).count();
        assert!(
            kept >= 30,
            "doubling the corpus should retain ~half the sample, kept {kept}/100"
        );

        // The exact invariant: every survivor kept its rank key, and every
        // dropped file was displaced by a strictly better-ranked newcomer.
        let worst_kept = b
            .iter()
            .map(|(_, p)| fnv1a64(7, p.as_os_str().as_encoded_bytes()))
            .max()
            .expect("non-empty");
        for (_, p) in a.iter().filter(|f| !b.contains(f)) {
            assert!(
                fnv1a64(7, p.as_os_str().as_encoded_bytes()) >= worst_kept,
                "a dropped file must rank no better than the worst survivor"
            );
        }
    }

    #[test]
    fn corpus_collection_fails_closed_when_root_is_missing() {
        let missing = std::env::temp_dir().join(format!(
            "ay-z3-scoreboard-missing-{}-{}",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        ));
        assert!(collect(&missing, None).is_err());
    }

    // ----------------------------------------------------------------------
    // Rating ladder: PAR / SUPERIOR / PERFECT / below / n/a
    // ----------------------------------------------------------------------

    #[test]
    fn rating_na_when_z3_absent_or_z3_decided_nothing() {
        use Verdict::*;
        let mut s = DivStats::default();
        // z3 present in the type sense but None here: z3_decided == 0.
        s.add(&rec(
            v(&[Unsat]),
            5,
            None,
            0,
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        assert_eq!(s.rating(false), Rating::NotApplicable); // z3 absent
        assert_eq!(s.rating(true), Rating::NotApplicable); // nothing z3 decided
        assert_eq!(s.rating_cell(true), "n/a");
    }

    #[test]
    fn rating_below_par_on_undecided_loss() {
        use Verdict::*;
        // z3 decides sat, AY unknown: an undecided loss.
        let mut s = DivStats::default();
        s.add(&rec(
            v(&[Unknown]),
            5,
            Some(v(&[Sat])),
            8,
            SelfCheck::Verdicts(vec![Unknown]),
        ));
        assert_eq!(s.rating(true), Rating::BelowPar);
        assert!(
            s.rating_cell(true).contains("u1"),
            "{}",
            s.rating_cell(true)
        );
    }

    #[test]
    fn rating_below_par_when_slower_over_the_wall_floor() {
        use Verdict::*;
        // Agree unsat, AY 50ms vs z3 20ms (AY slower, over the 10ms floor).
        let mut s = DivStats::default();
        s.add(&rec(
            v(&[Unsat]),
            50,
            Some(v(&[Unsat])),
            20,
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        assert_eq!(s.wall_losses, 1);
        assert_eq!(s.rating(true), Rating::BelowPar);
        assert!(
            s.rating_cell(true).contains("s1"),
            "{}",
            s.rating_cell(true)
        );
    }

    #[test]
    fn rating_par_when_faster_but_not_two_x() {
        use Verdict::*;
        // Agree unsat, AY 40ms vs z3 50ms: faster (PAR) but under 2x (not SUPERIOR).
        let mut s = DivStats::default();
        s.add(&rec_out(
            ay_rss(v(&[Unsat]), 40, Some(8 * MB)),
            Some(ay_rss(v(&[Unsat]), 50, Some(20 * MB))),
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        assert_eq!(s.wall_losses, 0);
        assert_eq!(s.wall_not_2x, 1);
        assert_eq!(s.rating(true), Rating::Par);
        assert_eq!(s.rating_cell(true), "PAR(x1,m0,r0)");
    }

    #[test]
    fn rating_par_when_two_x_fast_but_memory_regressed() {
        use Verdict::*;
        // AY 2x faster on wall, but its peak RSS is >= 80% of z3's: PAR, not SUPERIOR.
        let mut s = DivStats::default();
        s.add(&rec_out(
            ay_rss(v(&[Unsat]), 20, Some(19 * MB)),
            Some(ay_rss(v(&[Unsat]), 50, Some(20 * MB))),
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        assert_eq!(s.wall_not_2x, 0);
        assert_eq!(s.rss_cmp, 1);
        assert_eq!(s.rss_not_80, 1);
        assert_eq!(s.rating(true), Rating::Par);
        assert_eq!(s.rating_cell(true), "PAR(x0,m1,r0)");
    }

    #[test]
    fn rating_missing_rss_fails_closed_at_par() {
        use Verdict::*;
        let mut s = DivStats::default();
        s.add(&rec(
            v(&[Unsat]),
            20,
            Some(v(&[Unsat])),
            50,
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        assert_eq!(s.wall_not_2x, 0);
        assert_eq!(s.rss_cmp, 0);
        assert_eq!(s.rss_missing, 1);
        assert_eq!(s.rating(true), Rating::Par);
        assert_eq!(s.rating_cell(true), "PAR(x0,m0,r1)");
    }

    #[test]
    fn rating_superior_but_not_perfect_when_a_track_file_is_unsolved() {
        use Verdict::*;
        let mut s = DivStats::default();
        // Decided-by-both: AY >= 2x faster AND under 80% peak memory.
        s.add(&rec_out(
            ay_rss(v(&[Unsat]), 20, Some(8 * MB)),
            Some(ay_rss(v(&[Unsat]), 50, Some(20 * MB))),
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        // A file neither solver decides: not a loss, but AY is below 100% solved.
        s.add(&rec_out(
            ay_rss(v(&[Unknown]), 5, None),
            Some(ay_rss(v(&[Unknown]), 5, None)),
            SelfCheck::Verdicts(vec![Unknown]),
        ));
        assert_eq!(s.wall_not_2x, 0);
        assert_eq!(s.rss_not_80, 0);
        assert_eq!(s.unsolved(), 1);
        assert_eq!(s.rating(true), Rating::Superior);
        assert_eq!(s.rating_cell(true), "SUPERIOR(u1)");
    }

    #[test]
    fn rating_perfect_when_superior_and_all_files_solved() {
        use Verdict::*;
        let mut s = DivStats::default();
        s.add(&rec_out(
            ay_rss(v(&[Unsat]), 20, Some(8 * MB)),
            Some(ay_rss(v(&[Unsat]), 50, Some(20 * MB))),
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        assert_eq!(s.rating(true), Rating::Perfect);
        assert_eq!(s.rating_cell(true), "PERFECT");
    }

    #[test]
    fn rss_floor_excludes_small_processes_from_the_memory_bar() {
        use Verdict::*;
        // 2x faster on wall; both peaks below the 5 MB floor -> no memory bar.
        let mut s = DivStats::default();
        s.add(&rec_out(
            ay_rss(v(&[Unsat]), 20, Some(MB)),
            Some(ay_rss(v(&[Unsat]), 50, Some(2 * MB))),
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        assert_eq!(s.rss_cmp, 0);
        assert_eq!(s.rss_not_80, 0);
        assert_eq!(s.rating(true), Rating::Perfect);
    }

    #[test]
    fn wall_floor_excludes_trivial_files_from_the_speed_bar() {
        use Verdict::*;
        // AY slower than z3 but both under the 10ms floor -> not a wall loss.
        let mut s = DivStats::default();
        s.add(&rec_out(
            ay_rss(v(&[Unsat]), 3, Some(MB)),
            Some(ay_rss(v(&[Unsat]), 1, Some(2 * MB))),
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        assert_eq!(s.wall_cmp, 0);
        assert_eq!(s.wall_losses, 0);
        assert_eq!(s.rating(true), Rating::Perfect);
    }

    /// The headline speed statistic must not be fabricated by timer
    /// granularity. `geo_ratio` floors each side at `RATIO_FLOOR_SECS`
    /// (0.1 ms) and admits every decided-by-both file, so a 3 ms-vs-1 ms pair
    /// — two solvers that are both instant — enters it as a 3x loss.
    /// `geo_ratio_timed` applies the ladder's own eligibility rule and
    /// excludes it. This asymmetry is the whole point of the second statistic:
    /// if the two floors are ever unified the published 4.496x geomean becomes
    /// unreproducible, so pin them apart.
    #[test]
    fn timed_geomean_excludes_sub_floor_files_that_the_raw_geomean_admits() {
        use Verdict::*;
        let mut s = DivStats::default();
        // 3 ms vs 1 ms: both far below the 10 ms floor. Pure scheduler noise.
        s.add(&rec_out(
            ay_rss(v(&[Unsat]), 3, Some(MB)),
            Some(ay_rss(v(&[Unsat]), 1, Some(MB))),
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        assert_eq!(s.ratios.len(), 1, "raw geomean admits the sub-floor file");
        assert_eq!(
            s.ratios_timed.len(),
            0,
            "the timed geomean must exclude it — below the floor a ratio is \
             timer granularity, not a speed difference"
        );
        assert!(
            s.geo_ratio().is_some_and(|g| g > 2.0),
            "the raw statistic reports this noise as a >2x loss: {:?}",
            s.geo_ratio()
        );
        assert_eq!(
            s.geo_ratio_timed(),
            None,
            "with no eligible file the honest statistic reports nothing, \
             rather than reporting noise"
        );

        // Now a genuinely timed file: 200 ms vs 100 ms is a real 2x loss.
        s.add(&rec_out(
            ay_rss(v(&[Unsat]), 200, Some(MB)),
            Some(ay_rss(v(&[Unsat]), 100, Some(MB))),
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        assert_eq!(s.ratios_timed.len(), 1);
        let timed = s.geo_ratio_timed().expect("one eligible file");
        assert!(
            (timed - 2.0).abs() < 1e-9,
            "timed geomean must be exactly the eligible file's ratio, got {timed}"
        );
        // Σay/Σz3 = (3+200)/(1+100) — dominated by the file that took real
        // time, which is the property that makes it worth publishing.
        let total = s.total_ratio().expect("z3 spent measurable time");
        assert!(
            (total - 203.0 / 101.0).abs() < 1e-9,
            "aggregate-cost ratio must be sum-based, got {total}"
        );
    }

    #[test]
    fn mem_geo_is_geomean_of_the_rss_ratios() {
        use Verdict::*;
        let mut s = DivStats::default();
        // ratio 0.5 then 2.0 -> geomean 1.0.
        s.add(&rec_out(
            ay_rss(v(&[Unsat]), 20, Some(10 * MB)),
            Some(ay_rss(v(&[Unsat]), 20, Some(20 * MB))),
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        s.add(&rec_out(
            ay_rss(v(&[Unsat]), 20, Some(20 * MB)),
            Some(ay_rss(v(&[Unsat]), 20, Some(10 * MB))),
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        assert_eq!(s.rss_cmp, 2);
        let g = s.mem_geo().expect("two ratios");
        assert!((g - 1.0).abs() < 1e-9, "geomean {g}");
    }

    #[test]
    fn delta_reports_rating_transition() {
        use Verdict::*;
        let mut s = DivStats::default();
        // Now: SUPERIOR (one unsolved file keeps it below PERFECT).
        s.add(&rec_out(
            ay_rss(v(&[Unsat]), 20, Some(8 * MB)),
            Some(ay_rss(v(&[Unsat]), 50, Some(20 * MB))),
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        s.add(&rec_out(
            ay_rss(v(&[Unknown]), 5, None),
            Some(ay_rss(v(&[Unknown]), 5, None)),
            SelfCheck::Verdicts(vec![Unknown]),
        ));
        assert_eq!(s.rating(true), Rating::Superior);
        let mut divisions = BTreeMap::new();
        divisions.insert(
            "D".to_string(),
            BaselineDiv {
                solved_pct: Some(100.0),
                selfcert_pct: Some(100.0),
                rating: Some("PAR".to_string()),
            },
        );
        let base = Baseline {
            path: "b.json".into(),
            divisions,
        };
        let cell = delta_cell("D", &s, true, &base);
        assert!(cell.contains("PAR->SUPERIOR"), "{cell}");
    }

    /// Bumping `format_version` must not orphan the certificates already on
    /// disk: a format-2 baseline (written before the declared-`:status` fields
    /// existed) still loads and still yields a DELTA, because every field is
    /// looked up by name.
    #[test]
    fn baseline_from_a_format_2_certificate_still_yields_delta() {
        use Verdict::*;
        let dir = std::env::temp_dir().join(format!(
            "ay-z3-scoreboard-v2base-{}-{}",
            std::process::id(),
            utc_now_iso().replace([':', '-', '.'], "")
        ));
        std::fs::create_dir_all(&dir).expect("mkdir");
        let path = dir.join("v2.json");
        let v2 = serde_json::json!({
            "kind": "ay-z3-scoreboard",
            "format_version": 2,
            "divisions": [
                {"name": "D", "solved_pct": 90.0, "selfcert_pct": 50.0, "rating": "PAR"},
            ],
            "totals": {"name": "TOTAL", "solved_pct": 90.0, "selfcert_pct": 50.0, "rating": "PAR"},
        });
        std::fs::write(&path, v2.to_string()).expect("write");

        let base = load_baseline(&path).expect("a format-2 baseline still loads");
        assert!(base.divisions.contains_key("D"));
        assert!(base.divisions.contains_key("TOTAL"));

        let mut s = DivStats::default();
        s.add(&rec_out(
            ay_rss(v(&[Unsat]), 20, Some(8 * MB)),
            Some(ay_rss(v(&[Unsat]), 50, Some(20 * MB))),
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        let cell = delta_cell("D", &s, true, &base);
        assert!(cell.contains("s+10.0"), "{cell}");
        assert!(cell.contains("c+50.0"), "{cell}");
        assert!(cell.contains("PAR->PERFECT"), "{cell}");

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn delta_rating_unchanged_shows_equals() {
        use Verdict::*;
        let mut s = DivStats::default();
        s.add(&rec_out(
            ay_rss(v(&[Unsat]), 20, Some(8 * MB)),
            Some(ay_rss(v(&[Unsat]), 50, Some(20 * MB))),
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        assert_eq!(s.rating(true), Rating::Perfect);
        let mut divisions = BTreeMap::new();
        divisions.insert(
            "D".to_string(),
            BaselineDiv {
                solved_pct: Some(100.0),
                selfcert_pct: Some(100.0),
                rating: Some("PERFECT".to_string()),
            },
        );
        let base = Baseline {
            path: "b.json".into(),
            divisions,
        };
        let cell = delta_cell("D", &s, true, &base);
        assert!(cell.ends_with('='), "{cell}");
    }
}
