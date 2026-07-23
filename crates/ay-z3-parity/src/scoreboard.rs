// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `scoreboard` subcommand — a per-division progress tracker for the AY↔z3
//! parity campaign, on TWO metrics at once:
//!
//! * the **z3-agreement** metric (does AY decide what z3 decides, and agree),
//!   and
//! * AY's own **self-certification** metric (of the answers AY gives, how many
//!   can AY prove to *itself* via the fail-closed `ay solve --self-check`
//!   gate) — the campaign's real, z3-independent north star.
//!
//! For every division subdir under a corpus root, every `.smt2` file is run
//! through AY (via the FFI dylib), z3 (via libz3), and `ay --self-check` (via
//! a CLI binary proved to come from the same clean source revision as the FFI
//! library). Each run is a fresh, timeboxed child process, reusing the exact
//! isolation/timing plumbing of the `bench` subcommand, so no crashing or
//! runaway solve can bias or abort the campaign.
//!
//! Output is a compact per-division table plus a persisted JSON certificate
//! carrying all raw per-division and per-file data. Given a prior certificate
//! via `--baseline`, a DELTA column tracks solved% / selfcert% / strict changes
//! across runs. Any `sat`-vs-`unsat` DISAGREE (AY vs z3) — or any self-check
//! answer that contradicts AY's own eval — is a wrong answer: it is surfaced
//! as a prominent WARNING and forces a nonzero exit.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::{Duration, Instant};

use crate::bench::{
    self, categorize, geomean, host_info, median, ratio_of, run_one, run_selfcheck, sha256_of,
    spawn_timeboxed, utc_now_iso, BenchOutcome, Category, SelfCheck, WIN_LOSS_MIN_SECS,
};
use crate::diff::Verdict;
use crate::loader;

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
    fn walk(path: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
        let metadata = std::fs::symlink_metadata(path)?;
        if metadata.is_dir() {
            let mut entries = std::fs::read_dir(path)?.collect::<Result<Vec<_>, _>>()?;
            entries.sort_by_key(std::fs::DirEntry::path);
            for entry in entries {
                walk(&entry.path(), out)?;
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
    /// AY decides where z3 does not (z3 unknown / timeout / crash / no-verdict).
    fn beyond_z3(&self) -> bool {
        self.z3.is_some() && self.ay_decided() && !self.z3_decided() && !self.disagree()
    }
    /// A strict-superiority "loss": z3 decides this file but AY does not.
    fn loss(&self) -> bool {
        self.z3_decided() && !self.ay_decided()
    }
    /// Both solvers returned only decisive answers, but their verdict-list
    /// shapes differ (for example one answer versus two). This is not a proved
    /// sat-vs-unsat conflict, but it is not agreement and therefore blocks a
    /// strict-superiority claim.
    fn verdict_shape_mismatch(&self) -> bool {
        self.z3_decided() && self.ay_decided() && self.category == Some(Category::Other)
    }
    /// A strict-superiority "slower": decided by both, AY slower than z3 with
    /// the (slower) AY side above the 10 ms noise floor.
    fn slower(&self) -> bool {
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
    a.iter().zip(b.iter()).any(|(x, y)| {
        matches!(
            (x, y),
            (Verdict::Sat, Verdict::Unsat) | (Verdict::Unsat, Verdict::Sat)
        )
    })
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
    losses: usize,
    verdict_shape_mismatches: usize,
    slower: usize,
    self_cert: usize,
    self_conflict: usize,
    ratios: Vec<f64>,
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
    /// Decided-by-both files for which either peak-RSS measurement is missing.
    /// Missing evidence must block SUPERIOR rather than satisfy its memory bar
    /// vacuously (notably on non-Unix hosts).
    rss_missing: usize,
    /// Decided-by-both files that do not establish AY below 80% of z3's peak:
    /// either an eligible measured pair with `ay_rss >= 0.8 * z3_rss`, or a
    /// missing measurement. Breaks SUPERIOR's memory bar.
    rss_not_80: usize,
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
        }
        if r.loss() {
            self.losses += 1;
        }
        if r.verdict_shape_mismatch() {
            self.verdict_shape_mismatches += 1;
        }
        if r.slower() {
            self.slower += 1;
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
                let slower = r.ay.wall.as_secs_f64().max(z3.wall.as_secs_f64());
                if slower >= WIN_LOSS_MIN_SECS {
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
                        self.rss_not_80 += 1;
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
        self.losses += o.losses;
        self.verdict_shape_mismatches += o.verdict_shape_mismatches;
        self.slower += o.slower;
        self.self_cert += o.self_cert;
        self.self_conflict += o.self_conflict;
        self.ratios.extend_from_slice(&o.ratios);
        self.ay_wins_2x += o.ay_wins_2x;
        self.z3_wins_2x += o.z3_wins_2x;
        self.both_decided += o.both_decided;
        self.wall_cmp += o.wall_cmp;
        self.wall_losses += o.wall_losses;
        self.wall_not_2x += o.wall_not_2x;
        self.rss_cmp += o.rss_cmp;
        self.rss_missing += o.rss_missing;
        self.rss_not_80 += o.rss_not_80;
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

    fn median_ratio(&self) -> Option<f64> {
        let mut s = self.ratios.clone();
        s.sort_by(|a, b| a.partial_cmp(b).expect("no NaN ratios"));
        median(&s)
    }

    /// STRICT SUPERIORITY over z3 for this division: AY agrees on every file z3
    /// decides (no undecided loss, verdict-shape mismatch, or disagreement), and
    /// AY is at least as fast as z3 on every agreed file above the 10 ms floor.
    /// Only meaningful when z3 actually decided something here.
    fn strict(&self, z3_available: bool) -> Option<bool> {
        if !z3_available {
            return None;
        }
        Some(
            self.z3_decided > 0
                && self.losses == 0
                && self.verdict_shape_mismatches == 0
                && self.slower == 0
                && self.disagree == 0,
        )
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
    /// * **PAR** — DISAGREE = 0, AND AY returns a decisive verdict matching
    ///   z3's on every file z3 decides (0 undecided losses, 0 verdict-shape
    ///   mismatches), AND on every decided-by-both file above `WALL_FLOOR`
    ///   `ay_wall <= z3_wall` (0 wall losses).
    /// * **SUPERIOR** — all of PAR, AND on every decided-by-both file above
    ///   `WALL_FLOOR` `ay_wall <= 0.5*z3_wall` (>= 2x faster; 0 `wall_not_2x`),
    ///   AND every decided-by-both file has both RSS measurements and, when
    ///   above `RSS_FLOOR`, `ay_rss < 0.8*z3_rss` (< 80% peak memory;
    ///   0 `rss_not_80`). Missing RSS is reject-only, never vacuous success.
    /// * **PERFECT** — all of SUPERIOR, AND AY solves EVERY file in the
    ///   division (decisive on 100% of the track, not merely what z3 decides).
    ///
    /// `n/a` (`Rating::NotApplicable`) when z3 is absent or decided nothing
    /// here — there is then nothing to rate AY against.
    fn rating(&self, z3_available: bool) -> Rating {
        if !z3_available || self.z3_decided == 0 {
            return Rating::NotApplicable;
        }
        let par = self.disagree == 0
            && self.losses == 0
            && self.verdict_shape_mismatches == 0
            && self.wall_losses == 0;
        if !par {
            return Rating::BelowPar;
        }
        let superior = self.wall_not_2x == 0 && self.rss_not_80 == 0;
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
                // mJ verdict-shape mismatches.
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
                if self.verdict_shape_mismatches > 0 {
                    parts.push(format!("m{}", self.verdict_shape_mismatches));
                }
                format!("below({})", parts.join(","))
            }
            // xN files missing the 2x-speed bar, mN missing the <80%-mem bar.
            Rating::Par => format!("PAR(x{},m{})", self.wall_not_2x, self.rss_not_80),
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

fn probe_ay_cli(path: PathBuf, ffi_build_stamp: Option<&str>) -> AyCliIdentity {
    const VERSION_TIMEOUT: Duration = Duration::from_secs(5);

    let sha256 = sha256_of(&path);
    let mut cmd = Command::new(&path);
    cmd.arg("--version");
    let raw = spawn_timeboxed(cmd, VERSION_TIMEOUT);

    let probe_error = if let Some(error) = raw.harness_error {
        Some(error)
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

    let ay_cli_identity =
        resolve_ay_cli(cfg).map(|path| probe_ay_cli(path, ay_build_stamp.as_deref()));
    let ay_cli = ay_cli_identity
        .as_ref()
        .filter(|identity| identity.source_coherent)
        .map(|identity| identity.path.clone());
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

    let timeout = Duration::from_secs(cfg.timeout_secs);
    let total = files.len();
    eprintln!(
        "scoreboard: {total} files, timeout {}s, jobs {}, AY={} z3={} ay-cli={}",
        cfg.timeout_secs,
        cfg.jobs,
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
                let z3 = z3_available.then(|| run_one(&exe, &cfg.z3, file, timeout));
                let ay = run_one(&exe, &cfg.ay, file, timeout);
                let selfcheck = match &ay_cli {
                    Some(cli) => run_selfcheck(cli, file, timeout),
                    None => SelfCheck::Error("no ay CLI".to_string()),
                };
                let category = z3.as_ref().map(|z| categorize(&ay, z));
                let ratio = matches!(
                    category,
                    Some(Category::AgreeSat | Category::AgreeUnsat | Category::AgreeMixed)
                )
                .then(|| ratio_of(&ay, z3.as_ref().expect("agree implies z3 present")));
                let n_done = done.fetch_add(1, Ordering::Relaxed) + 1;
                eprintln!(
                    "[{n_done}/{total}] {division} {}: z3={} ay={} self={} {}",
                    file.file_name().and_then(|n| n.to_str()).unwrap_or("?"),
                    z3.as_ref()
                        .map(BenchOutcome::label)
                        .unwrap_or_else(|| "-".into()),
                    ay.label(),
                    selfcheck.label(),
                    category.map(Category::label).unwrap_or(""),
                );
                slots.lock().expect("slots poisoned")[i] = Some(FileRecord {
                    division: division.clone(),
                    file: file.clone(),
                    ay,
                    z3,
                    selfcheck,
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
        "  corpus root:      {}  ({} files, timeout {}s, jobs {}, wall {:.1}s)",
        cfg.root.display(),
        total,
        cfg.timeout_secs,
        cfg.jobs,
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
    let conflicts: Vec<&FileRecord> = records.iter().filter(|r| r.self_conflict()).collect();
    let unsound = disagrees.len() + conflicts.len();
    if unsound == 0 {
        println!(
            "RESULT: PASS — 0 sat-vs-unsat disagreements (AY vs z3) and 0 \
             self-check contradictions across {} files.",
            totals.files
        );
    } else {
        println!("{}", "!".repeat(72));
        println!(
            "WARNING: {unsound} WRONG ANSWER(S) — {} AY-vs-z3 DISAGREE, {} \
             self-check contradiction(s). THIS RUN FAILS.",
            disagrees.len(),
            conflicts.len()
        );
        println!("{}", "!".repeat(72));
        for r in &disagrees {
            println!(
                "  DISAGREE  {}  declared={} z3={} ay={}",
                r.file.display(),
                bench::declared_status(&r.file).unwrap_or_else(|| "(none)".into()),
                r.z3.as_ref().map(BenchOutcome::label).unwrap_or_default(),
                r.ay.label()
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
            s.beyond.to_string()
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
         BEYOND = files AY decides but z3 does not\n\
         GEO ay/z3 = geomean WALL ratio over decided-by-both (<1 = AY faster)\n\
         MEM ay/z3 = geomean PEAK-RSS ratio over decided-by-both above 5MB (<1 = AY leaner)\n\
         RATING (per division; floors: WALL 10ms, RSS 5MB):\n\
         \x20 PAR      = DISAGREE 0, AY decides every z3 decision, ay_wall <= z3_wall on every decided-by-both file > 10ms\n\
         \x20 SUPERIOR = PAR + ay_wall <= 0.5*z3_wall (>=2x) on every such file + measured ay_rss < 0.8*z3_rss on every decided-by-both file > 5MB; missing RSS blocks\n\
         \x20 PERFECT  = SUPERIOR + AY decides 100% of the track's files\n\
         \x20 below(uN,sM,dK,mJ) = N undecided losses, M slower-than-z3, K disagreements, J verdict-shape mismatches\n\
         \x20 PAR(xN,mM) = N files miss the 2x-speed bar, M miss the <80%-mem bar | SUPERIOR(uN) = N track files AY doesn't solve\n",
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
            "self_certified": s.self_cert,
            "self_conflict": s.self_conflict,
            "solved_pct": s.solved_pct(),
            "selfcert_pct": s.selfcert_pct(),
            "decided_by_both": s.ratios.len(),
            "geomean_wall_ratio_ay_over_z3": s.geo_ratio(),
            "median_wall_ratio_ay_over_z3": s.median_ratio(),
            "ay_wins_2x": s.ay_wins_2x,
            "z3_wins_2x": s.z3_wins_2x,
            "strict_superiority": s.strict(z3_available),
            "strict_blockers": {
                "undecided_losses": s.losses,
                "verdict_shape_mismatches": s.verdict_shape_mismatches,
                "slower": s.slower,
                "disagree": s.disagree
            },
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
                // SUPERIOR blockers
                "wall_below_2x": s.wall_not_2x,
                "rss_below_80pct_not_established": s.rss_not_80,
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
                "beyond_z3": r.beyond_z3(),
                "loss": r.loss(),
                "verdict_shape_mismatch": r.verdict_shape_mismatch(),
                "slower": r.slower(),
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
                "declared_status": bench::declared_status(&r.file),
                "z3": r.z3.as_ref().map(BenchOutcome::label),
                "ay": r.ay.label(),
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
    serde_json::json!({
        "kind": "ay-z3-scoreboard",
        "format_version": 1,
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
        "timeout_secs": cfg.timeout_secs,
        "jobs": cfg.jobs,
        "campaign_wall_secs": campaign_wall.as_secs_f64(),
        "baseline": cfg.baseline.as_ref().map(|p| p.display().to_string()),
        "methodology": {
            "z3_agreement": "solved% = ay-agree / z3-decided; DISAGREE = positional sat-vs-unsat (AY vs z3), must be 0",
            "self_certification": "selfcert% = files AY self-certifies (a source-coherent ay solve --self-check exits cleanly within the deadline and emits the same decisive verdict AY's eval gives) / files AY decides; the z3-independent metric",
            "strict_superiority": "per division: AY agrees on every file z3 decides (0 undecided losses, verdict-shape mismatches, or disagreements) AND AY >= as fast as z3 on every agreed file with the AY side above 10ms (0 slower)",
            "rating_ladder": "per division, highest tier reached. decided-by-both = files AY and z3 both decide. PAR = DISAGREE 0 AND AY returns a decisive verdict matching z3 on every file z3 decides (0 undecided losses + 0 verdict-shape mismatches) AND ay_wall <= z3_wall on every decided-by-both file above the WALL floor. SUPERIOR = PAR AND ay_wall <= 0.5*z3_wall on every such file (>=2x) AND both peak-RSS measurements are present for every decided-by-both file AND ay_rss < 0.8*z3_rss on every measured pair above the RSS floor (<80% peak). PERFECT = SUPERIOR AND AY decides 100% of the track's files. n/a when z3 is absent or decided nothing.",
            "peak_rss": "per (file, solver) child peak resident set size in BYTES via wait4()/rusage.ru_maxrss; Darwin reports bytes, Linux kilobytes (normalized to bytes with cfg(target_os))",
            "isolation": "each (file, solver) pair and each self-check runs in a fresh timeboxed child (reuses `bench` plumbing); a crash/timeout on one file cannot bias or abort the run",
            "win_loss_min_secs": WIN_LOSS_MIN_SECS,
            "wall_floor_secs": WALL_FLOOR_SECS,
            "rss_floor_bytes": RSS_FLOOR_BYTES,
        },
        "divisions": divisions.iter().map(|(n, s)| div_json(n, s)).collect::<Vec<_>>(),
        "totals": div_json("TOTAL", totals),
        "files": files_json,
        "disagree_files": disagree_files,
        "self_conflict_files": self_conflict_files,
        "pass": totals.disagree == 0 && totals.self_conflict == 0,
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
    /// rating-ladder tests that need to drive wall AND peak-RSS bars).
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
            category,
            ratio,
        }
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
        assert_eq!(s.strict(true), Some(false)); // 1 loss
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
    fn disagree_is_flagged_and_breaks_strict() {
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
        assert_eq!(s.strict(true), Some(false));
    }

    #[test]
    fn strict_true_when_all_decided_and_at_least_as_fast() {
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
        assert_eq!(s.strict(true), Some(true));
        assert_eq!(s.strict(false), None); // z3 absent -> n/a
    }

    #[test]
    fn decisive_verdict_count_mismatch_blocks_strict_superiority() {
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
        assert_eq!(s.strict(true), Some(false));
        // A verdict-shape mismatch is a PAR coverage blocker: below par, shown m1.
        assert_eq!(s.rating(true), Rating::BelowPar);
        assert!(s.rating_cell(true).contains("m1"));
    }

    #[test]
    fn slower_blocks_strict_only_above_floor() {
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
        assert_eq!(s.slower, 1);
        assert_eq!(s.strict(true), Some(false));

        // AY 3ms vs z3 1ms: slower but under the 10ms floor -> not a blocker.
        let mut s2 = DivStats::default();
        s2.add(&rec(
            v(&[Unsat]),
            3,
            Some(v(&[Unsat])),
            1,
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        assert_eq!(s2.slower, 0);
        assert_eq!(s2.strict(true), Some(true));
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
        assert_eq!(s.strict(false), None);
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
            ay_rss(v(&[Unsat]), 40, Some(MB)),
            Some(ay_rss(v(&[Unsat]), 50, Some(2 * MB))),
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        assert_eq!(s.wall_losses, 0);
        assert_eq!(s.wall_not_2x, 1);
        assert_eq!(s.rating(true), Rating::Par);
        assert_eq!(s.rating_cell(true), "PAR(x1,m0)");
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
        assert_eq!(s.rating_cell(true), "PAR(x0,m1)");
    }

    #[test]
    fn rating_par_when_rss_evidence_is_missing() {
        use Verdict::*;
        // The wall bar alone cannot establish SUPERIOR. This is the normal
        // shape on non-Unix hosts and can also arise from a failed per-child
        // rusage measurement: missing evidence must not become vacuous success.
        let mut s = DivStats::default();
        s.add(&rec_out(
            ay_rss(v(&[Unsat]), 20, None),
            Some(ay_rss(v(&[Unsat]), 50, Some(20 * MB))),
            SelfCheck::Verdicts(vec![Unsat]),
        ));
        assert_eq!(s.wall_not_2x, 0);
        assert_eq!(s.rss_cmp, 0);
        assert_eq!(s.rss_missing, 1);
        assert_eq!(s.rss_not_80, 1);
        assert_eq!(s.rating(true), Rating::Par);
        assert_eq!(s.rating_cell(true), "PAR(x0,m1)");
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
