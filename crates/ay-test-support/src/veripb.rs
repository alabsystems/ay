// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The ONE VeriPB checker resolver and verdict-asserting gate used by every
//! checker-backed test in this workspace.
//!
//! Why this module exists: before it, six independent copies of "find veripb"
//! each ended in `return` when the checker was missing, and the two most-used
//! gates asserted only `ExitStatus::success()`. The result was a suite that
//! reported green in 0.00s having checked nothing, and that `/usr/bin/true`
//! could satisfy end to end. Both failure modes are structurally impossible
//! here:
//!
//! * [`require_checker`] PANICS when no checker can be found, unless the
//!   caller's environment explicitly opts out via `AY_VERIPB_OPTIONAL`. Even
//!   then the opt-out is announced on stderr with a uniform, greppable marker
//!   ([`SKIP_MARKER`]) — libtest captures the stderr of passing tests, so run
//!   with `--nocapture` to see it. The default (unset) behaviour is a loud
//!   failure, which is what makes the announcement a belt-and-braces detail
//!   rather than the only signal.
//! * Resolution runs a SELF-TEST against the resolved binary: six probes it
//!   must answer the way a proof checker answers them. A binary that fails the
//!   self-test is a hard error that `AY_VERIPB_OPTIONAL` does NOT excuse —
//!   pointing `VERIPB_BIN` at `/usr/bin/true` fails loudly instead of silently
//!   passing every gate.
//! * Gates assert on the checker's own verdict LINE (`s VERIFIED ...`) AND on
//!   its exit code, because neither alone is sufficient:
//!   - exit code alone is not a gate: VeriPB exits 0 while printing
//!     `s VERIFIED NO CONCLUSION` for a proof that concludes nothing, and
//!     `/usr/bin/true` exits 0 having done nothing at all;
//!   - the verdict line alone is not a gate either: a checker can print a
//!     correct verdict and then exit 1 (killed, crashed, failed after
//!     printing), in which case the line is no longer evidence that the run
//!     completed. That was the THIRD fake this module did not catch, and
//!     `ci/fake-checkers/verdict-then-exit1.sh` is it.
//!   Acceptance therefore means: exit code 0 AND an `s VERIFIED <conclusion>`
//!   line whose conclusion is real. Anything else is a rejection. Fail closed.
//!
//! The shell gates enforce the identical contract, including the identical
//! self-test battery, from `scripts/lib/veripb_verdict.sh`. Both are exercised
//! against the same five committed fakes (`ci/fake-checkers/`), so a binary
//! cannot pass one surface by failing the other.

use std::fmt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::OnceLock;

/// Set to a non-empty value other than `0` to allow a checker-backed suite to
/// report SKIPPED instead of failing when no VeriPB checker is installed.
pub const OPT_OUT_ENV: &str = "AY_VERIPB_OPTIONAL";

/// Environment overrides consulted first, in order.
pub const CHECKER_ENV_VARS: [&str; 3] = ["VERIPB_BIN", "AY_PB26_VERIPB_BIN", "VERIPB"];

/// Uniform stderr marker for an announced (opted-out) checker skip.
pub const SKIP_MARKER: &str = "AY-VERIPB-SKIP";

/// Formula-format flags VeriPB understands. If a caller passes one of these,
/// [`run`] does not add its own `--opb`.
const FORMAT_FLAGS: [&str; 3] = ["--opb", "--cnf", "--wcnf"];

const VERDICT_PREFIX: &str = "s ";
const VERIFIED_STATUS: &str = "VERIFIED";
/// VeriPB's verdict when deletions were not checked (`-u`): the conclusion
/// holds only relative to a proof whose deletion steps were trusted.
const WEAKENED_STATUS: &str = "UNDER WEAKENED GUARANTEES";
const NO_CONCLUSION: &str = "NO CONCLUSION";

/// Colon-separated list of candidate checker paths that REPLACES the built-in
/// known build locations. Set it to a nonexistent path to model a machine with
/// no checker installed (which is how the fail-loudly behaviour is tested).
pub const SEARCH_PATH_ENV: &str = "AY_VERIPB_SEARCH_PATH";

/// Relative path, under the shared cache root, of the PRE-PIN cache layout: a
/// bare clone directory whose name carries NO checker identity.
///
/// It is named here only so it can be RECOGNISED and reported — never resolved.
/// See [`known_build_locations`].
pub const PRE_PIN_CACHE_REL: &str = "VeriPB/target/release/veripb";

/// The shared checker cache root (`$XDG_CACHE_HOME`, else `$HOME/.cache`), if
/// this environment names one.
fn cache_root() -> Option<PathBuf> {
    std::env::var_os("XDG_CACHE_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".cache")))
        .map(|cache| cache.join("ay-veripb"))
}

/// The pre-pin cache path, when a binary is actually sitting at it.
///
/// Resolution IGNORES it (see [`known_build_locations`]); [`ResolveError`]
/// names it so "no checker found" cannot be mistaken for "no checker built"
/// when an unpinnable one is present.
fn stale_pre_pin_build() -> Option<PathBuf> {
    let candidate = cache_root()?.join(PRE_PIN_CACHE_REL);
    candidate.is_file().then_some(candidate)
}

/// The NEUTRAL default candidate. `publish/DECISIONS.md` (2026-07-18 scrub log)
/// kept it deliberately when the maintainer's personal path was dropped: it is
/// machine-independent, so it can survive into a public snapshot.
///
/// Neutrality is not identity. Nothing in this repo builds it, no script writes
/// it, and its name records no commit and no patch — a binary there could be any
/// checker at all. It is kept (the publishing decision stands) but it is now
/// RANKED BELOW the identity-bearing pinned builds, and, like every other
/// identity-free source, it only becomes evidence by passing [`soundness_gate`].
pub const NEUTRAL_DEFAULT: &str = "/tmp/veripb-3/bin/veripb";

/// Placeholder occupying the `$PATH` slot in the searched list when `$PATH`
/// holds no `veripb`. `is_file()` is false for it, so it is never resolved; it
/// exists so the "searched, in order:" message keeps naming that slot IN ITS
/// REAL POSITION — which is the only reason a reader can tell the order changed.
const PATH_SLOT: &str = "$PATH/veripb";

/// The search order below the environment overrides, as a pure function of the
/// three environment facts it depends on, so the RANKING is testable without
/// `set_var` (process-global and racy under a threaded runner). The injection
/// idiom accepts an explicit environment reader so tests do not mutate process state.
/// Production AY uses its integrated checker; this resolver is for independent
/// reference checks and developer tools.
fn search_order(
    cache: Option<&Path>,
    path_hit: Option<PathBuf>,
    home: Option<&Path>,
) -> Vec<PathBuf> {
    let mut candidates = Vec::new();
    if let Some(cache) = cache {
        candidates.extend(pinned_cache_candidates(cache));
    }
    candidates.push(path_hit.unwrap_or_else(|| PathBuf::from(PATH_SLOT)));
    candidates.push(PathBuf::from(NEUTRAL_DEFAULT));
    if let Some(home) = home {
        candidates.push(home.join(".cargo/bin/veripb"));
    }
    candidates
}

/// Known local build locations, in RANK ORDER, tried after the environment
/// overrides.
///
/// THE RANKING (changed 2026-09-22, the totality half of the identity fix):
///
/// ```text
///   1. <cache>/<pinned-id>[-rustc<fp>]/target/release/veripb   identity-bearing
///   2. $PATH/veripb                                            ambient
///   3. /tmp/veripb-3/bin/veripb                                neutral default
///   4. $HOME/.cargo/bin/veripb                                 ambient
/// ```
///
/// Rows 2-4 carry NO identity, and rows 2 and 3 used to outrank row 1 — `$PATH`
/// because [`locate`] scanned it before consulting this list at all, and
/// `/tmp/veripb-3` because it was the first element here. So on a machine with
/// both, an unidentifiable checker beat the pinned build that the repo's own
/// scripts had built. Removing the LAST-ranked identity-free candidate while
/// leaving the FIRST-ranked ones is not a fix; this is the rest of it.
///
/// Rank is now: explicitly named (the [`CHECKER_ENV_VARS`] overrides, handled in
/// [`locate`]) > pinned identity > ambient. Nothing here is trusted on its rank:
/// whichever candidate wins still has to pass [`self_test`] AND
/// [`soundness_gate`] in [`vet`] before any suite sees it.
///
/// EVERY cache path offered here carries the checker's IDENTITY in its
/// directory name — the pinned upstream commit plus the reviewed patch's
/// sha-256 prefix ([`pinned_build_id`]), keyed or legacy-unkeyed
/// ([`is_pinned_cache_dir`]). That is the whole contract with the builders
/// (`scripts/cert_ci.sh`, `scripts/ci/pb_certified_gate.sh`), which clone the
/// pinned commit, apply the pinned patch, and build at exactly such a path.
///
/// WHAT WAS REMOVED, AND WHY IT WAS NOT COMPATIBILITY. This list used to end
/// with `<cache>/VeriPB/target/release/veripb`, described as "the original
/// pre-pin cache layout populated by an early `scripts/cert_ci.sh`". That
/// description is the argument against it: the early script `git clone
/// --depth 1`d the upstream DEFAULT BRANCH and built whatever it got, so a
/// binary at that path is by construction UNPINNED and UNPATCHED — precisely
/// the checker the pin exists to exclude. Nothing writes that path any more,
/// its name records no commit and no patch, so no amount of it being "first
/// come" makes it identifiable.
///
/// MEASURED 2026-09-22 on this workstation: with the pinned patch re-cut (pin
/// sha `11d772ad…`) no keyed directory matched any more, resolution fell
/// through to that path, and the clean upstream checkout sitting there —
/// `git rev-parse HEAD` == the pinned commit, tree CLEAN, i.e. the patch never
/// applied — was handed to every checker-backed suite in the workspace. It
/// reports the pinned version, so `pin::check_version` passed it; it then
/// ACCEPTED all 22 committed wrong-verdict fixtures. Every "and VeriPB said
/// VERIFIED" in the workspace was, that day, a statement about a checker with
/// 21 known wrong-verdict defects.
///
/// A stale build there is therefore not resolved, and not silently skipped
/// either: [`ResolveError::NotFound`] names it as IGNORED, with the pinned
/// build id to rebuild at.
fn known_build_locations() -> Vec<PathBuf> {
    if let Some(raw) = std::env::var_os(SEARCH_PATH_ENV) {
        return std::env::split_paths(&raw).collect();
    }
    let cache = cache_root();
    let home = std::env::var_os("HOME").map(PathBuf::from);
    search_order(cache.as_deref(), path_lookup(), home.as_deref())
}

/// Cache-key contract shared with `scripts/lib/veripb_build_id.sh` (the ONE
/// shell-side authority, sourced by both `scripts/ci/pb_certified_gate.sh` and
/// `scripts/cert_ci.sh`) and with `crates/ay/src/maxsat_cert.rs`.
///
/// This is the checker's IDENTITY: the pinned upstream commit plus the first
/// twelve hex digits of the reviewed patch's SHA-256, so a changed patch must
/// not silently reuse a binary built from the same upstream commit. It is both
/// the whole name of a legacy (pre-2026-08-30) cache directory and the prefix
/// of a keyed one — the shell side appends [`RUSTC_KEY_INFIX`] plus a compiler
/// fingerprint when it BUILDS, because compiling twice in one target dir with
/// two compilers breaks (E0514, commit 8499748c6). This resolver never builds,
/// and a finished binary runs the same under any of today's compilers, so
/// resolution accepts every directory matching the identity — keyed or legacy
/// — and the self-test plus version cross-check re-verify whichever is picked.
/// The agreement with the shell format is pinned by an EXECUTABLE test below
/// (`shell_and_rust_agree_on_the_cache_key`), not by convention.
#[must_use]
pub fn pinned_build_id() -> String {
    let patch_sha = pin::patch_sha256();
    let patch_prefix = patch_sha.get(..12).unwrap_or(patch_sha);
    format!("{}-{patch_prefix}", pin::commit())
}

/// Separator between the identity prefix and the compiler fingerprint in a
/// keyed cache-directory name. Must match the `printf` format in
/// `scripts/lib/veripb_build_id.sh::veripb_build_id` (pinned by test).
pub const RUSTC_KEY_INFIX: &str = "-rustc";

/// Whether a `~/.cache/ay-veripb` entry name denotes a build of the pinned
/// checker: exactly the identity (legacy layout) or the identity plus a
/// compiler fingerprint (keyed layout).
#[must_use]
pub fn is_pinned_cache_dir(name: &str, pinned_id: &str) -> bool {
    name == pinned_id
        || name
            .strip_prefix(pinned_id)
            .is_some_and(|rest| rest.starts_with(RUSTC_KEY_INFIX))
}

/// Candidate checker binaries under the shared build cache, keyed builds
/// before the legacy unkeyed one and lexically-later fingerprints first (the
/// order is about determinism, not preference: every match is the same pinned
/// source, and behaviour is re-proved on whichever binary wins). When nothing
/// matching exists the legacy path is still named, so a "searched:" error
/// message points at where a build would land.
fn pinned_cache_candidates(cache: &Path) -> Vec<PathBuf> {
    let pinned_id = pinned_build_id();
    let mut names: Vec<String> = std::fs::read_dir(cache)
        .map(|entries| {
            entries
                .filter_map(Result::ok)
                .filter_map(|entry| entry.file_name().into_string().ok())
                .filter(|name| is_pinned_cache_dir(name, &pinned_id))
                .collect()
        })
        .unwrap_or_default();
    names.sort_by(|a, b| b.cmp(a));
    if names.is_empty() {
        names.push(pinned_id);
    }
    names
        .iter()
        .map(|name| cache.join(name).join("target/release/veripb"))
        .collect()
}

// `pinned_cache_checker()` lived here from 7b961aad9 until this commit: a
// public "first existing identity-bearing cache build" for the suites that roll
// their own probe. It was right about the CACHE and wrong about the shape of
// the problem — it hands back a path with nothing asked of the binary, and its
// three callers each still consulted `$VERIPB_BIN` and `$PATH` first, ungated,
// before ever reaching it. Those callers now use `optional_checker`, which goes
// through the one resolver and its two batteries, so an accessor that returns
// an UNVETTED checker path has no caller and no business being public.

fn path_lookup() -> Option<PathBuf> {
    let executable = format!("veripb{}", std::env::consts::EXE_SUFFIX);
    std::env::var_os("PATH").and_then(|paths| {
        std::env::split_paths(&paths)
            .map(|directory| directory.join(&executable))
            .find(|candidate| candidate.is_file())
    })
}

/// Why no usable checker is available.
#[derive(Clone, Debug)]
pub enum ResolveError {
    /// An environment override was set but does not name an existing file.
    BadOverride { var: &'static str, value: PathBuf },
    /// Nothing was found in any searched location.
    NotFound {
        searched: Vec<String>,
        /// [`pinned_build_id`] — the cache directory name a build must land at
        /// for this resolver to accept it.
        pinned_id: String,
        /// A binary sitting at the identity-free PRE-PIN cache path, if one is
        /// there. It is NOT a candidate; it is reported so that "no checker
        /// found" on a machine that visibly has a `veripb` binary is explained
        /// rather than merely asserted.
        ignored_pre_pin: Option<PathBuf>,
    },
    /// A binary was found but does not behave like a VeriPB checker.
    SelfTestFailed { checker: PathBuf, detail: String },
    /// A binary was found, behaves like a checker, and gives WRONG VERDICTS on
    /// the committed fixtures. The worst case there is: it looks like evidence.
    Unsound { checker: PathBuf, detail: String },
}

impl fmt::Display for ResolveError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BadOverride { var, value } => write!(
                formatter,
                "{var} is set to `{}`, which is not an existing file. \
                 Unset it or point it at a VeriPB checker binary.",
                value.display()
            ),
            Self::NotFound {
                searched,
                pinned_id,
                ignored_pre_pin,
            } => {
                write!(
                    formatter,
                    "no VeriPB checker found. Searched, in order: {}. \
                     Build the pinned checker (`scripts/cert_ci.sh` or \
                     `scripts/ci/pb_certified_gate.sh`, which clone {}, apply {} and \
                     build into a cache directory named `{pinned_id}[-rustc<fingerprint>]`), \
                     or set VERIPB_BIN.",
                    searched.join(", "),
                    pin::commit(),
                    pin::patch(),
                )?;
                if let Some(stale) = ignored_pre_pin {
                    write!(
                        formatter,
                        "\nIGNORED: `{}` exists but is the PRE-PIN cache layout — its name \
                         records no commit and no patch, and the early script that wrote it \
                         built the upstream default branch UNPATCHED. A verdict from it is \
                         not evidence (published 3.0.2 accepts all 22 committed \
                         wrong-verdict fixtures), so it is not resolved. Rebuild at the \
                         pinned path instead of pointing VERIPB_BIN at it.",
                        stale.display()
                    )?;
                }
                Ok(())
            }
            Self::SelfTestFailed { checker, detail } => write!(
                formatter,
                "`{}` was resolved as the VeriPB checker but failed its self-test \
                 (a real checker must verify a known-good proof and reject a known-bad one): {detail}",
                checker.display()
            ),
            Self::Unsound { checker, detail } => write!(
                formatter,
                "`{}` was resolved as the VeriPB checker, behaves like one, and is NOT a \
                 SOUND one: {detail}\n\
                 A verdict from it is not evidence of anything. This is the gate the \
                 version string cannot be: published VeriPB 3.0.2 reports the pinned \
                 `{}` and still contradicts the truth on these fixtures. Build the pinned \
                 checker (`scripts/cert_ci.sh` or `scripts/ci/pb_certified_gate.sh`: clone \
                 {}, apply {}) instead of pointing this resolver at an unpatched one.",
                checker.display(),
                pin::version(),
                pin::commit(),
                pin::patch(),
            ),
        }
    }
}

/// Locate a checker without vetting it.
///
/// Order: `VERIPB_BIN`, `AY_PB26_VERIPB_BIN`, `VERIPB`, then
/// [`known_build_locations`] — whose first entries are the identity-bearing
/// pinned cache builds, and which now owns the `$PATH` slot too (this function
/// used to scan `$PATH` before consulting that list at all, so an ambient
/// checker outranked the pinned one, and [`SEARCH_PATH_ENV`] could not in fact
/// "model a machine with no checker installed" on a box that had one on
/// `$PATH`, though its doc says that is what it is for).
///
/// An environment override that does not name an existing file is an ERROR, not
/// a reason to fall through — a typo in `VERIPB_BIN` must never silently
/// degrade to "checker absent".
///
/// NOTHING here establishes that the binary found is a checker, let alone a
/// SOUND one. That is [`vet`]'s job, and every caller outside this module goes
/// through it.
pub fn locate() -> Result<PathBuf, ResolveError> {
    let mut searched = Vec::new();
    for var in CHECKER_ENV_VARS {
        if let Some(raw) = std::env::var_os(var) {
            if raw.is_empty() {
                continue;
            }
            let candidate = PathBuf::from(raw);
            if candidate.is_file() {
                return Ok(candidate);
            }
            return Err(ResolveError::BadOverride {
                var,
                value: candidate,
            });
        }
        searched.push(format!("${var}"));
    }
    for candidate in known_build_locations() {
        searched.push(candidate.display().to_string());
        if candidate.is_file() {
            return Ok(candidate);
        }
    }
    Err(ResolveError::NotFound {
        searched,
        pinned_id: pinned_build_id(),
        ignored_pre_pin: stale_pre_pin_build(),
    })
}

fn unique_temp_dir(label: &str) -> PathBuf {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let serial = COUNTER.fetch_add(1, Ordering::Relaxed);
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|elapsed| elapsed.as_nanos())
        .unwrap_or(0);
    std::env::temp_dir().join(format!(
        "ay-veripb-{label}-{}-{serial}-{nanos}",
        std::process::id()
    ))
}

/// Raw result of one checker invocation.
#[derive(Clone, Debug)]
pub struct CheckerRun {
    checker: PathBuf,
    args: Vec<String>,
    exit_code: Option<i32>,
    stdout: String,
    stderr: String,
}

impl CheckerRun {
    pub fn stdout(&self) -> &str {
        &self.stdout
    }

    pub fn stderr(&self) -> &str {
        &self.stderr
    }

    pub fn exit_code(&self) -> Option<i32> {
        self.exit_code
    }

    /// The checker's own `s ...` verdict line, if it printed one.
    pub fn verdict(&self) -> Option<&str> {
        self.stdout
            .lines()
            .map(str::trim_end)
            .find(|line| line.starts_with(VERDICT_PREFIX))
    }

    /// The verdict line, or a stable placeholder when the checker printed none.
    pub fn verdict_or_placeholder(&self) -> &str {
        self.verdict().unwrap_or("<no `s ...` verdict line>")
    }

    /// Split the verdict line into its guarantee level and its conclusion text.
    pub fn parsed_verdict(&self) -> Option<(Guarantee, &str)> {
        let body = self.verdict()?.strip_prefix(VERDICT_PREFIX)?;
        if let Some(conclusion) = body.strip_prefix(VERIFIED_STATUS) {
            return Some((Guarantee::Verified, conclusion.trim()));
        }
        if let Some(conclusion) = body.strip_prefix(WEAKENED_STATUS) {
            return Some((Guarantee::Weakened, conclusion.trim()));
        }
        None
    }

    /// True when the checker ran to completion successfully.
    ///
    /// Not a gate by itself — `/usr/bin/true` satisfies it, and so does VeriPB
    /// printing `s VERIFIED NO CONCLUSION` — but a NECESSARY condition for
    /// acceptance. VeriPB exits non-zero whenever it refuses a proof, so a
    /// non-zero exit standing next to an accepting-looking verdict line means
    /// the run cannot be trusted: the process did not finish the way a
    /// successful check finishes.
    pub fn exit_ok(&self) -> bool {
        self.exit_code == Some(0)
    }

    /// True when the checker accepted the proof with a real conclusion under
    /// FULL guarantees. `s VERIFIED NO CONCLUSION` is NOT a pass (the proof
    /// concluded nothing), `s UNDER WEAKENED GUARANTEES ...` is not either, and
    /// neither is a correct-looking verdict from a run that exited non-zero.
    pub fn is_verified(&self) -> bool {
        self.is_accepted_at(Guarantee::Verified)
    }

    /// True when the checker accepted the proof at `guarantee` or stronger.
    ///
    /// Requires BOTH halves of the contract: a clean exit and a verdict line
    /// carrying a real conclusion at a sufficient guarantee level.
    pub fn is_accepted_at(&self, guarantee: Guarantee) -> bool {
        if !self.exit_ok() {
            return false;
        }
        match self.parsed_verdict() {
            Some((observed, conclusion)) => {
                conclusion != NO_CONCLUSION
                    && !conclusion.is_empty()
                    && observed.is_at_least(guarantee)
            }
            None => false,
        }
    }

    /// True when the checker refused the proof: it produced no accepting
    /// verdict at any guarantee level.
    pub fn is_rejected(&self) -> bool {
        !self.is_accepted_at(Guarantee::Weakened)
    }

    fn report(&self, context: &str) -> String {
        format!(
            "{context}\n  checker: {} {}\n  verdict: {}\n  exit: {:?}\n  stdout:\n{}\n  stderr:\n{}",
            self.checker.display(),
            self.args.join(" "),
            self.verdict_or_placeholder(),
            self.exit_code,
            self.stdout,
            self.stderr
        )
    }

    /// Assert the checker verified the proof with the expected conclusion.
    ///
    /// This asserts on the VERDICT TEXT. Exit status is reported for
    /// diagnostics only and is never the gate.
    pub fn assert_verified(&self, expect: &Expect, context: &str) {
        assert!(
            self.is_accepted_at(expect.guarantee),
            "{}",
            self.report(&format!(
                "{context}: VeriPB did not accept the proof at the required guarantee \
                 (expected {expect})"
            ))
        );
        let (_, conclusion) = self.parsed_verdict().unwrap_or((Guarantee::Verified, ""));
        assert!(
            expect.conclusion.matches(conclusion),
            "{}",
            self.report(&format!(
                "{context}: VeriPB confirmed a DIFFERENT conclusion than the one under test \
                 (expected {expect})"
            ))
        );
    }

    /// Assert the checker refused the proof. Only meaningful because the
    /// resolved binary has passed [`self_test`]; a no-op binary can never reach
    /// this call site.
    pub fn assert_rejected(&self, context: &str) {
        assert!(
            self.is_rejected(),
            "{}",
            self.report(&format!(
                "{context}: VeriPB accepted a proof that MUST be rejected"
            ))
        );
    }
}

/// How strong the checker's acceptance is.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Guarantee {
    /// `s VERIFIED ...` — every step, including deletions, was checked.
    Verified,
    /// `s UNDER WEAKENED GUARANTEES ...` — the run trusted deletion steps
    /// (`veripb -u`). Strictly weaker; a test must ask for it explicitly.
    Weakened,
}

impl Guarantee {
    fn is_at_least(self, required: Self) -> bool {
        matches!(
            (self, required),
            (Self::Verified, _) | (Self::Weakened, Self::Weakened)
        )
    }

    fn status(self) -> &'static str {
        match self {
            Self::Verified => VERIFIED_STATUS,
            Self::Weakened => WEAKENED_STATUS,
        }
    }
}

/// The conclusion text a gate requires the checker to confirm.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Conclusion {
    /// Any genuine conclusion (anything except `NO CONCLUSION`).
    Any,
    Unsatisfiable,
    Satisfiable,
    /// `conclusion BOUNDS <lower> <upper>` as the checker restates it:
    /// `BOUNDS <lower> <= obj <= <upper>`.
    Bounds {
        lower: String,
        upper: String,
    },
}

impl Conclusion {
    fn matches(&self, conclusion: &str) -> bool {
        match self {
            Self::Any => conclusion != NO_CONCLUSION && !conclusion.is_empty(),
            Self::Unsatisfiable => conclusion == "UNSATISFIABLE",
            Self::Satisfiable => conclusion == "SATISFIABLE",
            Self::Bounds { lower, upper } => {
                let Some(rest) = conclusion.strip_prefix("BOUNDS ") else {
                    return false;
                };
                let fields: Vec<&str> = rest.split_whitespace().collect();
                // `<lower> <= obj <= <upper>`
                fields.len() == 5
                    && fields[0] == lower
                    && fields[1] == "<="
                    && fields[3] == "<="
                    && fields[4] == upper
            }
        }
    }
}

impl fmt::Display for Conclusion {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Any => formatter.write_str("<any real conclusion>"),
            Self::Unsatisfiable => formatter.write_str("UNSATISFIABLE"),
            Self::Satisfiable => formatter.write_str("SATISFIABLE"),
            Self::Bounds { lower, upper } => {
                write!(formatter, "BOUNDS {lower} <= obj <= {upper}")
            }
        }
    }
}

/// The exact verdict a gate requires: a guarantee level plus a conclusion.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Expect {
    pub guarantee: Guarantee,
    pub conclusion: Conclusion,
}

impl Expect {
    /// Fully checked `s VERIFIED UNSATISFIABLE`.
    pub const UNSAT: Self = Self {
        guarantee: Guarantee::Verified,
        conclusion: Conclusion::Unsatisfiable,
    };

    /// Fully checked `s VERIFIED SATISFIABLE`.
    pub const SAT: Self = Self {
        guarantee: Guarantee::Verified,
        conclusion: Conclusion::Satisfiable,
    };

    /// Fully checked, any real conclusion.
    pub const ANY: Self = Self {
        guarantee: Guarantee::Verified,
        conclusion: Conclusion::Any,
    };

    pub fn bounds(lower: impl Into<String>, upper: impl Into<String>) -> Self {
        Self {
            guarantee: Guarantee::Verified,
            conclusion: Conclusion::Bounds {
                lower: lower.into(),
                upper: upper.into(),
            },
        }
    }

    /// Accept the weaker `s UNDER WEAKENED GUARANTEES ...` verdict that
    /// `veripb -u` produces. Callers must say this out loud; it is never the
    /// default.
    #[must_use]
    pub fn under_weakened_guarantees(mut self) -> Self {
        self.guarantee = Guarantee::Weakened;
        self
    }
}

impl fmt::Display for Expect {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "s {} {} (or stronger)",
            self.guarantee.status(),
            self.conclusion
        )
    }
}

/// Run the checker over an on-disk formula/proof pair.
///
/// `extra_args` are placed before the two paths (for example `["-u"]` for
/// unchecked-deletion mode). `--opb` is added unless the caller already named a
/// formula format: every formula AY emits or certifies against is OPB, and
/// letting the checker guess by extension has bitten this suite before. The
/// escape hatch exists for the checker-soundness fixtures, one of which is a
/// DIMACS CNF; passing two format flags would leave which one wins up to the
/// argument parser.
pub fn run(checker: &Path, formula: &Path, proof: &Path, extra_args: &[&str]) -> CheckerRun {
    let mut args: Vec<String> = extra_args.iter().map(|arg| (*arg).to_string()).collect();
    if !args.iter().any(|arg| FORMAT_FLAGS.contains(&arg.as_str())) {
        args.push(String::from("--opb"));
    }
    args.push(formula.display().to_string());
    args.push(proof.display().to_string());

    let output = Command::new(checker)
        .args(&args)
        .output()
        .unwrap_or_else(|error| {
            panic!(
                "failed to execute the VeriPB checker `{}`: {error}",
                checker.display()
            )
        });

    CheckerRun {
        checker: checker.to_path_buf(),
        args,
        exit_code: output.status.code(),
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
    }
}

/// Run the checker over in-memory formula/proof text.
pub fn run_text(
    checker: &Path,
    label: &str,
    formula: &str,
    proof: &str,
    extra_args: &[&str],
) -> CheckerRun {
    let directory = unique_temp_dir(label);
    std::fs::create_dir_all(&directory).expect("create VeriPB scratch directory");
    let formula_path = directory.join("instance.opb");
    let proof_path = directory.join("proof.pbp");
    std::fs::write(&formula_path, formula).expect("write VeriPB scratch formula");
    std::fs::write(&proof_path, proof).expect("write VeriPB scratch proof");
    let run = run(checker, &formula_path, &proof_path, extra_args);
    let _ = std::fs::remove_dir_all(&directory);
    run
}

// ---------------------------------------------------------- probe fixtures
//
// PUBLIC BECAUSE THEY MUST NOT BE RE-INVENTED. This crate is a DEV-dependency
// everywhere, so a production module that has to self-test a checker before
// trusting it — `ay_pb_core::veripb_runner::self_test`, which runs its probes
// through its own `verify_unsat` rather than through this module's `run` —
// cannot call [`self_test`] and must hold the probe text itself. Exporting the
// bytes here keeps that a COPY OF ONE FIXTURE SET rather than a second,
// divergent battery: `veripb_runner`'s unit tests assert its constants are
// byte-identical to these, so a change on either side turns the other red.
//
// `scripts/lib/veripb_verdict.sh` carries the same text a third time (it must:
// a POSIX shell gate cannot link Rust). That copy is pinned by
// `crates/ay-pb-core/src/veripb_runner.rs`'s `self_test_fixtures_match_the_shell_battery`.

/// An unsatisfiable formula: `x1 >= 1` and `-x1 >= 0`.
pub const SELF_TEST_UNSAT_OPB: &str = "* #variable= 1 #constraint= 2\n+1 x1 >= 1 ;\n-1 x1 >= 0 ;\n";
/// A valid refutation of it.
pub const SELF_TEST_GOOD_UNSAT_PBP: &str = "pseudo-Boolean proof version 3.0\nf 2 ;\npol 1 2 +;\nrup >= 1 ;\noutput NONE;\nconclusion UNSAT : 4;\nend pseudo-Boolean proof;\n";
/// A well-formed proof over the same formula that derives and concludes NOTHING.
/// Real VeriPB answers `s VERIFIED NO CONCLUSION` and exits 0.
pub const SELF_TEST_NO_CONCLUSION_PBP: &str = "pseudo-Boolean proof version 3.0\nf 2 ;\noutput NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\n";
/// A SATISFIABLE formula: `x1 + x2 >= 1`.
pub const SELF_TEST_SAT_OPB: &str = "* #variable= 2 #constraint= 1\n+1 x1 +1 x2 >= 1 ;\n";
/// A genuine solution of it.
pub const SELF_TEST_GOOD_SAT_PBP: &str = "pseudo-Boolean proof version 3.0\nf 1 ;\noutput NONE;\nconclusion SAT : x1 ~x2;\nend pseudo-Boolean proof;\n";
/// A LIE about it: claims UNSAT, citing a satisfiable input row as the
/// contradiction.
pub const SELF_TEST_FALSE_UNSAT_PBP: &str = "pseudo-Boolean proof version 3.0\nf 1 ;\noutput NONE;\nconclusion UNSAT : 1;\nend pseudo-Boolean proof;\n";
/// A different LIE about it: claims SAT with an assignment that FALSIFIES the
/// only constraint. Structurally identical to a true SAT certificate, so a
/// checker that merely restates the proof's own claim cannot tell them apart.
pub const SELF_TEST_FALSE_SAT_PBP: &str = "pseudo-Boolean proof version 3.0\nf 1 ;\noutput NONE;\nconclusion SAT : ~x1 ~x2;\nend pseudo-Boolean proof;\n";
/// Not a proof at all.
pub const SELF_TEST_GARBAGE_PBP: &str = "this file is not a pseudo-Boolean proof\n";

/// Prove that `checker` really is a proof checker.
///
/// Six probes. Each of the five fakes committed under `ci/fake-checkers/`
/// passes some of them; none passes all six:
///
/// | probe | requirement | catches |
/// | --- | --- | --- |
/// | `good-unsat` | verify a valid refutation, exit 0 | `/usr/bin/true`, `/usr/bin/false`, `silent-exit0.sh`, `verdict-then-exit1.sh` (right verdict, exit 1), and `comment-verified.sh` (refuses on the verdict line while a `c` comment says otherwise) |
/// | `good-sat` | verify a valid solution, exit 0 | `always-unsat.sh` and anything else printing one fixed verdict |
/// | `false-unsat` | reject a proof claiming UNSAT for a satisfiable formula | `always-unsat.sh`, `parrot.sh` |
/// | `false-sat` | reject a proof claiming SAT with a falsifying assignment | `parrot.sh` — this is the probe that a checker which just restates the proof's own conclusion cannot survive |
/// | `garbage` | reject a file that is not a proof | `parrot.sh`, rubber stamps |
/// | `no-conclusion` | not treat `NO CONCLUSION` as acceptance | the gate itself: this is the exact verdict that satisfied `case $v in "s VERIFIED"*)` |
///
/// This is what makes every downstream gate — including the ones that assert a
/// proof must be REJECTED — non-vacuous.
///
/// # Errors
/// Returns a description of the first failed probe, naming the verdict and exit
/// code observed. Callers must treat that as fatal: a verdict from a binary
/// that fails this battery is not evidence of anything.
pub fn self_test(checker: &Path) -> Result<(), String> {
    let describe = |run: &CheckerRun| {
        format!(
            "verdict: {}; exit: {:?}; stdout: {}; stderr: {}",
            run.verdict_or_placeholder(),
            run.exit_code(),
            run.stdout().trim(),
            run.stderr().trim()
        )
    };

    let must_verify = |label: &str, opb: &str, pbp: &str, conclusion: &str| {
        let run = run_text(checker, label, opb, pbp, &[]);
        let ok = run.is_verified()
            && run
                .parsed_verdict()
                .is_some_and(|(_, seen)| seen == conclusion);
        if ok {
            Ok(())
        } else {
            Err(format!(
                "probe `{label}`: it did not answer `s VERIFIED {conclusion}` with exit 0 ({})",
                describe(&run)
            ))
        }
    };

    let must_reject = |label: &str, opb: &str, pbp: &str, why: &str| {
        let run = run_text(checker, label, opb, pbp, &[]);
        if run.is_rejected() {
            Ok(())
        } else {
            Err(format!(
                "probe `{label}`: it ACCEPTED {why} ({}); it cannot be a sound checker",
                describe(&run)
            ))
        }
    };

    must_verify(
        "selftest-good-unsat",
        SELF_TEST_UNSAT_OPB,
        SELF_TEST_GOOD_UNSAT_PBP,
        "UNSATISFIABLE",
    )?;
    must_verify(
        "selftest-good-sat",
        SELF_TEST_SAT_OPB,
        SELF_TEST_GOOD_SAT_PBP,
        "SATISFIABLE",
    )?;
    must_reject(
        "selftest-false-unsat",
        SELF_TEST_SAT_OPB,
        SELF_TEST_FALSE_UNSAT_PBP,
        "a proof claiming UNSAT for a SATISFIABLE formula",
    )?;
    must_reject(
        "selftest-false-sat",
        SELF_TEST_SAT_OPB,
        SELF_TEST_FALSE_SAT_PBP,
        "a proof claiming SAT with an assignment that falsifies the formula",
    )?;
    must_reject(
        "selftest-garbage",
        SELF_TEST_UNSAT_OPB,
        SELF_TEST_GARBAGE_PBP,
        "a file that is not a proof at all",
    )?;
    must_reject(
        "selftest-no-conclusion",
        SELF_TEST_UNSAT_OPB,
        SELF_TEST_NO_CONCLUSION_PBP,
        "a proof that concludes nothing as though it concluded something",
    )?;
    Ok(())
}

/// The BEHAVIOURAL half of the pin: every committed wrong-verdict fixture, run
/// against `checker`, all of which it must REFUSE.
///
/// # Why resolution and not just one gate test
///
/// [`self_test`] proves the binary is a checker. It does NOT prove it is a
/// CORRECT one, and that is not a gap in the probes — it is the measured fact
/// this module exists around: published VeriPB 3.0.2 passes all six self-test
/// probes, reports the pinned version string, and answers `s VERIFIED
/// UNSATISFIABLE` for satisfiable formulas. On 2026-09-22 exactly that binary
/// became the checker behind every "and VeriPB said VERIFIED" in this
/// workspace.
///
/// Identity closed that hole for ONE source — the cache — by refusing paths
/// whose directory name records no commit and no patch. But a directory name is
/// a convention, not a proof, and it is not even available for the other
/// sources: `$VERIPB_BIN`, `$PATH/veripb`, [`NEUTRAL_DEFAULT`] and
/// `~/.cargo/bin/veripb` are all identity-free by construction. So every
/// resolved checker, FROM ANY SOURCE, is put to the behavioural gate instead.
///
/// This is not a new policy: `scripts/cert_ci.sh` has always run
/// `veripb_require_self_test` AND `veripb_require_soundness` over whatever
/// `$VERIPB` it resolved, from any source, over these same fixtures and this
/// same manifest. The Rust resolver was the one out of line.
///
/// MEASURED COST, 2026-09-22 on this workstation with the pinned build: twenty-
/// two extra checker spawns, ONCE PER PROCESS behind [`resolve_once`]'s
/// `OnceLock`, alongside the six self-test probes resolution already ran. On
/// `ay-pb --test veripb_pin_gate`, 0.07 s before and 0.12 s after on an
/// otherwise idle box (+0.05 s; that target already ran the same twenty-two in
/// its own test, so it goes from 28 spawns to 50). Two runs taken while several
/// other builds shared the machine read 0.21 s and 0.26 s — the spread is load,
/// not the battery.
///
/// # Errors
/// A report naming every fixture the checker accepted, what it answered, what is
/// actually true, and what an unfixed build answers there. Callers must treat it
/// as fatal: this is the one failure that looks like success.
///
/// # Panics
/// When `ci/veripb-soundness/expected.tsv` is missing or malformed. An empty
/// fixture list would make this gate a no-op, which is the exact failure mode
/// the module is built against, so it is a hard stop rather than a pass.
pub fn soundness_gate(checker: &Path) -> Result<(), String> {
    let fixtures = pin::soundness_fixtures();
    let accepted: Vec<String> = fixtures
        .iter()
        .filter_map(|fixture| {
            // The flag comes from the MANIFEST, not from `run`'s `--opb`
            // default: one fixture is a DIMACS CNF and one a WCNF, and two
            // format flags would leave the choice to the argument parser.
            let outcome = run(
                checker,
                &fixture.formula,
                &fixture.proof,
                &[fixture.flag.as_str()],
            );
            (!outcome.is_rejected()).then(|| {
                format!(
                    "  - {}: got `{}`, but the truth is {} (an unfixed checker answers `{}` here)",
                    fixture.name,
                    outcome.verdict_or_placeholder(),
                    fixture.truth,
                    fixture.wrong_verdict
                )
            })
        })
        .collect();

    if accepted.is_empty() {
        return Ok(());
    }
    Err(format!(
        "it ACCEPTED {} of the {} committed proof/formula pairs whose verdict \
         CONTRADICTS the truth:\n{}",
        accepted.len(),
        fixtures.len(),
        accepted.join("\n")
    ))
}

/// Everything resolution proves about a checker binary, applied to whatever
/// [`locate`] returned and regardless of WHERE it came from.
///
/// Split out of [`resolve_once`] so the two batteries can be driven over an
/// arbitrary path in a test — the point being tested is precisely that the
/// source does not matter.
fn vet(checker: PathBuf) -> Result<PathBuf, ResolveError> {
    if let Err(detail) = self_test(&checker) {
        return Err(ResolveError::SelfTestFailed { checker, detail });
    }
    if let Err(detail) = soundness_gate(&checker) {
        return Err(ResolveError::Unsound { checker, detail });
    }
    Ok(checker)
}

fn resolve_once() -> &'static Result<PathBuf, ResolveError> {
    static RESOLVED: OnceLock<Result<PathBuf, ResolveError>> = OnceLock::new();
    RESOLVED.get_or_init(|| vet(locate()?))
}

/// Resolve a self-tested checker, or report why none is usable.
pub fn resolve() -> Result<PathBuf, ResolveError> {
    resolve_once().clone()
}

fn opted_out() -> bool {
    std::env::var_os(OPT_OUT_ENV).is_some_and(|value| {
        let value = value.to_string_lossy().into_owned();
        !value.is_empty() && value != "0"
    })
}

/// Resolve the checker for a checker-backed suite, or FAIL LOUDLY.
///
/// Returns `None` only when the checker is genuinely absent AND the environment
/// explicitly opts out via `AY_VERIPB_OPTIONAL`; the skip is then announced on
/// stderr with the [`SKIP_MARKER`] prefix so it is greppable in CI logs.
///
/// A resolved-but-bogus checker always panics — self-test failure (not a
/// checker) and soundness-gate failure (a checker that gives wrong verdicts)
/// alike: the opt-out excuses an ABSENT checker, never a FAKE or an UNSOUND
/// one.
#[must_use]
pub fn require_checker(suite: &str) -> Option<PathBuf> {
    match resolve() {
        Ok(checker) => Some(checker),
        Err(error @ (ResolveError::SelfTestFailed { .. } | ResolveError::Unsound { .. })) => {
            panic!(
                "{suite}: the resolved VeriPB checker is not a checker this workspace may \
             certify against.\n{error}\n\
             This suite refuses to run against a binary that cannot check proofs, or \
             that checks them wrongly."
            )
        }
        Err(error) => {
            if opted_out() {
                eprintln!(
                    "{SKIP_MARKER}: {suite} did not run the checker ({OPT_OUT_ENV} is set). {error}"
                );
                return None;
            }
            panic!(
                "{suite}: this suite is checker-backed and cannot verify anything without VeriPB.\n\
                 {error}\n\
                 Set {OPT_OUT_ENV}=1 to acknowledge running WITHOUT external verification."
            )
        }
    }
}

/// Resolve the checker for a suite that DEGRADES when none is installed —
/// falling back to a text-shape check — instead of failing like
/// [`require_checker`].
///
/// Six such suites each rolled their own "is a checker around?" probe: some
/// read `$VERIPB_BIN` and scanned `$PATH`, some hardcoded a cache path, and NOT
/// ONE of them ran a single probe against what it found. A probe that finds an
/// unsound checker is worse than one that finds nothing, because the suite then
/// reads green having asked a binary with twenty-one wrong-verdict defects.
///
/// So the degrade policy is narrowed to what it was always meant to cover:
///
/// * checker ABSENT -> `None`, announced on stderr with [`SKIP_MARKER`];
/// * checker present but not a checker ([`self_test`]), or a checker that gives
///   WRONG VERDICTS ([`soundness_gate`]) -> PANIC;
/// * an override set to a path that does not exist -> PANIC. "A typo in
///   `VERIPB_BIN` must never silently degrade to 'checker absent'" is this
///   module's own rule, and a probe that swallowed [`ResolveError::BadOverride`]
///   broke it in the one place nobody was looking.
#[must_use]
pub fn optional_checker(suite: &str) -> Option<PathBuf> {
    match resolve() {
        Ok(checker) => Some(checker),
        Err(error @ (ResolveError::SelfTestFailed { .. } | ResolveError::Unsound { .. })) => {
            panic!(
                "{suite}: a VeriPB checker was found and it must not be used.\n{error}\n\
             Degrading is this suite's policy for a MISSING checker, never for a broken \
             or unsound one."
            )
        }
        Err(error @ ResolveError::BadOverride { .. }) => {
            panic!("{suite}: the checker override is set and wrong.\n{error}")
        }
        Err(error) => {
            eprintln!("{SKIP_MARKER}: {suite} did not run the checker. {error}");
            None
        }
    }
}

/// The checker PIN: which VeriPB this workspace's certified claims are made
/// against, read from the one committed source of truth.
///
/// `ci/veripb.pin` is `include_str!`d at COMPILE time, so the constants below
/// and the shell gate (`scripts/ci/pb_certified_gate.sh`, which `.`s the same
/// file) cannot disagree — there is no second copy to update.
///
/// Why a pin at all: "VeriPB accepted it" is only evidence if you can say WHICH
/// VeriPB. Published 3.0.2 has TWENTY-ONE confirmed wrong-verdict defects; a
/// checker carrying them will happily print `s VERIFIED UNSATISFIABLE` for a
/// satisfiable formula — and for defect 10 (propagation slack in the row's own
/// width), defect 11 (a `pbc` subproof fabricating a database proofgoal) and
/// defect 14 (order auxiliary variables that are not order-private) it does so
/// from a handful of proof lines against ANY formula, so at an unpatched pin no
/// UNSAT verdict is evidence of anything. [`soundness_fixtures`] is the
/// behavioural half of the pin: any checker AY trusts must refuse all TWENTY-TWO
/// fixtures, and that is asserted, not assumed. Twenty-two fixtures for
/// twenty-one defects: defect 7 (normalization wrapping) has two opposite
/// manifestations.
///
/// The pin names ONE patch file ([`patch`]): the private fork's `alab-main`
/// delta over the shared upstream base, which carries the fix for every one of
/// the twenty-one defects. It is part of the checker's identity and is in the
/// build-cache key. (This repo previously carried a second, locally written
/// patch for defects 9-21; those fixes now live in the fork and the second
/// patch was dropped — see the prose in `ci/veripb.pin`.)
pub mod pin {
    use std::path::{Path, PathBuf};
    use std::process::Command;

    /// The committed pin file, embedded at compile time.
    pub const PIN_FILE: &str = include_str!("../../../ci/veripb.pin");

    /// Repo-relative path of the pin file (for error messages).
    pub const PIN_PATH: &str = "ci/veripb.pin";

    /// Read one `KEY=VALUE` entry from the pin. `None` if absent.
    ///
    /// The format is deliberately strict: no quoting, no expansion, no spaces,
    /// `#` comments only at line start. That is what lets POSIX `sh` and this
    /// reader agree byte for byte.
    #[must_use]
    pub fn get(key: &str) -> Option<&'static str> {
        PIN_FILE.lines().find_map(|line| {
            let line = line.trim();
            if line.starts_with('#') {
                return None;
            }
            let (name, value) = line.split_once('=')?;
            (name == key).then_some(value)
        })
    }

    /// Read one entry, panicking with a pointed message when it is missing.
    #[must_use]
    pub fn require(key: &str) -> &'static str {
        get(key).unwrap_or_else(|| panic!("{PIN_PATH} does not define {key}"))
    }

    /// Upstream repository the pinned checker is built from.
    #[must_use]
    pub fn repo() -> &'static str {
        require("VERIPB_REPO")
    }

    /// The pinned upstream commit. This, not the version string, is the
    /// checker's identity: 3.0.2 has been many different checkers.
    #[must_use]
    pub fn commit() -> &'static str {
        require("VERIPB_COMMIT")
    }

    /// What `veripb --version` must report.
    #[must_use]
    pub fn version() -> &'static str {
        require("VERIPB_VERSION")
    }

    /// Repo-relative path of the patch applied on top of [`commit`].
    #[must_use]
    pub fn patch() -> &'static str {
        require("VERIPB_PATCH")
    }

    /// Expected SHA-256 of [`patch`]. The patch is part of the pin: it is what
    /// turns an unsound upstream build into the checker AY validated against.
    #[must_use]
    pub fn patch_sha256() -> &'static str {
        require("VERIPB_PATCH_SHA256")
    }

    /// Workspace root, derived from this crate's manifest directory.
    #[must_use]
    pub fn repo_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("ay-test-support lives at <root>/crates/ay-test-support")
            .to_path_buf()
    }

    /// The version string a checker reports, as the last whitespace-separated
    /// field of the last `--version` line (`veripb 3.0.2` -> `3.0.2`).
    #[must_use]
    pub fn reported_version(checker: &Path) -> Option<String> {
        let output = Command::new(checker).arg("--version").output().ok()?;
        let text = String::from_utf8_lossy(&output.stdout).into_owned()
            + &String::from_utf8_lossy(&output.stderr);
        text.lines()
            .rfind(|line| !line.trim().is_empty())?
            .split_whitespace()
            .next_back()
            .map(str::to_owned)
    }

    /// Check that `checker` reports the pinned version.
    ///
    /// # Errors
    /// When the binary reports nothing, or reports a version other than the pin.
    pub fn check_version(checker: &Path) -> Result<(), String> {
        let expected = version();
        match reported_version(checker) {
            Some(actual) if actual == expected => Ok(()),
            Some(actual) => Err(format!(
                "`{}` reports VeriPB version `{actual}`, but {PIN_PATH} pins `{expected}` \
                 (commit {}). A verdict from an unpinned checker is not evidence: repin \
                 deliberately (and re-run the soundness fixtures) or use the pinned build.",
                checker.display(),
                commit()
            )),
            None => Err(format!(
                "`{}` printed no parseable `--version` output; it cannot be the pinned checker",
                checker.display()
            )),
        }
    }

    /// One committed formula/proof pair that a trustworthy checker must refuse.
    #[derive(Clone, Debug)]
    pub struct SoundnessFixture {
        /// Fixture directory name, which is also the bug label.
        pub name: String,
        /// Formula-format flag the checker needs (`--opb` / `--cnf`).
        pub flag: String,
        /// Absolute path to the formula.
        pub formula: PathBuf,
        /// Absolute path to the proof.
        pub proof: PathBuf,
        /// What is actually true of the formula.
        pub truth: String,
        /// The verdict an UNFIXED checker returns — the thing being guarded.
        pub wrong_verdict: String,
    }

    /// Load the soundness fixtures listed in `ci/veripb-soundness/expected.tsv`.
    ///
    /// # Panics
    /// When the manifest is missing or malformed: an empty fixture list would
    /// turn the soundness gate into a no-op, which is the failure mode this
    /// whole module exists to prevent.
    #[must_use]
    pub fn soundness_fixtures() -> Vec<SoundnessFixture> {
        let root = repo_root();
        let dir = root.join(require("VERIPB_SOUNDNESS_DIR"));
        let manifest_path = dir.join("expected.tsv");
        let manifest = std::fs::read_to_string(&manifest_path).unwrap_or_else(|error| {
            panic!(
                "cannot read the checker soundness manifest {}: {error}",
                manifest_path.display()
            )
        });

        let fixtures: Vec<SoundnessFixture> = manifest
            .lines()
            .map(str::trim_end)
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
            .map(|line| {
                let fields: Vec<&str> = line.split('\t').collect();
                assert!(
                    fields.len() == 6,
                    "malformed row in {}: expected 6 tab-separated fields, got {}: {line:?}",
                    manifest_path.display(),
                    fields.len()
                );
                SoundnessFixture {
                    name: fields[0].to_owned(),
                    flag: fields[1].to_owned(),
                    formula: dir.join(fields[0]).join(fields[2]),
                    proof: dir.join(fields[0]).join(fields[3]),
                    truth: fields[4].to_owned(),
                    wrong_verdict: fields[5].to_owned(),
                }
            })
            .collect();

        assert!(
            !fixtures.is_empty(),
            "{} lists no fixtures; the soundness gate would be vacuous",
            manifest_path.display()
        );
        fixtures
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn pin_fields_are_present_and_well_formed() {
            assert!(repo().starts_with("https://"), "repo: {}", repo());
            assert_eq!(
                commit().len(),
                40,
                "commit must be a full sha: {}",
                commit()
            );
            assert!(
                commit().chars().all(|c| c.is_ascii_hexdigit()),
                "commit must be hex: {}",
                commit()
            );
            assert_eq!(
                patch_sha256().len(),
                64,
                "patch sha256 must be 64 hex chars"
            );
            assert!(!version().is_empty());
        }

        // The patch-file hash check lives in tests/veripb_patch_pin.rs: the
        // patch is development-only (the public snapshot ships the pin, not
        // the patch), so that one test target is excluded from the export.

        #[test]
        fn all_twenty_two_soundness_fixtures_are_present_on_disk() {
            let fixtures = soundness_fixtures();
            assert_eq!(
                fixtures.len(),
                22,
                "twenty-one known wrong-verdict defects are pinned, covered by \
                 twenty-two fixtures (defect 7 has two opposite manifestations)"
            );
            for fixture in fixtures {
                assert!(
                    fixture.formula.is_file(),
                    "missing formula {}",
                    fixture.formula.display()
                );
                assert!(
                    fixture.proof.is_file(),
                    "missing proof {}",
                    fixture.proof.display()
                );
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Repo-relative path of the ONE shell-side cache-key authority.
    const BUILD_ID_LIB: &str = "scripts/lib/veripb_build_id.sh";

    /// `-vV` output modelled on real rustc: commit-hash BEFORE release, which
    /// is exactly the ordering that made a positional parse produce
    /// unreadable directory names (commit 8499748c6).
    #[cfg(unix)]
    const STUB_VV: &str = "rustc 1.90.0 (abcdef12345 2026-01-01)\n\
binary: rustc\n\
commit-hash: abcdef1234567890ffffffffffffffffffffffff\n\
commit-date: 2026-01-01\n\
host: aarch64-apple-darwin\n\
release: 1.90.0\n\
LLVM version: 20.1.0\n";

    /// Write an executable stub at `path` with the given body.
    #[cfg(unix)]
    fn write_stub(path: &Path, body: &str) {
        use std::os::unix::fs::PermissionsExt;
        std::fs::write(path, body).expect("write stub");
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755)).expect("chmod stub");
    }

    /// An executable stub compiler whose `-vV` is [`STUB_VV`].
    #[cfg(unix)]
    fn write_stub_rustc(path: &Path) {
        write_stub(
            path,
            &format!("#!/bin/sh\ncat <<'STUBEOF'\n{STUB_VV}STUBEOF\n"),
        );
    }

    /// Run `script` in a POSIX sh that has sourced the build-id lib, with
    /// `$RUSTC` forced (or forcibly absent) so the lib's compiler resolution
    /// is hermetic no matter what this machine carries on PATH.
    #[cfg(unix)]
    fn run_build_id_lib(rustc: Option<&Path>, script: &str) -> (Option<i32>, String, String) {
        let lib = pin::repo_root().join(BUILD_ID_LIB);
        assert!(lib.is_file(), "missing {BUILD_ID_LIB}");
        let mut command = Command::new("sh");
        command
            .arg("-u")
            .arg("-c")
            .arg(format!(". '{}'\n{script}", lib.display()));
        match rustc {
            Some(path) => {
                command.env("RUSTC", path);
            }
            None => {
                command.env_remove("RUSTC");
            }
        }
        let output = command.output().expect("run sh against the build-id lib");
        (
            output.status.code(),
            String::from_utf8_lossy(&output.stdout)
                .trim_end()
                .to_string(),
            String::from_utf8_lossy(&output.stderr).into_owned(),
        )
    }

    /// THE cross-language pin, and it is EXECUTABLE, not textual: the
    /// cache-key format lives in one shell file, and this test runs that
    /// file's functions under a stub compiler and compares byte-for-byte with
    /// the Rust side. The two cannot drift the way pb_certified_gate.sh once
    /// drifted from this resolver (the gate grew a -rustc<fingerprint> suffix
    /// on 2026-08-30 while this file, cert_ci.sh and maxsat_cert.rs still
    /// computed the unkeyed id, leaving the same pinned checker at two
    /// different cache paths depending on which entry point built it).
    #[cfg(unix)]
    #[test]
    fn shell_and_rust_agree_on_the_cache_key() {
        let dir = unique_temp_dir("build-id-agree");
        std::fs::create_dir_all(&dir).expect("mkdir");
        let stub = dir.join("rustc");
        write_stub_rustc(&stub);

        let (code, keyed, stderr) = run_build_id_lib(
            Some(&stub),
            &format!("veripb_build_id {} {}", pin::commit(), pin::patch_sha256()),
        );
        assert_eq!(code, Some(0), "veripb_build_id failed: {stderr}");
        assert_eq!(
            keyed,
            format!("{}{RUSTC_KEY_INFIX}1.90.0-abcdef1234", pinned_build_id()),
            "shell keyed id must be the Rust identity prefix plus -rustc<release>-<hash10>"
        );
        assert!(
            is_pinned_cache_dir(&keyed, &pinned_build_id()),
            "the resolver must accept every directory name the shell side builds"
        );

        let (code, legacy, stderr) = run_build_id_lib(
            None,
            &format!(
                "veripb_legacy_build_id {} {}",
                pin::commit(),
                pin::patch_sha256()
            ),
        );
        assert_eq!(code, Some(0), "veripb_legacy_build_id failed: {stderr}");
        assert_eq!(
            legacy,
            pinned_build_id(),
            "the legacy (pre-compiler-key) id IS the Rust identity"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Fail closed, out loud: no key may ever be minted for a compiler that
    /// cannot be identified — a cache keyed blindly is a cache that hands a
    /// foreign-compiler build to a gate that compiles inside it.
    #[cfg(unix)]
    #[test]
    fn cache_key_refuses_an_unidentifiable_compiler() {
        let dir = unique_temp_dir("build-id-refuse");
        std::fs::create_dir_all(&dir).expect("mkdir");
        let broken = dir.join("rustc");
        write_stub(&broken, "#!/bin/sh\nexit 1\n");
        let (code, stdout, stderr) = run_build_id_lib(
            Some(&broken),
            &format!("veripb_build_id {} {}", pin::commit(), pin::patch_sha256()),
        );
        assert_ne!(
            code,
            Some(0),
            "a compiler with no -vV output must be refused"
        );
        assert_eq!(stdout, "", "no key may be printed on the failure path");
        assert!(
            stderr.contains("ERROR"),
            "the refusal must be loud: {stderr}"
        );

        // A $RUSTC that does not exist is refused too, with the fix named —
        // cargo would fail on it as well, so silently falling through to a
        // different compiler would key the cache with the wrong identity.
        let (code, stdout, stderr) =
            run_build_id_lib(Some(Path::new("/nonexistent/rustc")), "veripb_rustc_path");
        assert_ne!(code, Some(0));
        assert_eq!(stdout, "");
        assert!(stderr.contains("not executable"), "{stderr}");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// The compiler_consumer sysroot's compat entry keys the cache whenever the Trust
    /// toolchain is installed: that is the compiler `targo` runs, and it
    /// outranks a bare `rustc` on PATH (inside aterm that is a reroute stub,
    /// and on a Trust machine it is not what builds the checker). Only a host
    /// without compiler_consumer falls through to the PATH rustc, which plain cargo runs.
    #[cfg(unix)]
    #[test]
    fn cache_key_compiler_resolution_covers_a_trust_only_machine() {
        let dir = unique_temp_dir("build-id-trust");
        let bin = dir.join("bin");
        let stock_bin = dir.join("stock-bin");
        let sysroot = dir.join("sysroot");
        std::fs::create_dir_all(&bin).expect("mkdir");
        std::fs::create_dir_all(&stock_bin).expect("mkdir");
        std::fs::create_dir_all(sysroot.join("bin")).expect("mkdir");
        let sysroot_rustc = sysroot.join("bin/rustc");
        write_stub_rustc(&sysroot_rustc);
        write_stub(
            &bin.join("compiler_consumer"),
            &format!("#!/bin/sh\nprintf '%s\\n' '{}'\n", sysroot.display()),
        );
        let path_rustc = stock_bin.join("rustc");
        write_stub_rustc(&path_rustc);
        let lib = pin::repo_root().join(BUILD_ID_LIB);
        let resolve = |path: String| {
            let output = Command::new("sh")
                .arg("-u")
                .arg("-c")
                .arg(format!(
                    "PATH='{path}'; export PATH\n. '{}'\nveripb_rustc_path",
                    lib.display()
                ))
                .env_remove("RUSTC")
                .output()
                .expect("run sh against the build-id lib");
            assert_eq!(
                output.status.code(),
                Some(0),
                "stderr: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            String::from_utf8_lossy(&output.stdout)
                .trim_end()
                .to_string()
        };
        // Trust toolchain installed, with or without a bare rustc on PATH.
        for path in [
            format!("{}:/usr/bin:/bin", bin.display()),
            format!("{}:{}:/usr/bin:/bin", stock_bin.display(), bin.display()),
        ] {
            assert_eq!(
                resolve(path.clone()),
                sysroot_rustc.to_str().unwrap(),
                "the compiler_consumer sysroot compat entry must key the cache (PATH={path})"
            );
        }
        // No compiler_consumer: the PATH rustc plain cargo would run.
        assert_eq!(
            resolve(format!("{}:/usr/bin:/bin", stock_bin.display())),
            path_rustc.to_str().unwrap(),
            "without the Trust toolchain the PATH rustc keys the cache"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// The gate scripts must SOURCE the one authority rather than carrying
    /// their own copy of the format — inline reimplementation is exactly how
    /// the key drifted apart in the first place — and the `-rustc` infix the
    /// Rust resolver matches on must be the one the lib prints.
    #[test]
    fn gate_scripts_source_the_one_cache_key_authority() {
        let root = pin::repo_root();
        let lib = std::fs::read_to_string(root.join(BUILD_ID_LIB)).expect("read the build-id lib");
        assert!(
            lib.contains(&format!("'%s-%s{RUSTC_KEY_INFIX}%s\\n'")),
            "the lib's keyed printf format must carry the `{RUSTC_KEY_INFIX}` infix \
             the Rust resolver matches on"
        );
        for script in ["scripts/ci/pb_certified_gate.sh", "scripts/cert_ci.sh"] {
            let text = std::fs::read_to_string(root.join(script))
                .unwrap_or_else(|error| panic!("read {script}: {error}"));
            assert!(
                text.contains("scripts/lib/veripb_build_id.sh"),
                "{script} must source the cache-key authority"
            );
            assert!(
                text.contains("$(veripb_build_id "),
                "{script} must compute its BUILD_ID via veripb_build_id"
            );
            for inline in ["-rustc${", "-rustc$("] {
                assert!(
                    !text.contains(inline),
                    "{script} reimplements the keyed id inline (`{inline}`) \
                     instead of using the lib"
                );
            }
        }
    }

    /// The resolver accepts every cache directory the shell side may have
    /// built — keyed by any compiler, or the pre-2026-08-30 legacy layout —
    /// because a finished binary runs the same under any of today's compilers
    /// and its behaviour is re-proved by the self-test either way. It must
    /// NOT accept a directory belonging to a different pin.
    #[test]
    fn pinned_cache_scan_finds_keyed_and_legacy_builds_and_nothing_else() {
        let cache = unique_temp_dir("cache-scan");
        let pinned_id = pinned_build_id();
        for name in [
            pinned_id.clone(),
            format!("{pinned_id}-rustc1.96.0-ac68faa20c"),
            format!("{pinned_id}-rustc1.99.0-dev-acb08e7616"),
        ] {
            std::fs::create_dir_all(cache.join(name)).expect("mkdir");
        }
        let strangers = [
            String::from("deadbeef-000000000000"),
            format!("{pinned_id}x"),
            format!("{pinned_id}-other"),
        ];
        for stranger in &strangers {
            std::fs::create_dir_all(cache.join(stranger)).expect("mkdir");
            assert!(
                !is_pinned_cache_dir(stranger, &pinned_id),
                "`{stranger}` is not a build of this pin"
            );
        }
        let expected: Vec<PathBuf> = [
            format!("{pinned_id}-rustc1.99.0-dev-acb08e7616"),
            format!("{pinned_id}-rustc1.96.0-ac68faa20c"),
            pinned_id.clone(),
        ]
        .iter()
        .map(|name| cache.join(name).join("target/release/veripb"))
        .collect();
        assert_eq!(
            pinned_cache_candidates(&cache),
            expected,
            "keyed builds first (later fingerprints first), legacy last, strangers never"
        );

        // An empty or absent cache still names the legacy path, so a
        // NotFound error can say where a build would land.
        let empty = unique_temp_dir("cache-scan-empty");
        assert_eq!(
            pinned_cache_candidates(&empty),
            vec![empty.join(&pinned_id).join("target/release/veripb")]
        );
        let _ = std::fs::remove_dir_all(&cache);
    }

    /// REGRESSION (2026-09-22): every cache path this resolver will hand to a
    /// gate must carry the checker's IDENTITY in its directory name.
    ///
    /// The resolver used to append `<cache>/VeriPB/target/release/veripb` — the
    /// PRE-PIN layout — after the identity-bearing ones. Its name records no
    /// commit and no patch, and the early `scripts/cert_ci.sh` that populated it
    /// `git clone --depth 1`d the upstream DEFAULT BRANCH and built it
    /// UNPATCHED. When the pin's patch was re-cut, no keyed directory matched
    /// any more, resolution fell through to that path, and an upstream 3.0.2
    /// that ACCEPTS all 22 committed wrong-verdict fixtures became the checker
    /// behind every "and VeriPB said VERIFIED" in this workspace. The version
    /// string did not discriminate it: it reports the pinned `3.0.2`.
    ///
    /// So: a checker binary present at that path must NOT be resolvable, and
    /// every cache candidate offered must be one `is_pinned_cache_dir` accepts.
    #[test]
    fn resolution_never_offers_a_cache_path_without_the_pin_identity() {
        let cache = unique_temp_dir("cache-identity-scan");
        let pinned_id = pinned_build_id();
        for name in [
            "VeriPB",
            "veripb",
            "4bb10c2ce98a8c80122a7a2399d7f35ffdc6e58e-deadbeefcafe",
            &format!("{pinned_id}-rustc1.99.0-dev-acb08e7616"),
        ] {
            std::fs::create_dir_all(cache.join(name).join("target/release"))
                .expect("create cache entry");
            std::fs::write(
                cache.join(name).join("target/release/veripb"),
                b"#!/bin/sh\nexit 0\n",
            )
            .expect("write stub checker");
        }

        let offered = pinned_cache_candidates(&cache);
        for candidate in &offered {
            let dir = candidate
                .parent()
                .and_then(Path::parent)
                .and_then(Path::parent)
                .and_then(|d| d.file_name())
                .and_then(|n| n.to_str())
                .expect("cache candidate is <cache>/<id>/target/release/veripb");
            assert!(
                is_pinned_cache_dir(dir, &pinned_id),
                "resolution offered `{}`, whose directory name `{dir}` carries no pin \
                 identity — a binary there could be any checker at all",
                candidate.display()
            );
        }
        assert!(
            !offered
                .iter()
                .any(|candidate| candidate.ends_with(PRE_PIN_CACHE_REL)),
            "the PRE-PIN cache layout `{PRE_PIN_CACHE_REL}` is back in the resolution \
             order; by construction it holds an UNPINNED, UNPATCHED upstream build"
        );
        assert_eq!(
            offered,
            vec![cache
                .join(format!("{pinned_id}-rustc1.99.0-dev-acb08e7616"))
                .join("target/release/veripb")],
            "only the identity-bearing entry is a candidate"
        );

        let _ = std::fs::remove_dir_all(&cache);
    }

    // ------------------------------------------------------------------
    // TOTALITY (2026-09-22). Identity closed ONE source, the cache. These
    // close the rest: the ranking, and the gate that applies to every source
    // because identity is not available for any of the others.
    // ------------------------------------------------------------------

    /// A stub that PASSES all six [`self_test`] probes and still gives wrong
    /// verdicts — a faithful model of published VeriPB 3.0.2, which is the
    /// binary this workspace actually resolved on 2026-09-22.
    ///
    /// It dispatches on the last argument, which `run_text` places in a scratch
    /// directory named after the probe label, so the six probes are answered
    /// exactly as a real checker answers them while everything else — the
    /// twenty-two committed fixtures included — is rubber-stamped.
    #[cfg(unix)]
    const UPSTREAM_3_0_2_MODEL: &str = r#"#!/bin/sh
for a in "$@"; do p="$a"; done
case "$p" in
  *selftest-good-unsat*) echo 's VERIFIED UNSATISFIABLE'; exit 0 ;;
  *selftest-good-sat*)   echo 's VERIFIED SATISFIABLE'; exit 0 ;;
  *selftest-*)           echo 'c refused'; exit 1 ;;
  *)                     echo 's VERIFIED UNSATISFIABLE'; exit 0 ;;
esac
"#;

    /// THE reason resolution cannot stop at [`self_test`], as an executable
    /// statement rather than a claim in prose.
    ///
    /// The six probes ask "is this a checker?" and this stub answers yes to all
    /// six. Nothing in them asks "is it a CORRECT one?", and the measured
    /// incident is precisely a binary that passes them, reports the pinned
    /// version string, and contradicts the truth on every committed fixture.
    #[cfg(unix)]
    #[test]
    fn a_checker_can_pass_every_self_test_probe_and_still_fail_the_soundness_gate() {
        let dir = unique_temp_dir("upstream-model");
        std::fs::create_dir_all(&dir).expect("mkdir");
        let stub = dir.join("veripb");
        write_stub(&stub, UPSTREAM_3_0_2_MODEL);

        self_test(&stub).expect("the model answers all six probes the way a checker does");

        let detail = soundness_gate(&stub)
            .expect_err("a checker that rubber-stamps the fixtures is not a sound checker");
        assert!(detail.contains("ACCEPTED 22 of the 22"), "{detail}");
        assert!(detail.contains("03-degree-wrap-weaken"), "{detail}");

        match vet(stub.clone()) {
            Err(ResolveError::Unsound { checker, .. }) => assert_eq!(checker, stub),
            other => panic!("resolution must refuse it as Unsound, got {other:?}"),
        }

        let _ = std::fs::remove_dir_all(&dir);
    }

    /// The gate does not depend on WHICH source offered the binary.
    ///
    /// [`vet`] is what every caller of [`resolve`] goes through and it takes a
    /// path: it cannot see whether that path came from `$VERIPB_BIN`, from
    /// `$PATH`, from [`NEUTRAL_DEFAULT`], from `~/.cargo/bin` or from an
    /// identity-bearing cache directory. That is the property being pinned —
    /// four of those five channels cannot carry an identity at all, so the one
    /// thing that can be asked of all five is that the binary BEHAVE.
    #[cfg(unix)]
    #[test]
    fn vetting_does_not_depend_on_which_source_offered_the_binary() {
        let root = unique_temp_dir("any-source");
        for channel in ["env-override", "path-hit", "neutral-default"] {
            let dir = root.join(channel);
            std::fs::create_dir_all(&dir).expect("mkdir");
            let stub = dir.join("veripb");
            write_stub(&stub, UPSTREAM_3_0_2_MODEL);
            assert!(
                matches!(vet(stub), Err(ResolveError::Unsound { .. })),
                "an unsound checker offered through `{channel}` was accepted"
            );
        }
        let _ = std::fs::remove_dir_all(&root);
    }

    /// REGRESSION (2026-09-22, totality): the RANK of the identity-bearing
    /// pinned build.
    ///
    /// `/tmp/veripb-3/bin/veripb` used to be the FIRST element of the built-in
    /// list, and `$PATH` was scanned before that list was consulted at all. So
    /// on a machine carrying both, a checker whose path records no commit and
    /// no patch beat the build this repo's own scripts produce. The neutral
    /// default is still offered — `publish/DECISIONS.md` keeps it on purpose —
    /// but it is offered LAST-but-one, not first.
    #[test]
    fn the_pinned_build_outranks_every_identity_free_candidate() {
        let cache = unique_temp_dir("rank-cache");
        let pinned_id = pinned_build_id();
        let keyed = format!("{pinned_id}-rustc1.99.0-dev-acb08e7616");
        std::fs::create_dir_all(cache.join(&keyed)).expect("mkdir");
        let home = unique_temp_dir("rank-home");
        let on_path = unique_temp_dir("rank-path").join("veripb");

        assert_eq!(
            search_order(Some(&cache), Some(on_path.clone()), Some(&home)),
            vec![
                cache.join(&keyed).join("target/release/veripb"),
                on_path,
                PathBuf::from(NEUTRAL_DEFAULT),
                home.join(".cargo/bin/veripb"),
            ],
            "identity-bearing pinned build first; $PATH, the neutral default and \
             ~/.cargo/bin carry no identity and rank below it"
        );

        let _ = std::fs::remove_dir_all(&cache);
    }

    /// An empty `$PATH` slot still occupies its position in the searched list,
    /// so [`ResolveError::NotFound`]'s "searched, in order:" keeps telling the
    /// truth about the order — the only way a reader can see the ranking.
    #[test]
    fn the_path_slot_is_reported_in_its_real_position_when_nothing_is_on_path() {
        let cache = unique_temp_dir("slot-cache");
        let pinned_id = pinned_build_id();
        assert_eq!(
            search_order(Some(&cache), None, None),
            vec![
                cache.join(&pinned_id).join("target/release/veripb"),
                PathBuf::from(PATH_SLOT),
                PathBuf::from(NEUTRAL_DEFAULT),
            ]
        );
        assert!(
            !PathBuf::from(PATH_SLOT).is_file(),
            "the `$PATH` placeholder must never be resolvable"
        );
    }

    #[test]
    fn no_conclusion_is_not_a_verified_verdict() {
        let run = CheckerRun {
            checker: PathBuf::from("/nonexistent"),
            args: Vec::new(),
            exit_code: Some(0),
            stdout: String::from("Running VeriPB version 3.0.2\ns VERIFIED NO CONCLUSION\n"),
            stderr: String::new(),
        };
        assert!(!run.is_verified());
        assert!(run.is_rejected());
    }

    #[test]
    fn silent_exit_zero_binary_is_not_verified() {
        let run = CheckerRun {
            checker: PathBuf::from("/usr/bin/true"),
            args: Vec::new(),
            exit_code: Some(0),
            stdout: String::new(),
            stderr: String::new(),
        };
        assert!(!run.is_verified());
        assert_eq!(run.verdict_or_placeholder(), "<no `s ...` verdict line>");
    }

    fn run_printing(verdict: &str) -> CheckerRun {
        CheckerRun {
            checker: PathBuf::from("/nonexistent"),
            args: Vec::new(),
            exit_code: Some(0),
            stdout: format!("Running VeriPB version 3.0.2\n{verdict}\n"),
            stderr: String::new(),
        }
    }

    #[test]
    fn bounds_expectation_matches_the_checker_restatement() {
        let expect = Expect::bounds("3", "3");
        assert!(expect.conclusion.matches(
            run_printing("s VERIFIED BOUNDS 3 <= obj <= 3")
                .parsed_verdict()
                .unwrap()
                .1
        ));
        assert!(!expect.conclusion.matches(
            run_printing("s VERIFIED BOUNDS 2 <= obj <= 3")
                .parsed_verdict()
                .unwrap()
                .1
        ));
        assert!(!Conclusion::Any.matches(NO_CONCLUSION));
        assert!(Conclusion::Unsatisfiable.matches("UNSATISFIABLE"));
    }

    /// `veripb -u` prints `s UNDER WEAKENED GUARANTEES ...` and exits 0. It is
    /// an ACCEPTANCE, but a weaker one, and a gate that asked for full
    /// verification must not silently take it.
    #[test]
    fn weakened_guarantees_is_not_full_verification() {
        let run = run_printing("s UNDER WEAKENED GUARANTEES BOUNDS 3 <= obj <= 3");
        assert_eq!(run.exit_code(), Some(0));
        assert!(!run.is_verified());
        assert!(!run.is_accepted_at(Guarantee::Verified));
        assert!(run.is_accepted_at(Guarantee::Weakened));
        assert!(!run.is_rejected());
        run.assert_verified(
            &Expect::bounds("3", "3").under_weakened_guarantees(),
            "weakened acceptance",
        );
    }

    #[test]
    fn full_verification_satisfies_a_weakened_expectation() {
        let run = run_printing("s VERIFIED UNSATISFIABLE");
        run.assert_verified(
            &Expect::UNSAT.under_weakened_guarantees(),
            "verified is stronger than weakened",
        );
    }

    #[cfg(unix)]
    #[test]
    fn self_test_rejects_an_exit_zero_no_op_binary() {
        let error = self_test(Path::new("/usr/bin/true"))
            .expect_err("/usr/bin/true must not pass the VeriPB self-test");
        assert!(
            error.contains("selftest-good-unsat"),
            "self-test must fail on the first must-verify probe: {error}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn self_test_rejects_an_always_failing_binary() {
        let error = self_test(Path::new("/usr/bin/false"))
            .expect_err("/usr/bin/false must not pass the VeriPB self-test");
        assert!(
            error.contains("selftest-good-unsat"),
            "self-test must fail on the first must-verify probe: {error}"
        );
    }

    fn run_with(verdict: &str, exit_code: i32) -> CheckerRun {
        CheckerRun {
            checker: PathBuf::from("/nonexistent"),
            args: Vec::new(),
            exit_code: Some(exit_code),
            stdout: format!("Running VeriPB version 3.0.2\n{verdict}\n"),
            stderr: String::new(),
        }
    }

    /// FAKE (i): the right verdict from a run that did not finish.
    ///
    /// This is the fake the module used to wave through, because it documented
    /// "gates assert on the verdict LINE, never on exit status". The line is
    /// genuinely correct; the process still failed. Acceptance needs both.
    #[test]
    fn a_correct_verdict_from_a_failed_run_is_not_an_acceptance() {
        let run = run_with("s VERIFIED UNSATISFIABLE", 1);
        assert_eq!(run.verdict(), Some("s VERIFIED UNSATISFIABLE"));
        assert!(!run.exit_ok());
        assert!(!run.is_verified());
        assert!(!run.is_accepted_at(Guarantee::Weakened));
        assert!(run.is_rejected());
    }

    /// FAKE (ii): silence and success. Covered by
    /// [`silent_exit_zero_binary_is_not_verified`]; asserted here at the
    /// acceptance boundary too.
    #[test]
    fn silence_with_a_clean_exit_is_not_an_acceptance() {
        let run = CheckerRun {
            checker: PathBuf::from("/usr/bin/true"),
            args: Vec::new(),
            exit_code: Some(0),
            stdout: String::new(),
            stderr: String::new(),
        };
        assert!(run.exit_ok());
        assert!(run.is_rejected());
    }

    /// FAKE (iii) and the conclusion-matching rule: a checker confirming the
    /// OPPOSITE of the claim under test must not satisfy that claim's gate.
    #[test]
    fn a_verified_but_contradictory_conclusion_does_not_satisfy_the_claim() {
        let run = run_with("s VERIFIED UNSATISFIABLE", 0);
        // It IS an acceptance — of a different statement.
        assert!(run.is_verified());
        assert!(!Conclusion::Satisfiable.matches(run.parsed_verdict().unwrap().1));
        assert!(!Conclusion::Bounds {
            lower: String::from("3"),
            upper: String::from("3"),
        }
        .matches(run.parsed_verdict().unwrap().1));
    }

    /// The prefix bug, stated as the property that used to fail: `s VERIFIED`
    /// is a prefix of `s VERIFIED NO CONCLUSION`, so a prefix test passes a
    /// proof that concluded nothing. Conclusion matching is what fixes it.
    #[test]
    fn no_conclusion_starts_with_the_success_prefix_but_is_not_a_pass() {
        let run = run_with("s VERIFIED NO CONCLUSION", 0);
        assert!(run.verdict().unwrap().starts_with("s VERIFIED"));
        assert!(!run.is_verified());
        assert!(run.is_rejected());
        assert!(!Conclusion::Any.matches(run.parsed_verdict().unwrap().1));
    }
}
