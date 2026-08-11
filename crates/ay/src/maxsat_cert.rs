// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The certificate lane for `ay maxsat bench --proof-check`: resolve the pinned
//! VeriPB checker, decide which rows get certified, read the checker's verdict,
//! and fold that verdict into a bench row.
//!
//! # THE RULE: a certificate may only DOWNGRADE
//!
//! This is the read side of `crate::maxsat_proof`'s write-only rule, and it
//! carries the same obligation from the other direction. Emission may never
//! promote an answer; checking may never promote a row. Concretely:
//! [`classify_certificate`] takes no [`RunStatus`] as input, its single caller
//! is the one `RunStatus::Optimum` construction site in `cmd_maxsat.rs`, and
//! every arm it can return is at or below `Optimum` in the scoring lattice
//! (`Optimum` -> `Unvalidated` -> `Wrong`). There is no code path by which a
//! Timeout, Memout, Error or Unvalidated row can be turned into a solved one by
//! anything in this module, because no certificate code runs on those paths at
//! all. AY's one historical wrong answer came from bound reasoning reaching the
//! answer path; a certificate reader that can raise a verdict would be the same
//! defect wearing a badge.
//!
//! # THE OTHER RULE: never vacuous
//!
//! `crates/ay-test-support/src/veripb.rs` records the incident this module is
//! built against: a checker-backed suite that "reported green in 0.00s having
//! checked nothing, and that `/usr/bin/true` could satisfy end to end". So the
//! word VERIFIED here is earned twice:
//!
//! * [`self_test`] runs the resolved binary against a proof it MUST accept and
//!   a proof it MUST reject before the sweep starts. `/bin/true` and
//!   `/bin/false` fail the first; `ci/fake-checkers/parrot.sh` — which reads
//!   the conclusion out of the proof and echoes it back — passes the first by
//!   construction and can only be caught by the second.
//! * [`parse_verdict`] accepts only `exit 0` AND a first `s ` line reading
//!   `s VERIFIED BOUNDS <lo> <= obj <= <hi>`. It is deliberately NOT a
//!   substring search over stdout — that is the defect in
//!   `ay-pb/src/veripb_runner.rs:472-481`, where a `c` comment line containing
//!   the word VERIFIED is enough to pass.
//!
//! The two probes here are the same discipline as the six in `ay-test-support`,
//! narrowed to the conclusion shape this lane emits (`BOUNDS`, not `UNSAT` or
//! `SAT`). The remaining four there are a checker-SOUNDNESS gate (does this
//! build carry the six known upstream wrong-verdict bugs?) that
//! `scripts/ci/pb_certified_gate.sh` already owns and re-proves against
//! committed fixtures. What a bench sweep needs to establish at t=0 is
//! narrower: that the binary it is about to trust can both verify and refuse.
//! Two probes is the minimum that establishes it, and it costs ~0.2s rather
//! than ~1s per sweep.
//!
//! Both probes must state their claim in the SHAPE `crate::maxsat_proof`
//! actually writes. A probe that differs structurally is not a probe of the
//! same thing: the false probe used to omit the conclusion's `: <hint-id>`
//! field, and that one missing token made the whole anti-parrot gate vacuous
//! (see [`SELF_TEST_FALSE_PBP`]).
//!
//! # Absent or unusable checker: a two-tier policy
//!
//! * **At startup**, `--proof-check` with no usable checker is a hard `bail!`.
//!   That is a hard failure that costs ZERO sweep time: it happens before the
//!   first spawn, so it cannot throw away a 3600s x 473 campaign. Prior art in
//!   this repo is `require_checker`, which PANICS; at t~=0.2s a bail is the
//!   same policy with a better exit path.
//! * **Mid-sweep**, a checker that becomes unusable (binary deleted, spawn
//!   fails, checker times out, watchdog kills it, artifacts missing) NEVER
//!   aborts. The row becomes `RunStatus::Unvalidated`. That is not a silent
//!   pass: `scoring_solved` counts only `Optimum`, and `bench_exit_code`
//!   already returns 1 whenever `unvalidated > 0`, so a sweep that lost its
//!   checker cannot print a green summary or exit 0 — while 473 solver-hours
//!   are not thrown away either.
//!
//! `AY_VERIPB_OPTIONAL` is deliberately NOT honoured here. It exists so a test
//! suite can run on a machine with no checker; a bench invocation that
//! explicitly passed `--proof-check` has no honest degraded mode.

use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::Duration;

use crate::cmd_maxsat::{run_cert_probe, RunStatus};

/// The checker PIN: which VeriPB this binary's certified claims are made
/// against.
///
/// `ay-test-support`'s copy of this reader is a DEV-dependency of `ay`
/// (`crates/ay/Cargo.toml`) and therefore unreachable from the shipping binary,
/// so the reader is duplicated here — but the DATA is not. Both `include_str!`
/// the one committed `ci/veripb.pin`, so an installed `ay` resolves the same
/// checker CI does and there is no second copy to drift. Embedding a committed
/// file rather than reading it at runtime is the crate's existing idiom
/// (`crates/ay-bisect/src/resource.rs` does it with `scripts/_oom_guard.py`),
/// and `publish/manifest.txt` ships `ci/veripb.pin` precisely so the exported
/// workspace still compiles.
pub(crate) mod pin {
    /// The committed pin file, embedded at compile time.
    pub(crate) const PIN_FILE: &str = include_str!("../../../ci/veripb.pin");

    /// Repo-relative path of the pin file (for error messages).
    pub(crate) const PIN_PATH: &str = "ci/veripb.pin";

    /// Read one `KEY=VALUE` entry from the pin. `None` if absent.
    ///
    /// Byte-identical in behaviour to `ay_test_support::veripb::pin::get`: the
    /// format is strict KEY=VALUE, no quoting, no expansion, `#` comments only
    /// at line start. That is what lets POSIX `sh`, the test-support reader and
    /// this reader agree exactly.
    pub(crate) fn get(key: &str) -> Option<&'static str> {
        PIN_FILE.lines().find_map(|line| {
            let line = line.trim();
            if line.starts_with('#') {
                return None;
            }
            let (name, value) = line.split_once('=')?;
            (name == key).then_some(value)
        })
    }

    fn require(key: &str) -> &'static str {
        // A pin missing a field is a build-time defect in a committed file, not
        // a runtime condition; the empty string would make the cache key and
        // the version cross-check silently wrong instead.
        get(key).unwrap_or("")
    }

    /// The pinned upstream commit. This, not the version string, is the
    /// checker's identity: 3.0.2 has been many different checkers.
    pub(crate) fn commit() -> &'static str {
        require("VERIPB_COMMIT")
    }

    /// What `veripb --version` should report. A cross-check, never an identity.
    pub(crate) fn version() -> &'static str {
        require("VERIPB_VERSION")
    }

    /// SHA-256 of the patch applied on top of [`commit`]. The patch is part of
    /// the pin: it is what turns an unsound upstream build into the checker AY
    /// validated against.
    pub(crate) fn patch_sha256() -> &'static str {
        require("VERIPB_PATCH_SHA256")
    }
}

/// Environment overrides consulted first, in order. Same names, same order as
/// `ay_test_support::veripb::CHECKER_ENV_VARS`, so a machine configured for the
/// test suites is configured for the bench lane.
const CHECKER_ENV_VARS: [&str; 3] = ["VERIPB_BIN", "AY_PB26_VERIPB_BIN", "VERIPB"];

/// Colon-separated candidate list that REPLACES the built-in known build
/// locations. Set it to a nonexistent path to model a machine with no checker.
const SEARCH_PATH_ENV: &str = "AY_VERIPB_SEARCH_PATH";

/// Cache-key contract shared with `scripts/ci/pb_certified_gate.sh` and
/// `ay-test-support`: the patch is part of the checker identity, so a changed
/// patch must not silently reuse a binary built from the same upstream commit.
fn pinned_build_id() -> String {
    let patch_sha = pin::patch_sha256();
    let patch_prefix = patch_sha.get(..12).unwrap_or(patch_sha);
    format!("{}-{patch_prefix}", pin::commit())
}

/// Every path a checker could be resolved from, in resolution order.
///
/// Pure in the environment: `env_get` is injected so the ordering and the
/// override rules can be tested without `set_var` (which is process-global and
/// racy under a threaded test runner).
///
/// An environment override that is set but does not name an existing file is a
/// hard `Err`, never a fall-through. A typo in `VERIPB_BIN` must never silently
/// degrade to "checker absent" — that would turn an operator mistake into a
/// sweep-wide `Unvalidated`, which reads like a checker outage.
pub(crate) fn candidate_paths(
    env_get: &dyn Fn(&str) -> Option<String>,
) -> Result<Vec<PathBuf>, String> {
    for var in CHECKER_ENV_VARS {
        match env_get(var) {
            // An explicitly empty override is how a caller unsets one variable
            // without unsetting the search; skip it rather than fail on it.
            Some(raw) if raw.is_empty() => continue,
            Some(raw) => {
                let candidate = PathBuf::from(raw);
                if candidate.is_file() {
                    return Ok(vec![candidate]);
                }
                return Err(format!(
                    "${var} is set to `{}`, which is not an existing file. Unset it or \
                     point it at the pinned VeriPB checker binary.",
                    candidate.display()
                ));
            }
            None => {}
        }
    }

    let mut candidates = Vec::new();
    if let Some(path) = env_get("PATH") {
        let executable = format!("veripb{}", std::env::consts::EXE_SUFFIX);
        if let Some(found) = std::env::split_paths(&path)
            .map(|directory| directory.join(&executable))
            .find(|candidate| candidate.is_file())
        {
            candidates.push(found);
        }
    }
    if let Some(raw) = env_get(SEARCH_PATH_ENV) {
        candidates.extend(std::env::split_paths(&raw));
        return Ok(candidates);
    }
    candidates.push(PathBuf::from("/tmp/veripb-3/bin/veripb"));
    let cache = env_get("XDG_CACHE_HOME")
        .map(PathBuf::from)
        .or_else(|| env_get("HOME").map(|home| PathBuf::from(home).join(".cache")));
    if let Some(cache) = cache {
        let cache = cache.join("ay-veripb");
        candidates.push(cache.join(pinned_build_id()).join("target/release/veripb"));
        // Compatibility with the original unkeyed cache populated by
        // scripts/cert_ci.sh. The pinned path above comes first: its directory
        // identity covers both the upstream commit and the reviewed patch.
        candidates.push(cache.join("VeriPB/target/release/veripb"));
    }
    if let Some(home) = env_get("HOME") {
        candidates.push(PathBuf::from(home).join(".cargo/bin/veripb"));
    }
    Ok(candidates)
}

/// First candidate that exists, or an error naming every path searched.
pub(crate) fn locate_with(env_get: &dyn Fn(&str) -> Option<String>) -> Result<PathBuf, String> {
    let candidates = candidate_paths(env_get)?;
    for candidate in &candidates {
        if candidate.is_file() {
            return Ok(candidate.clone());
        }
    }
    let searched: Vec<String> = candidates
        .iter()
        .map(|candidate| candidate.display().to_string())
        .collect();
    Err(format!(
        "no VeriPB checker found. Searched, in order: {}. Build the pinned checker \
         (scripts/ci/pb_certified_gate.sh), put `veripb` on PATH, or set VERIPB_BIN.",
        if searched.is_empty() {
            String::from("<nothing>")
        } else {
            searched.join(", ")
        }
    ))
}

/// [`locate_with`] over the real process environment.
pub(crate) fn locate() -> Result<PathBuf, String> {
    locate_with(&|key| std::env::var(key).ok())
}

/// The version string a checker reports, as the last whitespace-separated field
/// of the last `--version` line (`veripb 3.0.2` -> `3.0.2`).
///
/// Spawned through [`run_cert_probe`], not `Command::output()`: this runs while
/// the host-wide exclusive MaxSAT lease is held and must not be able to hang or
/// to buffer unbounded output.
///
/// BOUNDED at the source, by the same [`DETAIL_EXCERPT_MAX`] that bounds every
/// other checker-produced string this lane repeats. This is self-reported text
/// from an untrusted binary and it is interpolated into three places a human
/// reads — the startup warning, the `certificate lane:` banner and the JSON
/// report's `checker_version` — so capping it once here covers all three.
/// Observed: a checker printing 511-character lines.
fn reported_version(checker: &Path) -> Option<String> {
    let output = run_cert_probe(checker, &[OsStr::new("--version")]).ok()?;
    let text = output.stdout + &output.stderr;
    let field = text
        .lines()
        .filter(|line| !line.trim().is_empty())
        .next_back()?
        .split_whitespace()
        .next_back()?;
    Some(excerpt(field, DETAIL_EXCERPT_MAX))
}

/// Cross-check the resolved binary against the pinned version.
///
/// Deliberately NON-GATING: `ci/veripb.pin` says in as many words that
/// `--version` is not an identity ("3.0.2 has been many different checkers"),
/// so a version mismatch is a warning, not a refusal. The gate that matters is
/// [`self_test`], which asks the binary to behave like a checker rather than to
/// describe itself as one.
fn check_version(checker: &Path) -> Result<(), String> {
    let expected = pin::version();
    match reported_version(checker) {
        Some(actual) if actual == expected => Ok(()),
        Some(actual) => Err(format!(
            "`{}` reports VeriPB version `{actual}`, but {} pins `{expected}` (commit {}). \
             A verdict from an unpinned checker is weaker evidence than one from the pinned build.",
            checker.display(),
            pin::PIN_PATH,
            pin::commit()
        )),
        None => Err(format!(
            "`{}` printed no parseable `--version` output",
            checker.display()
        )),
    }
}

/// A two-variable PB optimisation instance whose optimum is exactly 1.
const SELF_TEST_OPB: &str =
    "* #variable= 2 #constraint= 1\nmin: +1 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n";
/// A genuine optimality certificate for it: a logged solution of cost 1, and a
/// lower bound of 1 hinted at input row 1 (which IS `obj >= 1`). Real VeriPB
/// answers `s VERIFIED BOUNDS 1 <= obj <= 1` and exits 0.
const SELF_TEST_GOOD_PBP: &str = "pseudo-Boolean proof version 3.0\nf 1 ;\nsol x1 ~x2 : 1 ;\noutput NONE;\nconclusion BOUNDS 1 : 1 1 : x1 ~x2 ;\nend pseudo-Boolean proof;\n";
/// A LIE about the same instance: `2 <= obj <= 2` claims the optimum is 2 when
/// it is 1. The upper half is honest (the witness `x1 x2` really does cost 2);
/// the LOWER bound is the lie, hinted at input row 1, which is `x1 + x2 >= 1`
/// and entails `obj >= 1`, not `obj >= 2`. Real VeriPB answers
/// `Expected constraint is not syntactically implied by the constraint at the
/// hint` and exits 1.
///
/// # Two properties this probe must have, and one it used to be missing
///
/// 1. **It must state something FALSE.** A probe that states a truth proves
///    nothing when a checker refuses it, and proves nothing when it accepts.
/// 2. **It must have the SHAPE the real emitter writes.** `maxsat_proof.rs`
///    always emits `conclusion BOUNDS <lb> : <hint-id> <ub> : <witness> ;`.
///    This probe used to omit the `: <hint-id>` field, and that made the whole
///    gate vacuous against `ci/fake-checkers/parrot.sh`: the parrot extracts
///    the upper bound positionally as `${6}`, so with the hint missing `${6}`
///    landed on a witness LITERAL and the parrot answered
///    `s VERIFIED BOUNDS 0 <= obj <= x1` — unparsable, therefore scored as a
///    refusal, therefore the parrot PASSED the anti-parrot probe. With the hint
///    present the parrot restates the lie verbatim as
///    `s VERIFIED BOUNDS 2 <= obj <= 2`, [`parse_verdict`] reads it as
///    `Verified`, and the probe fails it — which is the entire point of having
///    a false probe at all.
const SELF_TEST_FALSE_PBP: &str = "pseudo-Boolean proof version 3.0\nf 1 ;\nsol x1 x2 : 2 ;\noutput NONE;\nconclusion BOUNDS 2 : 1 2 : x1 x2 ;\nend pseudo-Boolean proof;\n";

fn scratch_dir(label: &str) -> PathBuf {
    // Hand-rolled because `tempfile` is a DEV-dependency of `ay`; same shape as
    // `cmd_submission.rs`'s `make_temp_dir`.
    static COUNTER: AtomicUsize = AtomicUsize::new(0);
    let serial = COUNTER.fetch_add(1, Ordering::Relaxed);
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|elapsed| elapsed.as_nanos())
        .unwrap_or(0);
    std::env::temp_dir().join(format!(
        "ay-maxsat-cert-{label}-{}-{serial}-{nanos}",
        std::process::id()
    ))
}

/// Prove that `checker` really is a proof checker, with two probes.
///
/// | probe | requirement | catches |
/// | --- | --- | --- |
/// | `cert-selftest-good` | verify a real optimality certificate, exit 0 | `/bin/false`, `/bin/true`, any silent binary, anything that always rejects |
/// | `cert-selftest-false` | REFUSE a certificate that claims a FALSE optimum, in the exact shape the real emitter writes | `/bin/true`, a rubber stamp, and `ci/fake-checkers/parrot.sh` — anything that merely restates the proof's own claim |
///
/// Both are required. Either alone is satisfiable by a one-line shell script,
/// and a lane whose only evidence is a binary that cannot fail is a lane that
/// checks nothing.
///
/// # Errors
/// A description of the first failed probe, naming the verdict and exit code
/// observed. Callers must treat it as fatal.
pub(crate) fn self_test(checker: &Path) -> Result<(), String> {
    let directory = scratch_dir("selftest");
    std::fs::create_dir_all(&directory)
        .map_err(|error| format!("cannot create self-test directory: {error}"))?;
    let opb = directory.join("selftest.opb");
    let result = (|| -> Result<(), String> {
        std::fs::write(&opb, SELF_TEST_OPB)
            .map_err(|error| format!("cannot write self-test formula: {error}"))?;

        let probe = |label: &str, proof_text: &str| -> Result<CertOutcome, String> {
            let pbp = directory.join(format!("{label}.pbp"));
            std::fs::write(&pbp, proof_text)
                .map_err(|error| format!("cannot write self-test proof: {error}"))?;
            // Bounded: a deadline, a process group, a capped capture. See
            // `run_cert_probe` — these spawns happen while the host-wide
            // exclusive MaxSAT lease is held.
            let output = run_cert_probe(
                checker,
                &[OsStr::new("--opb"), opb.as_os_str(), pbp.as_os_str()],
            )?;
            Ok(parse_verdict(output.code, &output.stdout, 1))
        };

        match probe("cert-selftest-good", SELF_TEST_GOOD_PBP)? {
            CertOutcome::Verified { lower: 1, upper: 1 } => {}
            other => {
                return Err(format!(
                    "probe `cert-selftest-good`: it did not answer \
                     `s VERIFIED BOUNDS 1 <= obj <= 1` with exit 0 ({other}); \
                     it cannot be a working checker"
                ))
            }
        }
        match probe("cert-selftest-false", SELF_TEST_FALSE_PBP)? {
            CertOutcome::Verified { .. } => Err(String::from(
                "probe `cert-selftest-false`: it ACCEPTED a certificate claiming an optimum \
                 of 2 for an instance whose optimum is 1; it is restating the proof's own \
                 claim rather than checking it, and it cannot be a sound checker",
            )),
            _ => Ok(()),
        }
    })();
    let _ = std::fs::remove_dir_all(&directory);
    result
}

// ---------------------------------------------------------------------------
// Verdicts
// ---------------------------------------------------------------------------

/// What the checker said about one emitted certificate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum CertOutcome {
    /// The checker accepted, under FULL guarantees, with a real BOUNDS
    /// conclusion.
    Verified { lower: u64, upper: u64 },
    /// The checker ran and did not accept. A soundness alarm.
    Rejected(String),
    /// No verdict could be obtained at all. Not evidence either way.
    Unusable(String),
}

impl std::fmt::Display for CertOutcome {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Verified { lower, upper } => write!(f, "verified {lower} <= obj <= {upper}"),
            Self::Rejected(why) => write!(f, "rejected: {why}"),
            Self::Unusable(why) => write!(f, "unusable: {why}"),
        }
    }
}

const VERDICT_PREFIX: &str = "s ";
const VERIFIED_STATUS: &str = "VERIFIED";
/// VeriPB's guarantee token when deletions were not checked: `veripb -u` prints
/// `s UNDER WEAKENED GUARANTEES BOUNDS <lo> <= obj <= <hi>` and exits 0. We
/// never ask for weakening, so seeing it means the run was not the run we
/// requested.
const WEAKENED_STATUS: &str = "UNDER WEAKENED GUARANTEES";

/// Longest checker-produced text that may be interpolated into a bench row's
/// `detail`. A row's detail is copied into the summary and into the JSON
/// report; a checker that dumps a megabyte on one line must not be able to make
/// either unreadable, and the two halves (verdict line, stderr excerpt) are
/// bounded identically so neither can swamp the other.
pub(crate) const DETAIL_EXCERPT_MAX: usize = 240;

/// The guarantee level a verdict line was issued at.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Guarantee {
    /// `s VERIFIED ...` — every step, deletions included, was checked.
    Full,
    /// `s UNDER WEAKENED GUARANTEES ...` — deletion steps were trusted.
    Weakened,
}

/// `body` with `token` stripped, when `token` is a whole leading word.
///
/// `s VERIFIEDX ...` is not `s VERIFIED X ...`.
fn strip_status<'a>(body: &'a str, token: &str) -> Option<&'a str> {
    let rest = body.strip_prefix(token)?;
    (rest.is_empty() || rest.starts_with(char::is_whitespace)).then(|| rest.trim())
}

/// Read the checker's verdict.
///
/// Acceptance requires BOTH halves of the contract, for the reasons
/// `ay-test-support/src/veripb.rs` documents at length:
///
/// * exit code 0 — a correct-looking verdict from a run that crashed, was
///   killed, or failed after printing is not evidence that the check finished
///   (`ci/fake-checkers/verdict-then-exit1.sh` is exactly that);
/// * the FIRST `s ` line reading `s VERIFIED BOUNDS <lo> <= obj <= <hi>` — exit
///   0 alone is satisfied by `/usr/bin/true`, and `s VERIFIED NO CONCLUSION`
///   (a proof that concluded nothing) is printed with exit 0 too.
///
/// The scan is over `s `-prefixed lines only, never `stdout.contains(...)`. A
/// `c` comment line mentioning VERIFIED must not accept; the substring form is
/// a live defect in `ay-pb/src/veripb_runner.rs`.
///
/// # `Rejected` vs `Unusable`: contradiction versus non-confirmation
///
/// [`CertOutcome::Rejected`] becomes `RunStatus::Wrong` — this harness saying
/// AY GAVE A WRONG ANSWER. `Wrong` must mean THE CHECKER ACTIVELY CONTRADICTED
/// AY; it must never mean the checker merely failed to confirm AY. That
/// accusation needs positive evidence, and the pinned checker does not always
/// supply it. Measured against
/// `~/.cache/ay-veripb/<pin>/target/release/veripb`, ALL FOUR of
///
/// * a genuinely false conclusion,
/// * a `.pbp` that does not exist,
/// * a truncated `.opb`,
/// * a truncated `.pbp`,
///
/// print exactly `Running VeriPB version 3.0.2` on stdout — no `s ` line at all
/// — diagnose themselves on stderr, and exit 1. A refusal and a crash are
/// therefore INDISTINGUISHABLE from stdout, and the stderr shapes overlap too
/// (`Error: Checking error at <file>:<line>` is printed both for a false
/// conclusion and for a truncated formula). So this reader emits exactly ONE
/// `Rejected`, and everything else that is not a readable acceptance is
/// `Unusable`:
///
/// * **no `s ` line, or a non-zero exit** -> [`CertOutcome::Unusable`]. We have
///   no verdict. `Unusable` lands the row in `Unvalidated`: unscored, and
///   `bench_exit_code` already fails the sweep on it, so a real refusal is
///   still loud — it just is not dressed up as a proven wrong answer.
/// * **exit 0 and an `s ` line whose status token is not an acceptance**
///   (`s NOT VERIFIED`) -> `Rejected`. THE POSITIVE EVIDENCE: the checker ran
///   to completion and chose to REFUSE the proof AY emitted. That refutes a
///   claim AY made. It does not discriminate a wrong answer from a broken
///   emitter — but both of those are AY's, which is what `Wrong` records.
/// * **exit 0, an acceptance token, but no readable `BOUNDS` interval**
///   (`s VERIFIED NO CONCLUSION`, a bare `s VERIFIED`, `s VERIFIED
///   SATISFIABLE`, `s VERIFIED UNSATISFIABLE`, an unparsable interval)
///   -> `Unusable`. Measured: real veripb 3.0.2 prints
///   `s VERIFIED NO CONCLUSION` with exit 0 for a proof that concludes
///   nothing. A VACUOUS proof establishes nothing, so it contradicts nothing,
///   so it cannot accuse AY — and the conclusion TYPE is dictated by the proof
///   `crate::maxsat_proof` wrote, never by the checker, so a non-`BOUNDS`
///   acceptance is a statement about OUR emitter rather than about AY's answer.
/// * **exit 0 and a WEAKENED `BOUNDS` interval** -> `Unusable`: an accepted
///   run, but not the run we asked for.
///
/// `reported_cost` is not part of the acceptance test — comparing the certified
/// upper bound against what the solver claimed is [`classify_certificate`]'s
/// job — but it is carried into the message, because "no verdict" without
/// "while the solver claimed N" is not actionable evidence.
pub(crate) fn parse_verdict(
    exit_code: Option<i32>,
    stdout: &str,
    reported_cost: u64,
) -> CertOutcome {
    let Some(line) = stdout
        .lines()
        .map(str::trim_end)
        .find(|line| line.starts_with(VERDICT_PREFIX))
    else {
        return CertOutcome::Unusable(format!(
            "checker printed no `s ...` verdict line (exit {exit_code:?}), which this checker \
             does for a refusal AND for a crash alike; solver reported cost {reported_cost}"
        ));
    };
    // Bounded before it reaches any message: the row detail this ends up in is
    // capped the same way the stderr excerpt beside it is.
    let verdict = excerpt(line, DETAIL_EXCERPT_MAX);
    if exit_code != Some(0) {
        return CertOutcome::Unusable(format!(
            "checker exited {exit_code:?} while printing `{verdict}`; \
             a verdict from a run that did not finish is not a verdict"
        ));
    }
    let body = line.trim_start_matches(VERDICT_PREFIX).trim();
    let (guarantee, conclusion) = if let Some(rest) = strip_status(body, VERIFIED_STATUS) {
        (Guarantee::Full, rest)
    } else if let Some(rest) = strip_status(body, WEAKENED_STATUS) {
        (Guarantee::Weakened, rest)
    } else {
        // THE ONLY `Rejected` this reader can produce, and the only one that
        // may accuse AY. Positive evidence: exit 0 (the run finished) AND a
        // verdict line whose status token is a REFUSAL of the proof.
        return CertOutcome::Rejected(format!("checker answered `{verdict}`"));
    };
    // An acceptance without the interval we asked about is NOT a refusal. A
    // bare `s VERIFIED`, `s VERIFIED NO CONCLUSION` (measured: real veripb
    // 3.0.2, exit 0, for a proof concluding nothing), `s VERIFIED SATISFIABLE`
    // and `s VERIFIED UNSATISFIABLE` all land here, and none of them
    // contradicts the reported cost: the conclusion type is whatever OUR
    // emitter wrote into the `.pbp`, so this is evidence about emission, not
    // about the answer.
    let Some(interval) = conclusion.strip_prefix("BOUNDS ") else {
        return CertOutcome::Unusable(format!(
            "checker answered `{verdict}` — that establishes no interval over the objective, \
             so it neither confirms nor contradicts the reported cost {reported_cost}"
        ));
    };
    // `<lower> <= obj <= <upper>`, exactly five fields.
    let fields: Vec<&str> = interval.split_whitespace().collect();
    if fields.len() != 5 || fields[1] != "<=" || fields[2] != "obj" || fields[3] != "<=" {
        return CertOutcome::Unusable(format!(
            "checker answered `{verdict}`, a BOUNDS verdict this reader cannot parse"
        ));
    }
    match (fields[0].parse::<u64>(), fields[4].parse::<u64>()) {
        // THE weakened guard, and it is load-bearing exactly here: the line has
        // just parsed as a perfectly good interval, so without this arm
        // `s UNDER WEAKENED GUARANTEES BOUNDS 2 <= obj <= 2` — which is what
        // `veripb -u` really prints, with exit 0 — would be accepted as a full
        // verification. It is not a refusal (the checker accepted); it is a
        // check we did not ask for and did not get, so it is Unusable.
        (Ok(_), Ok(_)) if guarantee == Guarantee::Weakened => CertOutcome::Unusable(format!(
            "checker answered `{verdict}` — that is a WEAKENED verdict (deletions unchecked) \
             and we never asked for one; the run we requested did not happen"
        )),
        (Ok(lower), Ok(upper)) => CertOutcome::Verified { lower, upper },
        _ => CertOutcome::Unusable(format!("checker answered `{verdict}` (non-integer bounds)")),
    }
}

// ---------------------------------------------------------------------------
// Arming
// ---------------------------------------------------------------------------

/// Whether, and where, this instance gets a certificate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum CertArm {
    /// `--proof-check` absent, or an external solver (which has no `--proof`
    /// to offer).
    Off,
    /// Certification deliberately declined for this instance. The reason is
    /// user-facing and is repeated verbatim in the row's authority string, so a
    /// skip can never be mistaken for a verified row.
    Skipped(String),
    /// Emit to `<stem>.opb` / `<stem>.opb.pbp` and check it.
    Armed { stem: PathBuf },
}

/// Sanitise an instance name into a filename component.
///
/// EVERY byte outside `[A-Za-z0-9_-]` becomes `_`, including `.`: emission does
/// `stem.with_extension("opb")` (`maxsat_proof.rs`), which would otherwise eat a
/// `.wcnf` suffix and let `a.wcnf` and `a.opb` collide on the same stem.
fn sanitise(name: &str) -> String {
    name.chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' || c == '-' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

/// Decide this instance's certificate arm. Called once per row, before spawn.
pub(crate) fn arm_certificate(
    plan: Option<&CertPlan>,
    external: bool,
    file: &Path,
    instance: &str,
) -> CertArm {
    let Some(plan) = plan else {
        return CertArm::Off;
    };
    if external {
        // A `--solver NAME=CMD` command line is the operator's, not ours; there
        // is no `--proof` to append to it and appending flags to a third-party
        // invocation would change what is being benchmarked.
        return CertArm::Off;
    }
    if plan.max_instance_bytes > 0 {
        // Measured expansion, on disk, per armed row: a 43,020,161-byte `.wcnf`
        // becomes a 71,989,226-byte `.opb` plus a 7,059,974-byte `.pbp` — 1.84x
        // the instance, not "roughly its size". The checker's RSS is not in
        // `MaxSatResources::plan` either — it borrows the solver's slot after
        // the solver exits. Stat is cheap and the bench worker already stats
        // this file for the giant gate.
        match std::fs::metadata(file) {
            Ok(metadata) if metadata.len() > plan.max_instance_bytes => {
                return CertArm::Skipped(format!(
                    "instance {} MiB exceeds --proof-max-instance-mib {}",
                    metadata.len() / (1024 * 1024),
                    plan.max_instance_bytes / (1024 * 1024)
                ));
            }
            Ok(_) => {}
            Err(error) => {
                // Cannot size it, so cannot honour the cap. Declining is the
                // fail-closed branch and it is annotated; guessing "small" is
                // how a 36MB artifact lands on a machine under memory pressure.
                return CertArm::Skipped(format!("cannot size instance: {error}"));
            }
        }
    }
    let seq = plan.seq.fetch_add(1, Ordering::Relaxed);
    CertArm::Armed {
        stem: plan.dir.join(format!("{seq:05}-{}", sanitise(instance))),
    }
}

/// The two files emission writes for `stem`, exactly as `maxsat_proof.rs`
/// names them.
pub(crate) fn artifact_paths(stem: &Path) -> (PathBuf, PathBuf) {
    let opb = stem.with_extension("opb");
    let pbp = {
        let mut path = opb.clone().into_os_string();
        path.push(".pbp");
        PathBuf::from(path)
    };
    (opb, pbp)
}

/// Confirm emission actually produced something before spending a checker slot
/// on it.
///
/// This is the branch that catches an emission failure. Emission's only current
/// signal is an `eprintln!` on the child's stderr, and the bench harness nulls
/// the child's stderr — so a certificate that was never written would otherwise
/// look exactly like one the checker refused to read.
pub(crate) fn precheck_artifacts(opb: &Path, pbp: &Path) -> Option<CertOutcome> {
    for path in [opb, pbp] {
        match std::fs::metadata(path) {
            Ok(metadata) if metadata.len() > 0 => {}
            Ok(_) => {
                return Some(CertOutcome::Unusable(format!(
                    "solver reported OPTIMUM but wrote an empty `{}`",
                    path.display()
                )))
            }
            Err(_) => {
                return Some(CertOutcome::Unusable(format!(
                    "solver reported OPTIMUM but wrote no certificate (`{}` is missing)",
                    path.display()
                )))
            }
        }
    }
    None
}

/// Trim `text` to a single-line excerpt suitable for a bench row's `detail`.
pub(crate) fn excerpt(text: &str, max: usize) -> String {
    let flat: String = text
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .collect::<Vec<_>>()
        .join(" | ");
    if flat.chars().count() <= max {
        flat
    } else {
        let head: String = flat.chars().take(max).collect();
        format!("{head}...")
    }
}

// ---------------------------------------------------------------------------
// The fold
// ---------------------------------------------------------------------------

/// Where a checker-verified interval leaves the cost the solver reported.
///
/// Shared by [`classify_certificate`] and [`CertPlan::record`] so the verdict a
/// row is scored with and the count printed in the summary cannot drift apart.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CostVerdict {
    /// `lower == cost == upper`: optimality itself was checked.
    Closed,
    /// `upper == cost` with `lower < cost`: the ANSWER was checked, optimality
    /// was not.
    UpperCertified,
    /// `lower <= cost < upper`: consistent with the answer, but weaker than it,
    /// so it confirms nothing about it.
    NotPinned,
    /// `cost` lies OUTSIDE the verified interval — the checker proved something
    /// the reported cost cannot coexist with.
    Contradicted,
    /// The checker reported `lower > upper`, which no formula can satisfy. That
    /// is evidence about the CHECKER, so it must not convict AY.
    Malformed,
}

fn cost_verdict(lower: u64, upper: u64, cost: u64) -> CostVerdict {
    if lower > upper {
        // A self-contradictory interval is a malfunctioning checker, not a
        // wrong answer by AY. `cost` is outside it for EVERY cost, so the
        // `Contradicted` arm below would convict on arithmetic that cannot be
        // satisfied — the same "did not confirm" vs "actively contradicted"
        // error N1 removed from the vacuous-proof path.
        CostVerdict::Malformed
    } else if cost < lower || cost > upper {
        CostVerdict::Contradicted
    } else if upper != cost {
        CostVerdict::NotPinned
    } else if lower == cost {
        CostVerdict::Closed
    } else {
        CostVerdict::UpperCertified
    }
}

/// #bench-cert: fold a certificate outcome into a row that was ALREADY going to
/// be `RunStatus::Optimum`.
///
/// Never-upgrade is STRUCTURAL, not a convention. This function takes no status
/// in; its only caller is the single `RunStatus::Optimum` construction site in
/// `cmd_maxsat.rs`, reached only after the wall-clock demotion, the missing
/// `o`-line check, the reference-field check and `verify_model` have all
/// passed; and every arm below returns `Optimum`, `Unvalidated` or `Wrong` —
/// never anything above the pre-state. The `UNSATISFIABLE` arm and the
/// fallthrough arm of the caller contain no certificate code at all, so no
/// Timeout / Memout / Error / Unvalidated row is reachable from here.
///
/// Same rule, mirrored, as `crate::maxsat_proof`'s write-only emitter.
///
/// `base_authority` is the caller's existing 2x2 provenance string. Every arm
/// either returns it unchanged or EXTENDS it: a certified row still says which
/// model verifier and which reference field backed it, because "VeriPB-certified"
/// on its own would be a narrower claim than the row actually carries.
///
/// # The two paths to `RunStatus::Wrong`, and the evidence each requires
///
/// 1. `CostVerdict::Contradicted` — the checker verified an interval that
///    EXCLUDES the cost AY reported. `cost > upper` means a better solution was
///    proven to exist, so the reported optimum is not optimal; `cost < lower`
///    means no solution that cheap can exist, so the reported model cannot
///    cost what AY said. Either way the checker's own verified statement and
///    AY's `o` line cannot both hold.
/// 2. `CertOutcome::Rejected` — a completed checker run (exit 0) that REFUSED
///    the proof. See [`parse_verdict`]: that is the one verdict shape which
///    refutes a claim AY made, and it is the only `Rejected` this lane emits.
///
/// Nothing else may reach `Wrong`. In particular a verified interval that
/// merely CONTAINS the reported cost without pinning it
/// (`CostVerdict::NotPinned`) is consistent with AY and confirms nothing, so it
/// is `Unvalidated` — "the checker did not confirm AY" is never an accusation.
pub(crate) fn classify_certificate(
    arm: &CertArm,
    outcome: Option<&CertOutcome>,
    cost: u64,
    base_authority: &str,
) -> (RunStatus, String, String) {
    match arm {
        CertArm::Off => (
            RunStatus::Optimum,
            String::new(),
            base_authority.to_string(),
        ),
        CertArm::Skipped(why) => (
            RunStatus::Optimum,
            format!("certificate skipped: {why}"),
            format!("{base_authority}; certificate skipped ({why})"),
        ),
        CertArm::Armed { .. } => match outcome {
            Some(CertOutcome::Verified { lower, upper }) => {
                match cost_verdict(*lower, *upper, cost) {
                    CostVerdict::Closed => (
                        RunStatus::Optimum,
                        format!("veripb: closed {lower} <= obj <= {upper}"),
                        format!("{base_authority} + VeriPB-certified optimality"),
                    ),
                    // A checked upper bound is real evidence — the model and
                    // its cost were both recomputed by the checker — but the
                    // interval does not entail optimality, and saying so is the
                    // difference between certifying an answer and certifying a
                    // claim about it.
                    CostVerdict::UpperCertified => (
                        RunStatus::Optimum,
                        format!("veripb: {lower} <= obj <= {upper} (lb not closed)"),
                        format!(
                            "{base_authority} + VeriPB-certified upper bound (lb {lower} not closed)"
                        ),
                    ),
                    // The interval CONTAINS the reported cost but is weaker
                    // than the claim: consistent with AY, and no confirmation
                    // of it. Not confirming is not contradicting, so this may
                    // not accuse anyone.
                    CostVerdict::NotPinned => (
                        RunStatus::Unvalidated,
                        format!(
                            "certificate does not pin the answer: veripb verified \
                             {lower} <= obj <= {upper}, solver reported {cost}"
                        ),
                        String::from(
                            "proof requested; certificate does not pin the answer (unvalidated)",
                        ),
                    ),
                    // THE wrong-answer detector the whole lane exists for: the
                    // checker's verified interval EXCLUDES the cost AY printed,
                    // so the `o` line and the certificate cannot both hold.
                    CostVerdict::Malformed => (
                        RunStatus::Unvalidated,
                        format!(
                            "checker reported the impossible interval {lower} <= obj <= {upper}; \
                             treating as unusable rather than convicting the solver"
                        ),
                        String::from("certificate requested; checker malfunctioned (unvalidated)"),
                    ),
                    CostVerdict::Contradicted => (
                        RunStatus::Wrong,
                        format!(
                            "certificate verifies {lower} <= obj <= {upper}, which excludes the \
                             reported cost {cost}"
                        ),
                        String::from("veripb certificate checker"),
                    ),
                }
            }
            // A completed checker run that REFUSED the proof — the one verdict
            // shape that refutes a claim AY made. See `parse_verdict`.
            Some(CertOutcome::Rejected(why)) => (
                RunStatus::Wrong,
                format!("certificate REJECTED: {why}"),
                String::from("veripb certificate checker"),
            ),
            Some(CertOutcome::Unusable(why)) => (
                // Not evidence of a wrong answer, and not evidence of a right
                // one either. `Unvalidated` is not scored and already forces a
                // non-zero bench exit code, so this cannot be mistaken for a
                // pass — while a lost checker does not throw away the sweep.
                RunStatus::Unvalidated,
                format!("certificate not checked: {why}"),
                String::from("proof requested; checker unusable (unvalidated)"),
            ),
            None => (
                // Defensive: an armed row with no outcome means the caller
                // skipped the check without saying so. Treat it as unchecked
                // rather than as verified.
                RunStatus::Unvalidated,
                String::from("certificate not checked: no verdict was obtained"),
                String::from("proof requested; checker unusable (unvalidated)"),
            ),
        },
    }
}

// ---------------------------------------------------------------------------
// Artifact lifecycle
// ---------------------------------------------------------------------------

/// RAII net for the certificate artifacts of ONE bench row.
///
/// `run_one` has ~15 early returns (memout, watchdog failure, lease loss, late
/// finish, capture overflow, ...), and emission ALSO runs on the anytime path —
/// a `s UNKNOWN` with an incumbent writes a full `.opb`. Without this guard a
/// 3600s sweep, most of whose rows time out with an incumbent, would leave one
/// multi-MB artifact per row on disk: the 17GB failure mode, reached without a
/// single certificate ever being checked. Dropping this deletes them;
/// [`CertPlan::retain_or_delete`] calls [`keep`](Self::keep) on the rows whose
/// VERDICT makes their artifacts evidence.
pub(crate) struct CertArtifacts {
    paths: Option<(PathBuf, PathBuf)>,
    keep: bool,
    /// Set when a PRE-EXISTING artifact could not be unlinked; see
    /// [`for_arm`](Self::for_arm).
    stale: Option<String>,
}

impl CertArtifacts {
    /// Bind these paths to THIS run, by unlinking whatever is already there.
    ///
    /// Stems are `<seq:05>-<instance>` and `seq` restarts at 0 in every
    /// process, so a reused `--proof-dir` at `--jobs 1` — a fully deterministic
    /// ordering — hands row N of this sweep exactly the filenames row N of the
    /// previous sweep wrote. Left alone, [`precheck_artifacts`] would accept
    /// that stale pair (it only asks whether the files exist and are non-empty)
    /// and the checker would certify a PREVIOUS run's answer against THIS run's
    /// cost. That is a false `RunStatus::Wrong`: the worst verdict this lane can
    /// emit, produced from an artifact this run never wrote.
    ///
    /// So the pair is unlinked here, before the solver child is spawned — which
    /// also covers the spawn-failed and killed-before-emission paths, since
    /// after this point a file at either path can only have been written by
    /// this row's child. A pair that will NOT unlink is recorded and surfaced
    /// as `Unusable` rather than checked, because the binding is what makes the
    /// check attributable at all.
    pub(crate) fn for_arm(arm: &CertArm) -> Self {
        let paths = match arm {
            CertArm::Armed { stem } => Some(artifact_paths(stem)),
            CertArm::Off | CertArm::Skipped(_) => None,
        };
        let mut stale = None;
        if let Some((opb, pbp)) = &paths {
            for path in [opb, pbp] {
                match std::fs::remove_file(path) {
                    Ok(()) => {}
                    Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                    Err(error) => {
                        stale.get_or_insert(format!(
                            "`{}` predates this run and could not be removed ({error}), so a \
                             certificate found there cannot be attributed to this row",
                            path.display()
                        ));
                    }
                }
            }
        }
        Self {
            paths,
            keep: false,
            stale,
        }
    }

    pub(crate) fn paths(&self) -> Option<(&Path, &Path)> {
        self.paths
            .as_ref()
            .map(|(opb, pbp)| (opb.as_path(), pbp.as_path()))
    }

    /// The outcome to use INSTEAD of checking, when this row's artifact paths
    /// could not be bound to this run.
    pub(crate) fn stale(&self) -> Option<CertOutcome> {
        self.stale.clone().map(CertOutcome::Unusable)
    }

    /// Retain these artifacts past the end of the row (failure evidence).
    pub(crate) fn keep(&mut self) {
        self.keep = true;
    }

    /// Keep this row's artifacts iff the verdict it ended up with makes them
    /// evidence, subject to [`CertPlan::retain_or_delete`]'s caps.
    ///
    /// `run_one` reaches `RunStatus::Wrong` from FIVE detectors — a missing
    /// `o` line, a reference optimum that disagrees, a model that fails
    /// re-evaluation, an UNSAT claim against a feasible reference, and the
    /// certificate fold itself — and only the last of those reaches the fold.
    /// The other four `return` early, so without this call their artifacts go
    /// out with `Drop` — deleting the evidence in exactly the rows where an
    /// independent authority contradicted AY. Calling it more often cannot
    /// over-retain: the caps and the `Wrong` reserve are enforced downstream,
    /// and a row with nothing on disk consumes no slot.
    pub(crate) fn retain_if_evidence(&mut self, plan: Option<&CertPlan>, status: RunStatus) {
        let retained = match (plan, self.paths()) {
            (Some(plan), Some((opb, pbp))) => plan.retain_or_delete(status, opb, pbp),
            _ => false,
        };
        if retained {
            self.keep();
        }
    }
}

impl Drop for CertArtifacts {
    fn drop(&mut self) {
        if self.keep {
            return;
        }
        if let Some((opb, pbp)) = &self.paths {
            let _ = std::fs::remove_file(opb);
            let _ = std::fs::remove_file(pbp);
        }
    }
}

// ---------------------------------------------------------------------------
// The plan
// ---------------------------------------------------------------------------

/// Hard caps on the failure evidence one sweep may leave on disk.
///
/// Retention used to be uncapped, keyed on "did this row fail". That is the
/// multi-GB blowup the lane was designed to avoid, because `Unusable` is a
/// SYSTEMIC per-sweep condition, not a per-row accident: a checker that was
/// deleted mid-sweep, or one that times out on every row, produces `Unusable`
/// for EVERY armed row, and at 1.84x the instance size that is the whole corpus
/// on disk — on a 24GB machine that has kernel-panicked twice. Meanwhile
/// `CertPlan::drop` refuses to reclaim the scratch directory once anything has
/// been retained, so nothing came back.
///
/// The evidence value of the 33rd identical failure is zero; its disk cost is
/// not. Both caps are hard, and hitting either is REPORTED in the summary and
/// in the JSON report — never silent, because "we stopped keeping evidence" is
/// itself something a reader has to know.
const RETAIN_MAX_ROWS: usize = 32;
/// Total bytes of retained `.opb` + `.pbp`, across the whole sweep.
const RETAIN_MAX_BYTES: u64 = 256 * 1024 * 1024;

/// The slice of both caps that ONLY a `RunStatus::Wrong` row may claim.
///
/// Retention used to be first-come-first-served across every non-`Optimum`
/// row, and that put the lane's whole purpose at the mercy of infrastructure
/// noise: `Unusable` is SYSTEMIC (a deleted checker, a checker that times out
/// or breaches RSS on every row, artifacts that never got written) and every
/// one of those rows is `Unvalidated`, so 32 of them arriving before the ONE
/// contradicted row evict nothing — they simply fill the budget, and the
/// evidence for the row this lane exists to catch is deleted on arrival.
///
/// A reservation fixes that without an eviction ledger: `Unvalidated` may spend
/// at most `RETAIN_MAX_* - RETAIN_WRONG_RESERVED_*`, so a `Wrong` row always
/// finds room however loud the sweep has been. `Wrong` itself is still bounded
/// by the full cap — the 33rd identical wrong answer is not worth 74MiB — and
/// hitting either bound is reported, never silent.
const RETAIN_WRONG_RESERVED_ROWS: usize = 8;
/// Bytes reserved the same way, and for the same reason.
///
/// This MUST exceed the largest artifact pair the size guard admits, or the
/// reserve cannot hold even one wrong-answer row and the row dimension above is
/// the only real protection. The guard admits an instance of
/// `PROOF_MAX_INSTANCE_MIB_DEFAULT` (40 MiB) and the measured `.opb` + `.pbp`
/// expansion is 1.84x, i.e. ~74 MiB for a single row — so 64 MiB, the first
/// value here, was already too small. 160 MiB holds two such pairs with margin
/// while leaving 96 MiB of the 256 MiB total for unvalidated noise.
const RETAIN_WRONG_RESERVED_BYTES: u64 = 160 * 1024 * 1024;

/// What the sweep has kept, and what it refused to keep.
#[derive(Debug, Default)]
struct Retention {
    rows: usize,
    bytes: u64,
    /// Rows whose artifacts were deleted because a cap was already reached.
    refused: usize,
}

/// Per-sweep certificate configuration, built once in `bench()` before the
/// first spawn and shared by every worker.
#[derive(Debug)]
pub(crate) struct CertPlan {
    /// The resolved, version-checked, self-tested checker.
    pub(crate) checker: PathBuf,
    /// What that binary reports for `--version` (recorded in the JSON report:
    /// a verdict from an unpinned checker is weaker evidence, and the report is
    /// where that identity has to live).
    pub(crate) checker_version: String,
    /// Where artifacts are written.
    pub(crate) dir: PathBuf,
    /// True when we created `dir` and may remove it.
    owned_dir: bool,
    /// Instances above this are skipped (0 = no cap).
    pub(crate) max_instance_bytes: u64,
    /// Wall-clock budget for one checker invocation.
    pub(crate) check_timeout: Duration,
    seq: AtomicUsize,
    verified: AtomicUsize,
    closed: AtomicUsize,
    skipped: AtomicUsize,
    rejected: AtomicUsize,
    unchecked: AtomicUsize,
    retention: Mutex<Retention>,
}

impl CertPlan {
    /// Resolve and PROVE the checker, then prepare the artifact directory.
    ///
    /// Every failure here is fatal to the sweep by design, and costs nothing:
    /// this runs before the first instance is spawned, so a bad `--proof-check`
    /// setup fails at t~=0.2s rather than after 473 solver-hours.
    pub(crate) fn new(
        dir: Option<&Path>,
        max_instance_mib: u64,
        check_timeout: Duration,
    ) -> Result<Self, String> {
        let checker = locate()?;
        // Non-gating: see check_version's doc. The pin itself says `--version`
        // is not an identity, so a mismatch is announced and the self-test
        // decides.
        let checker_version = match check_version(&checker) {
            Ok(()) => pin::version().to_string(),
            Err(why) => {
                safe_eprintln!("c WARNING[--proof-check]: {why}");
                reported_version(&checker).unwrap_or_else(|| String::from("<unknown>"))
            }
        };
        self_test(&checker).map_err(|why| {
            format!(
                "`{}` was resolved as the VeriPB checker but failed its self-test \
                 (a real checker must verify a known-good certificate and refuse a \
                 known-bad one): {why}",
                checker.display()
            )
        })?;

        let (dir, owned_dir) = match dir {
            Some(dir) => (dir.to_path_buf(), false),
            None => (scratch_dir("sweep"), true),
        };
        std::fs::create_dir_all(&dir).map_err(|error| {
            format!(
                "cannot create certificate directory `{}`: {error}",
                dir.display()
            )
        })?;

        Ok(Self {
            checker,
            checker_version,
            dir,
            owned_dir,
            max_instance_bytes: max_instance_mib.saturating_mul(1024 * 1024),
            check_timeout,
            seq: AtomicUsize::new(0),
            verified: AtomicUsize::new(0),
            closed: AtomicUsize::new(0),
            skipped: AtomicUsize::new(0),
            rejected: AtomicUsize::new(0),
            unchecked: AtomicUsize::new(0),
            retention: Mutex::new(Retention::default()),
        })
    }

    /// Tally one row for the summary line and the JSON report.
    ///
    /// Counting only, with no influence on any verdict: `classify_certificate`
    /// has already decided the row by the time this runs.
    pub(crate) fn record(&self, arm: &CertArm, outcome: Option<&CertOutcome>, cost: u64) {
        let bump = |counter: &AtomicUsize| {
            counter.fetch_add(1, Ordering::Relaxed);
        };
        match arm {
            CertArm::Off => {}
            CertArm::Skipped(_) => bump(&self.skipped),
            CertArm::Armed { .. } => match outcome {
                // Same `cost_verdict` the fold used, so the tally cannot say
                // "verified" about a row the fold scored `Wrong`.
                Some(CertOutcome::Verified { lower, upper }) => {
                    match cost_verdict(*lower, *upper, cost) {
                        CostVerdict::Closed => {
                            bump(&self.verified);
                            bump(&self.closed);
                        }
                        CostVerdict::UpperCertified => bump(&self.verified),
                        CostVerdict::NotPinned => bump(&self.unchecked),
                        // A verified interval that excludes the reported cost is
                        // a rejection of the ANSWER, so it counts as one.
                        CostVerdict::Contradicted => bump(&self.rejected),
                        // A malfunctioning checker established nothing.
                        CostVerdict::Malformed => bump(&self.unchecked),
                    }
                }
                Some(CertOutcome::Rejected(_)) => bump(&self.rejected),
                Some(CertOutcome::Unusable(_)) | None => bump(&self.unchecked),
            },
        }
    }

    /// Keep this row's artifacts iff its VERDICT makes them evidence AND the
    /// retention caps still allow it. Returns `true` when they were kept.
    ///
    /// # Why the verdict and not the outcome variant
    ///
    /// This used to key on [`CertOutcome`], and that deleted the evidence for
    /// the one case the lane exists to catch: `Verified { upper }` with
    /// `upper != cost` is the checker and the solver disagreeing about the
    /// ANSWER, [`classify_certificate`] scores it `RunStatus::Wrong`, and the
    /// `Verified` arm unlinked both files on the way out. Keying on the status
    /// the row actually ended up with cannot get that wrong: every non-`Optimum`
    /// verdict keeps its artifacts, and `Optimum` — including a certified one
    /// and a deliberately skipped one — keeps nothing, because its verdict is
    /// already in the row and nobody will ever open the files.
    ///
    /// # Why the caps, and why `Wrong` gets a reserve
    ///
    /// See [`RETAIN_MAX_ROWS`] and [`RETAIN_WRONG_RESERVED_ROWS`]. A cap that
    /// has been hit is recorded and reported; retention is never silently
    /// abandoned.
    pub(crate) fn retain_or_delete(&self, status: RunStatus, opb: &Path, pbp: &Path) -> bool {
        let size = |path: &Path| std::fs::metadata(path).map_or(0, |meta| meta.len());
        // Nothing on disk is nothing to retain, and it must not consume a slot:
        // `precheck_artifacts` yields `Unusable` precisely when these files are
        // absent or empty, which is the commonest Unusable of all.
        let bytes = size(opb).saturating_add(size(pbp));
        let keep =
            status != RunStatus::Optimum && bytes > 0 && self.reserve_retention(status, bytes);
        if !keep {
            for path in [opb, pbp] {
                // NotFound is tolerated: emission may legitimately not have run.
                let _ = std::fs::remove_file(path);
            }
        }
        keep
    }

    /// Charge `bytes` against the retention caps, or refuse.
    ///
    /// A non-`Wrong` row is held to the SMALLER budget, which is what keeps the
    /// reserve intact: `Unvalidated` can never push the ledger past
    /// `RETAIN_MAX_* - RETAIN_WRONG_RESERVED_*`, so a `Wrong` row arriving last
    /// still finds the reserve untouched.
    fn reserve_retention(&self, status: RunStatus, bytes: u64) -> bool {
        let (max_rows, max_bytes) = if status == RunStatus::Wrong {
            (RETAIN_MAX_ROWS, RETAIN_MAX_BYTES)
        } else {
            (
                RETAIN_MAX_ROWS - RETAIN_WRONG_RESERVED_ROWS,
                RETAIN_MAX_BYTES - RETAIN_WRONG_RESERVED_BYTES,
            )
        };
        // A poisoned ledger means a worker panicked mid-accounting. Reading
        // through the poison and continuing to enforce is the fail-closed side:
        // the worst it can do is delete artifacts, never over-retain them.
        let mut ledger = self
            .retention
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if ledger.rows >= max_rows || ledger.bytes.saturating_add(bytes) > max_bytes {
            ledger.refused += 1;
            return false;
        }
        ledger.rows += 1;
        ledger.bytes = ledger.bytes.saturating_add(bytes);
        true
    }

    fn ledger(&self) -> Retention {
        let ledger = self
            .retention
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        Retention {
            rows: ledger.rows,
            bytes: ledger.bytes,
            refused: ledger.refused,
        }
    }

    pub(crate) fn verified(&self) -> usize {
        self.verified.load(Ordering::Relaxed)
    }

    pub(crate) fn closed(&self) -> usize {
        self.closed.load(Ordering::Relaxed)
    }

    pub(crate) fn skipped(&self) -> usize {
        self.skipped.load(Ordering::Relaxed)
    }

    pub(crate) fn rejected(&self) -> usize {
        self.rejected.load(Ordering::Relaxed)
    }

    pub(crate) fn unchecked(&self) -> usize {
        self.unchecked.load(Ordering::Relaxed)
    }

    /// Rows whose artifacts survive the sweep as failure evidence.
    pub(crate) fn retained(&self) -> usize {
        self.ledger().rows
    }

    /// Bytes those artifacts occupy. Bounded by [`RETAIN_MAX_BYTES`].
    pub(crate) fn retained_bytes(&self) -> u64 {
        self.ledger().bytes
    }

    /// Failing rows whose artifacts were DELETED because a retention cap had
    /// already been reached. Non-zero means evidence was dropped, and the
    /// summary says so.
    pub(crate) fn retention_refused(&self) -> usize {
        self.ledger().refused
    }

    /// The caps, for the message that reports them: total rows, total bytes,
    /// and the rows/bytes of that total which only a `Wrong` row may claim.
    /// The summary prints all four, because a reader told only the headline cap
    /// would mis-read an `Unvalidated` row refused at the smaller budget.
    pub(crate) const fn retention_caps() -> (usize, u64, usize, u64) {
        (
            RETAIN_MAX_ROWS,
            RETAIN_MAX_BYTES,
            RETAIN_WRONG_RESERVED_ROWS,
            RETAIN_WRONG_RESERVED_BYTES,
        )
    }
}

impl Drop for CertPlan {
    fn drop(&mut self) {
        // Same shape as `cmd_launch.rs`'s `TempDirCleanup`, with one extra
        // condition: retained artifacts are failure evidence, so a directory
        // holding any of them survives the sweep. That survival is bounded by
        // the retention caps — without them this branch is what turned a bad
        // sweep into a permanent multi-GB residue. A user-supplied --proof-dir
        // is never removed: we did not create it and may not own it.
        if self.owned_dir && self.retained() == 0 {
            let _ = std::fs::remove_dir_all(&self.dir);
        }
    }
}

#[cfg(test)]
#[allow(clippy::panic, clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::*;
    use crate::cmd_maxsat::{
        bench_exit_code, scoring_solved, summarize_bench, RunResult, RunStatus,
    };

    const BASE: &str = "reference optimum + independently verified model";

    fn env_from(pairs: &[(&str, &str)]) -> impl Fn(&str) -> Option<String> {
        let owned: Vec<(String, String)> = pairs
            .iter()
            .map(|(k, v)| ((*k).to_string(), (*v).to_string()))
            .collect();
        move |key: &str| {
            owned
                .iter()
                .find(|(name, _)| name == key)
                .map(|(_, value)| value.clone())
        }
    }

    fn scratch(label: &str) -> PathBuf {
        let dir = scratch_dir(label);
        std::fs::create_dir_all(&dir).expect("mkdir");
        dir
    }

    /// A plan that owns nothing and checks nothing: enough to exercise the
    /// arming rules and the retention ledger.
    fn test_plan(dir: &Path) -> CertPlan {
        CertPlan {
            checker: PathBuf::from("/nonexistent/veripb"),
            checker_version: String::from("3.0.2"),
            dir: dir.to_path_buf(),
            owned_dir: false,
            max_instance_bytes: 0,
            check_timeout: Duration::from_secs(60),
            seq: AtomicUsize::new(0),
            verified: AtomicUsize::new(0),
            closed: AtomicUsize::new(0),
            skipped: AtomicUsize::new(0),
            rejected: AtomicUsize::new(0),
            unchecked: AtomicUsize::new(0),
            retention: Mutex::new(Retention::default()),
        }
    }

    /// The committed fake checkers, which are the only artifacts in this repo
    /// that can prove a gate is not vacuous.
    fn fake_checker(name: &str) -> PathBuf {
        let path = ay_test_support::veripb::pin::repo_root()
            .join("ci/fake-checkers")
            .join(name);
        assert!(
            path.is_file(),
            "committed fake checker is missing: {}",
            path.display()
        );
        path
    }

    /// THE never-upgrade net. Table-drives every arm of the fold and asserts
    /// that the only inputs which can leave a row scored are the ones that
    /// genuinely certify (or deliberately decline to check) it.
    #[test]
    fn certificate_outcomes_never_upgrade() {
        let armed = CertArm::Armed {
            stem: PathBuf::from("/nonexistent/stem"),
        };
        let cases: Vec<(CertArm, Option<CertOutcome>, bool)> = vec![
            (CertArm::Off, None, true),
            (CertArm::Skipped(String::from("too big")), None, true),
            (
                armed.clone(),
                Some(CertOutcome::Verified {
                    lower: 947,
                    upper: 947,
                }),
                true,
            ),
            (
                armed.clone(),
                Some(CertOutcome::Verified {
                    lower: 381,
                    upper: 947,
                }),
                true,
            ),
            (
                armed.clone(),
                Some(CertOutcome::Verified {
                    lower: 0,
                    upper: 946,
                }),
                false,
            ),
            (
                armed.clone(),
                Some(CertOutcome::Rejected(String::from("bad pol step"))),
                false,
            ),
            (
                armed.clone(),
                Some(CertOutcome::Unusable(String::from("checker vanished"))),
                false,
            ),
            (armed, None, false),
        ];

        for (arm, outcome, expected_scored) in cases {
            let (status, detail, authority) =
                classify_certificate(&arm, outcome.as_ref(), 947, BASE);
            assert_eq!(
                scoring_solved(status),
                expected_scored,
                "arm {arm:?} outcome {outcome:?} scored={} detail={detail}",
                scoring_solved(status)
            );
            // Nothing may claim more than Optimum, and the two failure shapes
            // must land on their documented statuses.
            match (&arm, &outcome) {
                (CertArm::Armed { .. }, Some(CertOutcome::Rejected(_))) => {
                    assert_eq!(status, RunStatus::Wrong);
                    assert_eq!(authority, "veripb certificate checker");
                }
                (CertArm::Armed { .. }, Some(CertOutcome::Unusable(_)) | None) => {
                    assert_eq!(status, RunStatus::Unvalidated);
                    assert!(authority.contains("unvalidated"), "{authority}");
                }
                _ => {}
            }
            // A row that still scores must retain the provenance it already
            // had; "VeriPB-certified" alone would be a narrower claim.
            if scoring_solved(status) {
                assert!(
                    authority.contains(BASE),
                    "certified authority dropped the model-verifier provenance: {authority}"
                );
            }
        }
    }

    /// A REJECTED certificate must fail the sweep, not merely annotate it.
    /// Mirrors `unvalidated_unsat_claims_never_score_or_succeed`.
    #[test]
    fn rejected_certificate_fails_the_sweep() {
        let arm = CertArm::Armed {
            stem: PathBuf::from("/nonexistent/stem"),
        };
        let (status, detail, authority) = classify_certificate(
            &arm,
            Some(&CertOutcome::Rejected(String::from(
                "conclusion BOUNDS unverifiable",
            ))),
            947,
            BASE,
        );
        assert_eq!(status, RunStatus::Wrong);
        assert!(detail.contains("REJECTED"), "{detail}");

        let results = vec![RunResult {
            instance: String::from("case.wcnf"),
            status,
            seconds: 1.5,
            cost: Some(947),
            detail,
            authority,
        }];
        let summary = summarize_bench(&results, 10.0);
        assert_eq!(summary.wrong, 1);
        assert_eq!(summary.solved, 0);
        assert_eq!(bench_exit_code(summary), 1);
    }

    /// The wrong-answer detector: a certificate that verifies a DIFFERENT
    /// upper bound than the solver reported is a disagreement about the answer,
    /// and exactly one side can be right.
    #[test]
    fn certificate_upper_bound_must_match_the_reported_cost() {
        let arm = CertArm::Armed {
            stem: PathBuf::from("/nonexistent/stem"),
        };
        let (status, detail, authority) = classify_certificate(
            &arm,
            Some(&CertOutcome::Verified {
                lower: 0,
                upper: 946,
            }),
            947,
            BASE,
        );
        assert_eq!(status, RunStatus::Wrong);
        assert!(detail.contains("946") && detail.contains("947"), "{detail}");
        assert_eq!(authority, "veripb certificate checker");
    }

    #[test]
    fn parse_verdict_accepts_only_a_finished_run_with_a_real_bounds_conclusion() {
        assert_eq!(
            parse_verdict(
                Some(0),
                "Running VeriPB version 3.0.2\ns VERIFIED BOUNDS 381 <= obj <= 947\n",
                947
            ),
            CertOutcome::Verified {
                lower: 381,
                upper: 947
            }
        );
    }

    /// A VACUOUS proof is not evidence of a wrong answer.
    ///
    /// MEASURED against the pinned checker, on a proof concluding nothing:
    ///
    /// ```text
    /// $ veripb --opb t.opb none.pbp
    /// Running VeriPB version 3.0.2
    /// s VERIFIED NO CONCLUSION
    /// $ echo $?
    /// 0
    /// ```
    ///
    /// Exit 0 and an acceptance token — so every "did it finish" check passes —
    /// and yet NOTHING was established. Reading that as `Rejected` made the
    /// harness accuse AY of a wrong answer on the strength of a proof that
    /// said nothing at all. It is the D2 error (silence is not a refusal) in
    /// the no-conclusion case.
    ///
    /// The same holds for every other acceptance that is not the interval we
    /// asked about: the conclusion TYPE is written by `maxsat_proof`, not
    /// chosen by the checker, so it is evidence about emission, never a
    /// contradiction of the answer.
    #[test]
    fn parse_verdict_treats_a_vacuous_proof_as_no_verdict_not_as_a_refusal() {
        for stdout in [
            "Running VeriPB version 3.0.2\ns VERIFIED NO CONCLUSION\n",
            "s VERIFIED\n",
            "s VERIFIED SATISFIABLE\n",
            "s VERIFIED UNSATISFIABLE\n",
            "s VERIFIED BOUNDS 1 <= cost <= 1\n",
        ] {
            let observed = parse_verdict(Some(0), stdout, 947);
            assert!(
                matches!(observed, CertOutcome::Unusable(_)),
                "an acceptance that establishes no interval must not accuse AY: \
                 {stdout:?} -> {observed}"
            );
            // And the fold must call that Unvalidated, never Wrong.
            let (status, _, _) = classify_certificate(
                &CertArm::Armed {
                    stem: PathBuf::from("/nonexistent/stem"),
                },
                Some(&observed),
                947,
                BASE,
            );
            assert_eq!(status, RunStatus::Unvalidated, "{stdout:?}");
        }
    }

    /// A verified interval that merely CONTAINS the reported cost confirms
    /// nothing about it — and "did not confirm" is never "contradicted".
    #[test]
    fn a_verified_interval_that_does_not_pin_the_cost_is_unvalidated_not_wrong() {
        let arm = CertArm::Armed {
            stem: PathBuf::from("/nonexistent/stem"),
        };
        // 947 sits strictly inside [0, 1000]: consistent with AY, no evidence
        // for AY. Unvalidated.
        let (status, detail, _) = classify_certificate(
            &arm,
            Some(&CertOutcome::Verified {
                lower: 0,
                upper: 1000,
            }),
            947,
            BASE,
        );
        assert_eq!(status, RunStatus::Unvalidated, "{detail}");
        // 947 sits OUTSIDE [1000, 1000]: the checker proved obj >= 1000, so a
        // model of cost 947 cannot exist. That is a contradiction.
        let (status, detail, _) = classify_certificate(
            &arm,
            Some(&CertOutcome::Verified {
                lower: 1000,
                upper: 1000,
            }),
            947,
            BASE,
        );
        assert_eq!(status, RunStatus::Wrong, "{detail}");
    }

    /// A correct-looking verdict line from a run that did not finish is not a
    /// verdict (`ci/fake-checkers/verdict-then-exit1.sh`). It is also not
    /// evidence of a WRONG ANSWER: the run did not finish, so it refuted
    /// nothing.
    #[test]
    fn parse_verdict_refuses_a_good_line_from_a_failed_run() {
        assert!(matches!(
            parse_verdict(Some(1), "s VERIFIED BOUNDS 2 <= obj <= 2\n", 2),
            CertOutcome::Unusable(_)
        ));
    }

    /// THE weakened guard, stated so that deleting it fails this test.
    ///
    /// `veripb -u` prints `s UNDER WEAKENED GUARANTEES BOUNDS <lo> <= obj <= <hi>`
    /// and exits 0: a well-formed, fully PARSEABLE interval from a run that did
    /// not check deletion steps. Every other check in `parse_verdict` passes it
    /// — the guarantee token is recognised, the conclusion is a real BOUNDS
    /// interval, both bounds are integers — so if the guard goes, this input is
    /// accepted as `Verified { lower: 2, upper: 2 }`.
    #[test]
    fn parse_verdict_refuses_a_weakened_verdict() {
        let observed = parse_verdict(
            Some(0),
            "s UNDER WEAKENED GUARANTEES BOUNDS 2 <= obj <= 2\n",
            2,
        );
        assert!(
            matches!(observed, CertOutcome::Unusable(_)),
            "a weakened verdict is not the check we asked for: {observed}"
        );
        assert!(observed.to_string().contains("WEAKENED"), "{observed}");
    }

    /// The `ay-pb/src/veripb_runner.rs:478` bug, stated as a property: the
    /// verdict is the FIRST `s `-prefixed line, and nothing else on stdout is
    /// a verdict.
    ///
    /// The previous version of this test asserted only `Rejected` on a stdout
    /// whose comment line ALSO parsed as a refusal, so it passed under the very
    /// mutation it claimed to forbid — replacing
    /// `.find(|line| line.starts_with(VERDICT_PREFIX))` with a `.contains`
    /// scan picked the comment and still answered `Rejected`. Each case below
    /// is chosen so that selecting the WRONG line changes the OUTCOME, which is
    /// what makes the anchoring the thing under test.
    #[test]
    fn parse_verdict_reads_only_the_first_s_prefixed_line() {
        // (stdout, expected, what selecting the wrong line would produce)
        let cases: [(&str, &str); 3] = [
            // A `c` comment mentioning VERIFIED must not shadow a genuine
            // acceptance. A `.contains(VERIFIED_STATUS)` scan picks the comment
            // and answers Rejected.
            (
                "c this proof was not VERIFIED\ns VERIFIED BOUNDS 2 <= obj <= 2\n",
                "verified",
            ),
            // A `c` comment carrying a COMPLETE verdict must not be read as
            // one. A `.contains` scan picks the comment; anchoring reads the
            // vacuous `s ` line below it.
            (
                "c s VERIFIED BOUNDS 2 <= obj <= 2\ns VERIFIED NO CONCLUSION\n",
                "unusable",
            ),
            // FIRST, not last: a checker that refuses and then chatters must
            // not be read from the bottom. Scanning for the last `s ` line
            // answers `verified` here.
            (
                "s NOT VERIFIED\ns VERIFIED BOUNDS 2 <= obj <= 2\n",
                "rejected",
            ),
        ];
        for (stdout, expected) in cases {
            let observed = parse_verdict(Some(0), stdout, 2);
            let actual = match observed {
                CertOutcome::Verified { .. } => "verified",
                CertOutcome::Rejected(_) => "rejected",
                CertOutcome::Unusable(_) => "unusable",
            };
            assert_eq!(
                actual, expected,
                "the verdict must be the FIRST `s ` line: {stdout:?}"
            );
        }
    }

    /// Silence is not a refusal.
    ///
    /// The pinned checker prints NO `s ` line for a genuine refusal, for a
    /// missing `.pbp`, for a truncated `.opb` and for a truncated `.pbp` alike
    /// — all four print only `Running VeriPB version 3.0.2` and exit 1. Reading
    /// that as `Rejected` made every infrastructure failure an accusation that
    /// AY gave a wrong answer. It is `Unusable`: unscored, and
    /// `bench_exit_code` still fails the sweep on it.
    #[test]
    fn parse_verdict_treats_silence_as_no_verdict_not_as_a_refusal() {
        for (exit, stdout) in [
            (Some(0), ""),
            (Some(1), "Running VeriPB version 3.0.2\n"),
            (None, "Running VeriPB version 3.0.2\n"),
        ] {
            let observed = parse_verdict(exit, stdout, 2);
            assert!(
                matches!(observed, CertOutcome::Unusable(_)),
                "exit {exit:?} stdout {stdout:?} -> {observed}"
            );
        }
        // And the fold must call that Unvalidated, never Wrong.
        let arm = CertArm::Armed {
            stem: PathBuf::from("/nonexistent/stem"),
        };
        let (status, _, _) = classify_certificate(
            &arm,
            Some(&parse_verdict(Some(1), "Running VeriPB version 3.0.2\n", 2)),
            2,
            BASE,
        );
        assert_eq!(status, RunStatus::Unvalidated);
    }

    /// The ONE verdict shape that licenses `Rejected`: a completed run whose
    /// status token REFUSES the proof. Everything else is at most "we did not
    /// get the check we asked for".
    #[test]
    fn parse_verdict_rejects_only_a_completed_refusal() {
        for stdout in ["s NOT VERIFIED\n", "s FAILED\n"] {
            let observed = parse_verdict(Some(0), stdout, 2);
            assert!(
                matches!(observed, CertOutcome::Rejected(_)),
                "{stdout:?} -> {observed}"
            );
        }
        // The same refusal from a run that did not finish proves nothing.
        assert!(matches!(
            parse_verdict(Some(1), "s NOT VERIFIED\n", 2),
            CertOutcome::Unusable(_)
        ));
    }

    /// #D10: a checker's own text is UNTRUSTED, and every place this lane
    /// repeats it is bounded.
    ///
    /// A `detail` is copied verbatim into the sweep summary and into the JSON
    /// report, so a checker that answers on one megabyte-long line must not be
    /// able to make either unreadable. Both halves of a detail — the verdict
    /// line and the stderr excerpt beside it — are bounded by the same
    /// `DETAIL_EXCERPT_MAX`, so neither can swamp the other.
    ///
    /// The `--version` string is the third such place and is bounded at its
    /// source in `reported_version`, which is what covers the startup warning,
    /// the `certificate lane:` banner and the report's `checker_version`.
    #[test]
    fn checker_text_is_bounded_everywhere_it_is_repeated() {
        let shout = "X".repeat(200_000);
        // Every verdict shape that carries the line into a message.
        for stdout in [
            format!("s NOT VERIFIED {shout}\n"),
            format!("s VERIFIED {shout}\n"),
            format!("s VERIFIED BOUNDS {shout} <= obj <= 2\n"),
            format!("s UNDER WEAKENED GUARANTEES BOUNDS 2 <= obj <= 2 {shout}\n"),
        ] {
            let observed = parse_verdict(Some(0), &stdout, 2).to_string();
            // Against a LITERAL, not against `DETAIL_EXCERPT_MAX`: a bound
            // compared only to itself is satisfied by widening it.
            assert!(
                observed.chars().count() < 1024,
                "an unbounded verdict line reached a row detail ({} chars)",
                observed.chars().count()
            );
        }
        // A verdict from a run that did not finish takes a different message
        // path and must be bounded too.
        let observed = parse_verdict(Some(1), &format!("s VERIFIED {shout}\n"), 2).to_string();
        assert!(
            observed.chars().count() < 1024,
            "{} chars",
            observed.chars().count()
        );
        // And `excerpt` itself must cap rather than merely flatten.
        assert_eq!(
            excerpt(&shout, DETAIL_EXCERPT_MAX).chars().count(),
            DETAIL_EXCERPT_MAX + 3,
            "excerpt must truncate to the cap plus its `...` marker"
        );
    }

    #[test]
    fn size_guard_and_external_solver_disarm_certification() {
        let dir = scratch("armguard");
        let file = dir.join("case.wcnf");
        std::fs::write(&file, "h 1 0\nabc\n").expect("write");
        assert_eq!(std::fs::metadata(&file).unwrap().len(), 10);

        let mut plan = test_plan(&dir);
        plan.max_instance_bytes = 1;

        match arm_certificate(Some(&plan), false, &file, "case.wcnf") {
            CertArm::Skipped(why) => assert!(
                why.contains("--proof-max-instance-mib"),
                "a skip must name the flag that caused it: {why}"
            ),
            other => panic!("expected a size skip, got {other:?}"),
        }
        // The external lane is never armed, whatever the size guard says.
        assert_eq!(
            arm_certificate(Some(&plan), true, &file, "case.wcnf"),
            CertArm::Off
        );
        assert_eq!(
            arm_certificate(None, false, &file, "case.wcnf"),
            CertArm::Off
        );

        // 0 means NO cap, not "a cap of zero bytes".
        plan.max_instance_bytes = 0;
        let armed = arm_certificate(Some(&plan), false, &file, "case.wcnf");
        match &armed {
            CertArm::Armed { stem } => {
                let name = stem.file_name().unwrap().to_string_lossy().into_owned();
                assert!(name.ends_with("case_wcnf"), "stem not sanitised: {name}");
                assert!(name.starts_with("00000-"), "stem not sequenced: {name}");
            }
            other => panic!("expected Armed, got {other:?}"),
        }
        // The `.` must be gone: `with_extension("opb")` would otherwise eat it.
        if let CertArm::Armed { stem } = &armed {
            let (opb, pbp) = artifact_paths(stem);
            assert!(opb.to_string_lossy().ends_with("case_wcnf.opb"));
            assert!(pbp.to_string_lossy().ends_with("case_wcnf.opb.pbp"));
        }
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn candidate_paths_treats_a_broken_override_as_an_error() {
        let env = env_from(&[("VERIPB_BIN", "/nonexistent/veripb")]);
        let error = candidate_paths(&env).expect_err("a set-but-missing override must be fatal");
        assert!(error.contains("VERIPB_BIN"), "{error}");
    }

    #[test]
    fn candidate_paths_skips_an_empty_override() {
        let env = env_from(&[
            ("VERIPB_BIN", ""),
            ("PATH", "/nonexistent-path-dir"),
            ("AY_VERIPB_SEARCH_PATH", "/nonexistent/checker"),
        ]);
        let paths = candidate_paths(&env).expect("an empty override falls through");
        assert_eq!(paths, vec![PathBuf::from("/nonexistent/checker")]);
    }

    #[test]
    fn locate_reports_every_path_it_searched() {
        let env = env_from(&[
            ("PATH", "/nonexistent-path-dir"),
            ("AY_VERIPB_SEARCH_PATH", "/nonexistent/checker"),
        ]);
        let error = locate_with(&env).expect_err("no checker exists at that path");
        assert!(error.contains("/nonexistent/checker"), "{error}");
    }

    /// Half of the non-vacuity proof: delete the GOOD probe and these two
    /// trivial binaries pass the self-test.
    ///
    /// This test does NOT establish anything about the false probe — both of
    /// these produce empty stdout, so the good probe already refuses them. The
    /// false probe has its own killer, below.
    #[cfg(unix)]
    #[test]
    fn self_test_rejects_a_trivially_true_checker() {
        let error = self_test(Path::new("/usr/bin/true"))
            .expect_err("/usr/bin/true must not pass the certificate self-test");
        assert!(error.contains("cert-selftest-good"), "{error}");
        let error = self_test(Path::new("/usr/bin/false"))
            .expect_err("/usr/bin/false must not pass the certificate self-test");
        assert!(error.contains("cert-selftest-good"), "{error}");
    }

    /// The other half, and the one that keeps the false probe honest:
    /// `ci/fake-checkers/parrot.sh` reads the `conclusion` line out of the
    /// proof and echoes back the matching verdict. It PASSES the good probe by
    /// construction — a parrot agrees with every claim — so the ONLY thing that
    /// can catch it is a probe whose proof states something false in the shape
    /// the real emitter writes. Delete the false probe, or drop the `: <hint>`
    /// field from it, and this test fails.
    #[cfg(unix)]
    #[test]
    fn self_test_rejects_a_parrot_checker() {
        let parrot = fake_checker("parrot.sh");
        let error = self_test(&parrot).expect_err(
            "a checker that only restates the proof's own claim \
                                           must not pass the certificate self-test",
        );
        assert!(
            error.contains("cert-selftest-false"),
            "the parrot must be caught by the FALSE probe, not by luck: {error}"
        );
    }

    /// The other committed fakes, for completeness: none of them survives the
    /// self-test either. `always-unsat.sh` and `silent-exit0.sh` die on the
    /// good probe; `verdict-then-exit1.sh` dies on the exit-code half of the
    /// verdict contract even while reprinting a REAL checker's verdict.
    ///
    /// # Why there is a locally-written stub here
    ///
    /// `verdict-then-exit1.sh` delegates to a real checker, so it can only run
    /// where one is installed — and this test used to `continue` past it in
    /// silence when none was, which removed the ONLY automated coverage of the
    /// exit-code half of the verdict rule on precisely the hosts most likely to
    /// lack a checker. A checker-free host is where that rule is least
    /// exercised and most likely to rot, and a silent skip is the vacuity
    /// failure this whole lane exists to prevent. So the stub below states the
    /// same thing the committed fake does — a PERFECT verdict line from a run
    /// that exited 1 — without needing anything installed, and it runs
    /// everywhere. The committed fake is still run on top of it when a real
    /// checker is present.
    #[cfg(unix)]
    #[test]
    fn self_test_rejects_every_committed_fake_checker() {
        use std::os::unix::fs::PermissionsExt as _;

        let scratch = scratch("fakes");
        let script = |name: &str, body: &str| -> PathBuf {
            let path = scratch.join(name);
            std::fs::write(&path, body).expect("write script");
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755))
                .expect("chmod script");
            path
        };

        let mut targets: Vec<(String, PathBuf)> = ["silent-exit0.sh", "always-unsat.sh"]
            .iter()
            .map(|name| ((*name).to_string(), fake_checker(name)))
            .collect();

        // The exit-code half of the verdict rule, covered on EVERY host. This
        // stub is a CORRECT checker in every respect but one: it accepts the
        // good proof, refuses the false one, and exits 1. So the only rule that
        // can catch it is "a verdict from a run that did not finish is not a
        // verdict" — delete that rule and this stub passes both probes.
        let exit_code_stub = script(
            "stub-verdict-then-exit1.sh",
            "#!/bin/sh\ncase \"${1:-}\" in --version) echo 'veripb 3.0.2'; exit 0 ;; esac\n\
             echo 'Running VeriPB version 3.0.2'\n\
             if grep -q 'conclusion BOUNDS 1 :' \"$3\"; then\n\
             \techo 's VERIFIED BOUNDS 1 <= obj <= 1'\n\
             else\n\
             \techo 's NOT VERIFIED'\n\
             fi\nexit 1\n",
        );
        let error = self_test(&exit_code_stub)
            .expect_err("a perfect verdict from a run that exited 1 is not a verdict");
        assert!(
            error.contains("cert-selftest-good"),
            "the stub must be caught by the EXIT CODE, not by its verdict text: {error}"
        );
        targets.push((
            String::from("stub: perfect verdict, exit 1"),
            exit_code_stub,
        ));

        // And the committed fake, whenever a real checker can back it.
        if let Ok(real) = ay_test_support::veripb::locate() {
            let fake = fake_checker("verdict-then-exit1.sh");
            targets.push((
                String::from("verdict-then-exit1.sh"),
                script(
                    "shim-verdict-then-exit1.sh",
                    &format!(
                        "#!/bin/sh\nAY_FAKE_VERIPB_DELEGATE={} exec {} \"$@\"\n",
                        real.display(),
                        fake.display()
                    ),
                ),
            ));
        }

        let survivors: Vec<&str> = targets
            .iter()
            .filter(|(_, target)| self_test(target).is_ok())
            .map(|(name, _)| name.as_str())
            .collect();
        let survivors: Vec<String> = survivors.iter().map(|name| (*name).to_string()).collect();
        std::fs::remove_dir_all(&scratch).ok();
        assert!(
            survivors.is_empty(),
            "fake checkers passed the self-test: {survivors:?}"
        );
    }

    #[test]
    fn retention_keys_on_the_verdict_not_on_the_outcome_variant() {
        let dir = scratch("retain");
        let plan = test_plan(&dir);
        let make = |name: &str| -> (PathBuf, PathBuf) {
            let stem = dir.join(name);
            let (opb, pbp) = artifact_paths(&stem);
            std::fs::write(&opb, "* opb\n").expect("write opb");
            std::fs::write(&pbp, "pbp\n").expect("write pbp");
            (opb, pbp)
        };

        let (opb, pbp) = make("good");
        assert!(!plan.retain_or_delete(RunStatus::Optimum, &opb, &pbp));
        assert!(!opb.exists(), "a verified .opb must not survive the sweep");
        assert!(!pbp.exists(), "a verified .pbp must not survive the sweep");

        // THE case the lane exists for: the checker verified a DIFFERENT bound
        // than the solver reported. `classify_certificate` scores that `Wrong`
        // while the outcome variant is still `Verified` — keying on the variant
        // deleted exactly this evidence.
        let (opb, pbp) = make("disagreed");
        let (status, _, _) = classify_certificate(
            &CertArm::Armed {
                stem: dir.join("disagreed"),
            },
            Some(&CertOutcome::Verified {
                lower: 0,
                upper: 946,
            }),
            947,
            BASE,
        );
        assert_eq!(status, RunStatus::Wrong);
        assert!(
            plan.retain_or_delete(status, &opb, &pbp),
            "the wrong-answer detector must not delete its own evidence"
        );
        assert!(
            opb.exists() && pbp.exists(),
            "wrong-answer evidence was deleted"
        );

        let (opb, pbp) = make("bad");
        assert!(plan.retain_or_delete(RunStatus::Wrong, &opb, &pbp));
        assert!(opb.exists(), "rejection evidence must be kept");
        assert!(pbp.exists(), "rejection evidence must be kept");

        // An Unusable produced by `precheck_artifacts` has NOTHING on disk, so
        // it must not consume a retention slot.
        let (opb, pbp) = artifact_paths(&dir.join("absent"));
        let before = plan.retained();
        assert!(!plan.retain_or_delete(RunStatus::Unvalidated, &opb, &pbp));
        assert_eq!(plan.retained(), before, "an absent pair was 'retained'");

        // The RAII net covers every path that never reaches the fold.
        let stem = dir.join("orphan");
        let (opb, pbp) = artifact_paths(&stem);
        let guard = CertArtifacts::for_arm(&CertArm::Armed { stem });
        std::fs::write(&opb, "* opb\n").expect("write opb");
        std::fs::write(&pbp, "pbp\n").expect("write pbp");
        drop(guard);
        assert!(!opb.exists(), "an unchecked row must not leak its .opb");
        assert!(!pbp.exists(), "an unchecked row must not leak its .pbp");

        std::fs::remove_dir_all(&dir).ok();
    }

    /// #N3: a `Wrong` row keeps its certificate whichever detector produced it.
    ///
    /// Four of `run_one`'s five wrong-answer detectors — missing `o` line,
    /// reference optimum disagrees, model fails re-evaluation, UNSAT against a
    /// feasible reference — `return` before the certificate fold, so the only
    /// thing standing between their artifacts and `Drop` is this call. It is
    /// the same defect class as D4, in the paths that fire exactly when the
    /// evidence matters.
    #[test]
    fn a_wrong_verdict_keeps_its_artifacts_whichever_detector_produced_it() {
        let dir = scratch("wrong-evidence");
        let plan = test_plan(&dir);
        let armed = |name: &str| -> (CertArtifacts, PathBuf, PathBuf) {
            let stem = dir.join(name);
            let guard = CertArtifacts::for_arm(&CertArm::Armed { stem: stem.clone() });
            let (opb, pbp) = artifact_paths(&stem);
            std::fs::write(&opb, "* opb\n").expect("write opb");
            std::fs::write(&pbp, "pbp\n").expect("write pbp");
            (guard, opb, pbp)
        };

        // A detector that returns early still keeps its evidence.
        let (mut guard, opb, pbp) = armed("detector-wrong");
        guard.retain_if_evidence(Some(&plan), RunStatus::Wrong);
        drop(guard);
        assert!(
            opb.exists() && pbp.exists(),
            "a wrong-answer detector deleted its own certificate"
        );

        // A row that is merely unvalidated keeps its evidence too...
        let (mut guard, opb, pbp) = armed("detector-unvalidated");
        guard.retain_if_evidence(Some(&plan), RunStatus::Unvalidated);
        drop(guard);
        assert!(opb.exists() && pbp.exists());

        // ...and a scored row keeps nothing: nobody will open those files.
        let (mut guard, opb, pbp) = armed("detector-optimum");
        guard.retain_if_evidence(Some(&plan), RunStatus::Optimum);
        drop(guard);
        assert!(!opb.exists() && !pbp.exists());

        // With no plan at all (`--proof-check` off) there is nothing to keep,
        // and the RAII net still cleans up.
        let (mut guard, opb, pbp) = armed("detector-no-plan");
        guard.retain_if_evidence(None, RunStatus::Wrong);
        drop(guard);
        assert!(!opb.exists() && !pbp.exists());

        std::fs::remove_dir_all(&dir).ok();
    }

    /// #N5: the checker's self-reported `--version` is UNTRUSTED text, and it
    /// reaches three human-facing places (the startup warning, the
    /// `certificate lane:` banner, the JSON report's `checker_version`).
    /// Bounding it at the source covers all three.
    #[cfg(unix)]
    #[test]
    fn a_shouting_checker_cannot_flood_the_version_string() {
        use std::os::unix::fs::PermissionsExt as _;

        let dir = scratch("version-bound");
        let script = dir.join("shout.sh");
        std::fs::write(
            &script,
            "#!/bin/sh\nawk 'BEGIN{s=\"\";while(length(s)<511)s=s \"V\";print s}'\nexit 0\n",
        )
        .expect("write script");
        std::fs::set_permissions(&script, std::fs::Permissions::from_mode(0o755)).expect("chmod");

        let reported = reported_version(&script).expect("the stub prints a parseable field");
        // A LITERAL, and a TIGHT one. `DETAIL_EXCERPT_MAX + 3` would be
        // self-referential; 512 would be loose enough for the observed
        // 511-character line to slip through, which is the exact case this
        // test exists for.
        assert!(
            reported.chars().count() < 256,
            "an unbounded version string ({} chars) reached the banner and the report",
            reported.chars().count()
        );
        // The cross-check must still fail loudly rather than accept it.
        let error = check_version(&script).expect_err("511 `V`s is not the pinned version");
        assert!(
            error.chars().count() < 1024,
            "the warning itself was unbounded: {} chars",
            error.chars().count()
        );

        std::fs::remove_dir_all(&dir).ok();
    }

    /// Retention is BOUNDED. `Unusable` is systemic — a checker that vanished
    /// makes every armed row unchecked — so "keep every failure" is the
    /// multi-GB blowup this lane exists to avoid. Past the cap, artifacts are
    /// deleted and the refusal is counted so the summary can say so.
    /// The `Wrong` byte reserve must be able to hold at least one artifact pair
    /// the size guard actually admits, or it protects nothing in the byte
    /// dimension: unvalidated noise fills the general budget and the one
    /// contradicted row is refused for want of space.
    ///
    /// Kill mutation: set `RETAIN_WRONG_RESERVED_BYTES` back to 64 MiB (its
    /// first value) — 64 MiB < the ~74 MiB a 40 MiB instance expands to.
    #[test]
    fn the_wrong_reserve_holds_at_least_one_admitted_artifact_pair() {
        // Literals, not the constants under test: a bound compared only to
        // itself is satisfied by widening it, which is how two tests in the
        // previous round passed while proving nothing.
        let largest_admitted_instance: u64 = 40 * 1024 * 1024;
        let observed_artifact_expansion = 1.84_f64;
        let largest_pair = (largest_admitted_instance as f64 * observed_artifact_expansion) as u64;
        assert!(
            RETAIN_WRONG_RESERVED_BYTES >= largest_pair,
            "the wrong-answer byte reserve ({RETAIN_WRONG_RESERVED_BYTES}) cannot hold one \
             admitted artifact pair ({largest_pair}); unvalidated noise can still crowd out \
             the evidence this lane exists to keep"
        );
        assert!(
            RETAIN_WRONG_RESERVED_BYTES < RETAIN_MAX_BYTES,
            "the reserve must leave room for unvalidated evidence too"
        );
    }

    #[test]
    fn retention_is_capped_and_the_cap_is_reported() {
        let dir = scratch("retain-cap");
        let plan = test_plan(&dir);
        let unvalidated_max = RETAIN_MAX_ROWS - RETAIN_WRONG_RESERVED_ROWS;
        let rows = RETAIN_MAX_ROWS + 4;
        for row in 0..rows {
            let stem = dir.join(format!("{row:05}-case"));
            let (opb, pbp) = artifact_paths(&stem);
            std::fs::write(&opb, "* opb\n").expect("write opb");
            std::fs::write(&pbp, "pbp\n").expect("write pbp");
            let kept = plan.retain_or_delete(RunStatus::Unvalidated, &opb, &pbp);
            assert_eq!(kept, row < unvalidated_max, "row {row}");
            assert_eq!(opb.exists(), kept, "row {row}");
            assert_eq!(pbp.exists(), kept, "row {row}");
        }
        assert_eq!(plan.retained(), unvalidated_max);
        assert_eq!(plan.retention_refused(), rows - unvalidated_max);
        assert!(plan.retained_bytes() > 0);
        assert!(plan.retained_bytes() <= RETAIN_MAX_BYTES);

        // And the byte cap bites independently of the row cap.
        let plan = test_plan(&dir);
        let stem = dir.join("huge");
        let (opb, pbp) = artifact_paths(&stem);
        std::fs::write(&opb, vec![b'x'; 1024]).expect("write opb");
        std::fs::write(&pbp, "pbp\n").expect("write pbp");
        {
            let mut ledger = plan.retention.lock().expect("ledger");
            ledger.bytes = RETAIN_MAX_BYTES;
        }
        assert!(!plan.retain_or_delete(RunStatus::Wrong, &opb, &pbp));
        assert!(!opb.exists() && !pbp.exists());
        assert_eq!(plan.retention_refused(), 1);

        std::fs::remove_dir_all(&dir).ok();
    }

    /// #N2: infrastructure noise must not be able to evict the ONE row this
    /// lane exists to catch.
    ///
    /// `Unusable` is SYSTEMIC — a deleted checker, a checker that times out or
    /// breaches RSS on every row — and D2 widened the non-`Optimum` set so
    /// every one of those is `Unvalidated`. With one shared FIFO budget, 32
    /// such rows arriving first filled it, and the contradicted row that
    /// arrived afterwards had its artifacts deleted on the way out. The
    /// reserve is what makes that impossible.
    #[test]
    fn unvalidated_noise_cannot_evict_wrong_answer_evidence() {
        let dir = scratch("retain-reserve");
        let plan = test_plan(&dir);
        let make = |name: &str| -> (PathBuf, PathBuf) {
            let (opb, pbp) = artifact_paths(&dir.join(name));
            std::fs::write(&opb, "* opb\n").expect("write opb");
            std::fs::write(&pbp, "pbp\n").expect("write pbp");
            (opb, pbp)
        };

        // The reserve must EXIST, and this assertion has to be made against a
        // LITERAL. Every other assertion below is expressed in terms of
        // `RETAIN_WRONG_RESERVED_ROWS`, so setting it to 0 leaves them all
        // trivially true: the loop that proves a `Wrong` row still fits would
        // run zero times. That is the vacuity failure this lane exists to
        // refuse, reproduced inside its own test.
        assert!(
            RETAIN_WRONG_RESERVED_ROWS > 0 && RETAIN_WRONG_RESERVED_BYTES > 0,
            "there is no reserve: unvalidated noise can consume the entire budget"
        );
        assert!(RETAIN_WRONG_RESERVED_ROWS < RETAIN_MAX_ROWS);

        // A whole sweep's worth of checker outage, well past the total cap.
        for row in 0..(RETAIN_MAX_ROWS * 4) {
            let (opb, pbp) = make(&format!("noise-{row:05}"));
            plan.retain_or_delete(RunStatus::Unvalidated, &opb, &pbp);
        }
        assert_eq!(
            plan.retained(),
            RETAIN_MAX_ROWS - RETAIN_WRONG_RESERVED_ROWS,
            "unvalidated rows spent past their budget and into the reserve"
        );

        // Now the row the lane exists for arrives, last. It must still fit.
        for row in 0..RETAIN_WRONG_RESERVED_ROWS {
            let (opb, pbp) = make(&format!("wrong-{row:05}"));
            assert!(
                plan.retain_or_delete(RunStatus::Wrong, &opb, &pbp),
                "wrong-answer evidence was crowded out by unvalidated noise (row {row})"
            );
            assert!(opb.exists() && pbp.exists(), "row {row}");
        }
        assert_eq!(plan.retained(), RETAIN_MAX_ROWS);

        // The reserve is a reserve, not an exemption: `Wrong` is still bounded
        // by the total cap, and passing it is counted so the summary says so.
        let refused_before = plan.retention_refused();
        let (opb, pbp) = make("wrong-overflow");
        assert!(!plan.retain_or_delete(RunStatus::Wrong, &opb, &pbp));
        assert!(!opb.exists() && !pbp.exists());
        assert_eq!(plan.retention_refused(), refused_before + 1);

        std::fs::remove_dir_all(&dir).ok();
    }

    /// A previous sweep's artifacts must never be checked as if this run wrote
    /// them. Stems are `<seq:05>-<instance>` with `seq` restarting at 0 per
    /// process, so a reused `--proof-dir` at `--jobs 1` collides exactly; the
    /// stale pair is non-empty, so `precheck_artifacts` would wave it through
    /// and the checker would certify a previous run's answer against this run's
    /// cost — a FALSE `RunStatus::Wrong`.
    #[test]
    fn a_previous_runs_artifacts_are_unlinked_before_this_row_runs() {
        let dir = scratch("stale");
        let stem = dir.join("00000-case_wcnf");
        let (opb, pbp) = artifact_paths(&stem);
        std::fs::write(&opb, "* a previous sweep's formula\n").expect("write opb");
        std::fs::write(&pbp, "a previous sweep's proof\n").expect("write pbp");
        assert!(
            precheck_artifacts(&opb, &pbp).is_none(),
            "the stale pair is exactly the shape precheck accepts — that is the hazard"
        );

        let guard = CertArtifacts::for_arm(&CertArm::Armed { stem });
        assert!(guard.stale().is_none(), "a removable pair is not a failure");
        assert!(
            !opb.exists(),
            "a previous run's .opb survived into this row"
        );
        assert!(
            !pbp.exists(),
            "a previous run's .pbp survived into this row"
        );
        // And with nothing on disk, the row is Unvalidated, never Wrong.
        assert!(matches!(
            precheck_artifacts(&opb, &pbp),
            Some(CertOutcome::Unusable(_))
        ));
        drop(guard);
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn precheck_catches_a_certificate_that_was_never_written() {
        let dir = scratch("precheck");
        let (opb, pbp) = artifact_paths(&dir.join("missing"));
        assert!(matches!(
            precheck_artifacts(&opb, &pbp),
            Some(CertOutcome::Unusable(_))
        ));
        std::fs::write(&opb, "* opb\n").expect("write");
        std::fs::write(&pbp, "").expect("write");
        assert!(
            matches!(
                precheck_artifacts(&opb, &pbp),
                Some(CertOutcome::Unusable(_))
            ),
            "a zero-length proof is not a proof"
        );
        std::fs::write(&pbp, "pbp\n").expect("write");
        assert!(precheck_artifacts(&opb, &pbp).is_none());
        std::fs::remove_dir_all(&dir).ok();
    }

    /// One pin, one identity. A copied or stale `include_str!` target, or a
    /// reader that mishandles the `#` comment block at the top of the file,
    /// shows up here.
    #[test]
    fn pin_reader_agrees_with_ay_test_support() {
        assert_eq!(pin::commit(), ay_test_support::veripb::pin::commit());
        assert_eq!(pin::version(), ay_test_support::veripb::pin::version());
        assert_eq!(
            pin::patch_sha256(),
            ay_test_support::veripb::pin::patch_sha256()
        );
        assert_eq!(pin::commit().len(), 40);
    }

    /// End to end against the REAL pinned checker: emit a certificate the way
    /// `ay maxsat solve --proof` does, read the verdict the way the bench lane
    /// does, then change one number and confirm the checker refuses it.
    ///
    /// Uses `require_checker`, so it PANICS rather than skips unless
    /// `AY_VERIPB_OPTIONAL` is set.
    #[cfg(unix)]
    #[test]
    fn certifies_a_real_emission_and_rejects_a_tampered_one() {
        use crate::maxsat_proof::{emit_certificate, PaidCore};

        const SUITE: &str = "maxsat-bench-cert";
        const WCNF: &str = "h -1 -2 -3 0\nh -4 -5 -6 0\n1 1 0\n1 2 0\n1 3 0\n1 4 0\n1 5 0\n1 6 0\n";

        let Some(checker) = ay_test_support::veripb::require_checker(SUITE) else {
            return;
        };
        let dir = scratch("e2e");
        let wcnf = dir.join("t.wcnf");
        std::fs::write(&wcnf, WCNF).expect("write wcnf");

        let model = vec![false, false, true, true, false, true, true];
        let cores = vec![
            PaidCore {
                hard_row: 1,
                w_min: 1,
                members: vec![1, 2, 3],
            },
            PaidCore {
                hard_row: 2,
                w_min: 1,
                members: vec![4, 5, 6],
            },
        ];
        let stream = |p: &Path,
                      cb: &mut dyn FnMut(Option<u64>, &[i32]) -> anyhow::Result<()>|
         -> anyhow::Result<()> {
            crate::cmd_maxsat::stream_wcnf_file(p, cb).map(|_| ())
        };
        let stem = dir.join("00000-t_wcnf");
        emit_certificate(&wcnf, &stem, &model, 2, &cores, &[], &stream).expect("emit");
        let (opb, pbp) = artifact_paths(&stem);
        assert!(precheck_artifacts(&opb, &pbp).is_none());

        let check = |proof: &Path| -> CertOutcome {
            let output = run_cert_probe(
                &checker,
                &[OsStr::new("--opb"), opb.as_os_str(), proof.as_os_str()],
            )
            .expect("run checker");
            parse_verdict(output.code, &output.stdout, 2)
        };

        assert_eq!(
            check(&pbp),
            CertOutcome::Verified { lower: 2, upper: 2 },
            "the pinned checker must certify a genuine optimality proof"
        );
        // And the fold must turn that into a scored, certified row.
        let arm = CertArm::Armed { stem: stem.clone() };
        let (status, detail, authority) = classify_certificate(&arm, Some(&check(&pbp)), 2, BASE);
        assert_eq!(status, RunStatus::Optimum);
        assert!(detail.contains("closed"), "{detail}");
        assert!(
            authority.contains("VeriPB-certified optimality"),
            "{authority}"
        );

        // Now understate the upper bound by one. Nothing else changes.
        //
        // The pinned checker REFUSES this — and it refuses it the way it
        // refuses everything: `Running VeriPB version 3.0.2` on stdout, the
        // diagnosis on stderr, exit 1. There is no `s ` verdict line, and the
        // same stdout is produced by a missing `.pbp` and by a truncated
        // `.opb`, so this reader cannot tell a refusal from a crash and must
        // not call either one a WRONG ANSWER. The row is `Unvalidated`:
        // unscored, and `bench_exit_code` fails the sweep on it.
        let good = std::fs::read_to_string(&pbp).expect("read pbp");
        let tampered = good.replacen(": 9 2 :", ": 9 1 :", 1);
        assert_ne!(tampered, good, "{SUITE}: the mutation did not apply");
        let tampered_path = dir.join("tampered.pbp");
        std::fs::write(&tampered_path, tampered).expect("write tampered");
        let refused = check(&tampered_path);
        assert!(
            !matches!(refused, CertOutcome::Verified { .. }),
            "{SUITE}: the checker accepted an understated upper bound ({refused})"
        );
        assert!(
            matches!(refused, CertOutcome::Unusable(_)),
            "{SUITE}: a verdict-less exit-1 refusal is not positive evidence of a wrong \
             answer ({refused})"
        );
        let (status, detail, _) = classify_certificate(&arm, Some(&refused), 2, BASE);
        assert_eq!(status, RunStatus::Unvalidated, "{detail}");
        assert!(!scoring_solved(status), "{detail}");
        assert_eq!(
            bench_exit_code(summarize_bench(
                &[RunResult {
                    instance: String::from("t.wcnf"),
                    status,
                    seconds: 1.0,
                    cost: Some(2),
                    detail,
                    authority: String::new(),
                }],
                10.0
            )),
            1,
            "{SUITE}: an unchecked certificate must still fail the sweep"
        );

        std::fs::remove_dir_all(&dir).ok();
    }
}
