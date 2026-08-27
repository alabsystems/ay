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

/// Known local build locations, tried after `$PATH`.
fn known_build_locations() -> Vec<PathBuf> {
    if let Some(raw) = std::env::var_os(SEARCH_PATH_ENV) {
        return std::env::split_paths(&raw).collect();
    }
    let mut candidates = vec![PathBuf::from("/tmp/veripb-3/bin/veripb")];
    let cache = std::env::var_os("XDG_CACHE_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".cache")));
    if let Some(cache) = cache {
        let cache = cache.join("ay-veripb");
        candidates.push(cache.join(pinned_build_id()).join("target/release/veripb"));
        // Compatibility with the original unkeyed cache populated by
        // scripts/cert_ci.sh. The pinned path above comes first: its directory
        // identity covers both the upstream commit and the reviewed patch.
        candidates.push(cache.join("VeriPB/target/release/veripb"));
    }
    if let Some(home) = std::env::var_os("HOME") {
        candidates.push(PathBuf::from(home).join(".cargo/bin/veripb"));
    }
    candidates
}

/// Cache-key contract shared with `scripts/ci/pb_certified_gate.sh`.
///
/// EVERY patch is part of the checker identity, so a changed or added patch
/// must not silently reuse a binary built from the same upstream commit. Both
/// prefixes are in the key for that reason.
fn pinned_build_id() -> String {
    let patch_sha = pin::patch_sha256();
    let patch_prefix = patch_sha.get(..12).unwrap_or(patch_sha);
    let patch2_sha = pin::patch2_sha256();
    let patch2_prefix = patch2_sha.get(..12).unwrap_or(patch2_sha);
    format!("{}-{patch_prefix}-{patch2_prefix}", pin::commit())
}

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
    NotFound { searched: Vec<String> },
    /// A binary was found but does not behave like a VeriPB checker.
    SelfTestFailed { checker: PathBuf, detail: String },
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
            Self::NotFound { searched } => write!(
                formatter,
                "no VeriPB checker found. Searched, in order: {}. \
                 Install VeriPB, put `veripb` on PATH, or set VERIPB_BIN.",
                searched.join(", ")
            ),
            Self::SelfTestFailed { checker, detail } => write!(
                formatter,
                "`{}` was resolved as the VeriPB checker but failed its self-test \
                 (a real checker must verify a known-good proof and reject a known-bad one): {detail}",
                checker.display()
            ),
        }
    }
}

/// Locate a checker without running the self-test.
///
/// Order: `VERIPB_BIN`, `AY_PB26_VERIPB_BIN`, `VERIPB`, then `$PATH`, then the
/// known local build locations. An environment override that does not name an
/// existing file is an ERROR, not a reason to fall through — a typo in
/// `VERIPB_BIN` must never silently degrade to "checker absent".
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
    searched.push(String::from("$PATH/veripb"));
    if let Some(found) = path_lookup() {
        return Ok(found);
    }
    for candidate in known_build_locations() {
        searched.push(candidate.display().to_string());
        if candidate.is_file() {
            return Ok(candidate);
        }
    }
    Err(ResolveError::NotFound { searched })
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

fn resolve_once() -> &'static Result<PathBuf, ResolveError> {
    static RESOLVED: OnceLock<Result<PathBuf, ResolveError>> = OnceLock::new();
    RESOLVED.get_or_init(|| {
        let checker = locate()?;
        match self_test(&checker) {
            Ok(()) => Ok(checker),
            Err(detail) => Err(ResolveError::SelfTestFailed { checker, detail }),
        }
    })
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
/// A resolved-but-bogus checker (self-test failure) always panics: the opt-out
/// excuses an ABSENT checker, never a FAKE one.
#[must_use]
pub fn require_checker(suite: &str) -> Option<PathBuf> {
    match resolve() {
        Ok(checker) => Some(checker),
        Err(error @ ResolveError::SelfTestFailed { .. }) => panic!(
            "{suite}: the resolved VeriPB checker is not a working checker.\n{error}\n\
             This suite refuses to run against a binary that cannot check proofs."
        ),
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
/// The pin names TWO patch files ([`patch`] and [`patch2`]); both are part of
/// the checker's identity and both are in the build-cache key.
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

    /// Repo-relative path of the SECOND patch, applied on top of [`patch`].
    ///
    /// It exists as a separate file on purpose: [`patch`] is byte-verifiable
    /// against the private fork, and folding a locally written fix into it would
    /// destroy that property. This one is written here and may be edited here.
    /// See the prose in `ci/veripb.pin`.
    #[must_use]
    pub fn patch2() -> &'static str {
        require("VERIPB_PATCH2")
    }

    /// Expected SHA-256 of [`patch2`], the fix for the ninth and tenth
    /// wrong-verdict defects (`pol` addition wrapping the cancellation
    /// subtraction, and the propagator computing its slack in the row's own
    /// integer width).
    #[must_use]
    pub fn patch2_sha256() -> &'static str {
        require("VERIPB_PATCH2_SHA256")
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
            assert_eq!(
                patch2_sha256().len(),
                64,
                "patch2 sha256 must be 64 hex chars"
            );
            assert_ne!(
                patch_sha256(),
                patch2_sha256(),
                "the two patches must be different files"
            );
            assert!(!version().is_empty());
        }

        #[test]
        fn the_pinned_patches_match_their_recorded_hashes() {
            use sha2::{Digest, Sha256};
            for (path, expected, key) in [
                (patch(), patch_sha256(), "VERIPB_PATCH_SHA256"),
                (patch2(), patch2_sha256(), "VERIPB_PATCH2_SHA256"),
            ] {
                let path = repo_root().join(path);
                let bytes = std::fs::read(&path).unwrap_or_else(|error| {
                    panic!("pinned patch {} unreadable: {error}", path.display())
                });
                let digest = format!("{:x}", Sha256::digest(&bytes));
                assert_eq!(
                    digest,
                    expected,
                    "{} does not match {key} in {PIN_PATH}. The patches are part of \
                     the checker's identity — update both together.",
                    path.display()
                );
            }
        }

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

    #[test]
    fn pinned_cache_key_matches_the_shell_gate_contract() {
        assert_eq!(
            pinned_build_id(),
            format!(
                "{}-{}-{}",
                pin::commit(),
                &pin::patch_sha256()[..12],
                &pin::patch2_sha256()[..12]
            )
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
