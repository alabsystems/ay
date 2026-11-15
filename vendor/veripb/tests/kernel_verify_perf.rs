//! Performance guard for `--kernel-verify`.
//!
//! The corpus instances are tiny, so an accidental quadratic in the kernel
//! replay or the bridge would never show up there. This test generates
//! synthetic instances that are deliberately wide and deep, runs the shipped
//! binary with and without the flag, and bounds both the *absolute* overhead
//! and its *growth* when the instance doubles in size.
//!
//! One shape is not enough: the first version of this guard emitted only
//! `pol 1 2 + 2 * 2 d s;`, which touches neither `pol` stash nor any RUP path,
//! and four separate quadratics survived it. Each shape below pins one class:
//!
//! | shape | what a regression there would look like |
//! |---|---|
//! | `PolChurn` | per-term accumulator rescans in the proved normalizer, across add/multiply/divide/saturate |
//! | `LitStash` | per-axiom re-normalization in the `pol` literal-axiom stash flush |
//! | `WeakenStash` | per-variable re-normalization in the `pol` weakening stash flush |
//! | `RupChain` | trail *membership* by list scan (long trail, narrow reasons) |
//! | `RupWide` | per-step slack re-folds in `rup::check_rup` and in the bridge's hinted search (one wide row propagating everything) |
//! | `RedAutoDischarge` | the per-obligation re-judging of the goals `red` proofgoal *generation* discharges by itself, which is one `substitute()` plus one proved implication chain per touched database constraint |
//! | `CnfWideClause` | per-literal rescans in the **formula cross-check** — the second reader's DIMACS clause dedup, and the bridge's canonicalization of one very wide stored clause |
//!
//! `CnfWideClause` is the only shape whose cost is in `shadow_init` rather
//! than in the per-step replay, and it is here because that path shipped
//! quadratic: `veripb-second-reader`'s clause dedup was a linear scan over the
//! literals already emitted, so one clause of 10k/20k/40k/80k literals cost
//! 87/221/950/4544 ms (~4.6x per doubling) and ~14 s at 160k. It is also the
//! only shape that exercises the CNF path at all; every other formula here is
//! OPB, whose reader was linear throughout.
//!
//! Each shape also asserts what its summary line must contain, so a shape that
//! silently stops exercising its path — because the step became a skip, say —
//! fails here instead of passing very fast.
//!
//! ## Reading a ratio from this file
//!
//! A dedicated efficiency audit measured the accumulated cost of the whole
//! soundness audit on an Apple M5 Max (18 cores, 128 GB, macOS 26.5.2), with
//! release binaries, the in-process `--stats` timer, runs interleaved in
//! *randomized* order, and min and median of 15 repetitions. Over the corpus
//! (449 derivations, mean instance 92 microseconds) HEAD is **+3%** against
//! the last performance-audited commit `b4ddbd26` plain, **+1%** under
//! `--kernel-verify`, and **+7-8%** against upstream `4bb10c2c`. None of the
//! checks added since is individually measurable: the rule-placement lookup is
//! a discriminant match, the order-phase check a `contains` on a six-element
//! slice, the occurrence-index eviction guard sits in a branch the whole corpus
//! enters 263 times, and the parser's checked UTF-8 conversions are linear at
//! 8.6 ms per 64k comment lines.
//!
//! **Do not read a single shape's ratio as a regression without controlling
//! for code layout.** `WeakenStash` under `--kernel-verify` read 1.11x at HEAD,
//! and bisecting gave a non-monotone result that could not be causal. The
//! decisive test was rebuilding HEAD with *one comment line added to an
//! unrelated file*: that alone moved the shape from 1.107 to 1.018 at n=64000
//! and 1.070 to 1.023 at n=128000. LTO code placement is worth about +/-9% on
//! a single shape here. The corpus aggregate is not layout luck — the
//! perturbed binary gives 1.042 where HEAD gives 1.035 — so trust the
//! aggregate, and reproduce a single-shape ratio against a perturbed build
//! before believing it.
//!
//! Two behaviours are super-linear and both are inherent, measured and left
//! alone. One `pol` accumulating n constraints over n distinct variables is
//! exponent 1.99 (107 ms at n=16000) because the cost is the sum of the
//! accumulator width, ~n^2/2 term merges at memcpy speed; capping the
//! accumulator at 1 or 16 terms returns it to exponent 0.98-1.02, so it is the
//! width and not a rescan. And `--kernel-verify` re-judging the obligations
//! that `red` proofgoal generation discharges by itself is exactly n(n+1)/2
//! implications (125250 at n=500, 2001000 at n=2000), exponent 2.02 against
//! 1.02 with the flag off — which is what the flag promises, since the plain
//! checker discharges those obligations by not looking at them. `RedAutoDischarge`
//! above is the shape that pins the second one.
//!
//! The budgets are deliberately close to the measured cost. At the sizes below
//! every shape's overhead is a few tens of milliseconds; the pre-audit
//! quadratic bridge took seconds to minutes on the same inputs, so it misses
//! by two orders of magnitude rather than by the 300x slack the original
//! `plain * 10 + 3s` envelope allowed.
//!
//! ## The growth cap is a wall-clock ratio, and is treated as one
//!
//! The absolute budget catches a *full* quadratic on its own. What only the
//! growth cap can see is a milder super-linearity — measured: an
//! `O(terms²/128)` term added to the proved normalizer keeps the flagged run
//! at 192 ms against a 340 ms budget while growing 3.2x per doubling — so the
//! cap has to stay tight, and its cost is a nonzero false-alarm rate. One was
//! observed at 3.86x in a plain `cargo test --release --workspace` against a
//! steady state of ~2.1x. Three things follow, and all three are implemented
//! below rather than paid for by loosening `GROWTH_CAP`:
//!
//! * a violation is **re-measured** (`GROWTH_ATTEMPTS`) and fails only if
//!   every attempt exceeds the cap, with all the ratios in the message;
//! * plain and flagged runs are **interleaved**, so a load transient does not
//!   land entirely in the numerator;
//! * a shape whose overhead is under `GROWTH_FLOOR` **escalates its `n`**
//!   instead of skipping the check with a bare `continue`. That skip used to
//!   be silent and machine-dependent: on fast hardware some shapes sat under
//!   the floor permanently and one straddled it between runs, so the only
//!   super-linearity check this file has was not running for them, and the
//!   trial still reported that overhead "stays linear across every replay
//!   shape". A shape that cannot clear the floor after `MAX_ESCALATIONS`
//!   doublings now fails and says so.
//!
//! It was written for the fork's former CI job, `cargo nextest run --workspace
//! --release`, i.e. with other test binaries running concurrently, so the
//! guard tolerates suite-wide process parallelism by design.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

/// Absolute envelope: a multiple of the unflagged run plus a fixed allowance
/// for process start-up and the kernel replay's own constant factor.
const BUDGET_FACTOR: u32 = 5;
const BUDGET_CONSTANT: Duration = Duration::from_millis(200);

/// Growth cap: doubling the instance may at most triple the *overhead*
/// (measured linear growth is ~2.0x; a quadratic is ~4x). It is the geometric
/// midpoint of the two, which is where it belongs; the fix for the occasional
/// false alarm is `GROWTH_ATTEMPTS`, not a looser cap.
const GROWTH_CAP: f64 = 3.0;

/// Below this the overhead is process noise, and the ratio would be a coin
/// flip. A shape under the floor is **not** skipped: `n` is doubled and the
/// pair re-measured (see `MAX_ESCALATIONS`).
const GROWTH_FLOOR: Duration = Duration::from_millis(10);

/// How many times a shape whose overhead is under `GROWTH_FLOOR` may double
/// its `n` before the trial gives up and fails.
///
/// Escalating beats hard-coding a bigger base size in `SHAPES`: the base that
/// clears 10 ms on a CI runner is ~4x oversized on a fast laptop and wrong
/// again on the next machine, whereas escalation is self-calibrating and costs
/// nothing where the base already suffices.
const MAX_ESCALATIONS: u32 = 3;

/// A ratio of two wall-clock measurements has a nonzero false-alarm rate --
/// one was observed at 3.86x in a plain `cargo test --release --workspace`,
/// against a steady state of ~2.1x -- so a violation is re-measured before it
/// fails the trial. Cost is zero on the happy path.
const GROWTH_ATTEMPTS: usize = 3;

/// Wide `pol` churn: add, multiply, divide, saturate over `n`-term rows.
const POL_LINES: usize = 30;

/// `red` steps in the auto-discharge shape; each one discharges every
/// database constraint the witness satisfies.
const RED_LINES: usize = 20;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Shape {
    PolChurn,
    LitStash,
    WeakenStash,
    RupChain,
    RupWide,
    RedAutoDischarge,
    CnfWideClause,
}

use Shape::*;

/// Every shape, with the base size it is measured at. The sizes differ because
/// the shapes cost very different amounts per unit: `PolChurn` does
/// `POL_LINES` passes over each row, the others one.
const SHAPES: &[(Shape, usize)] = &[
    (PolChurn, 4_000),
    (LitStash, 64_000),
    (WeakenStash, 64_000),
    (RupChain, 64_000),
    (RupWide, 64_000),
    (RedAutoDischarge, 10_000),
    (CnfWideClause, 80_000),
];

impl Shape {
    fn name(self) -> &'static str {
        match self {
            PolChurn => "pol churn",
            LitStash => "pol literal-axiom stash",
            WeakenStash => "pol weakening stash",
            RupChain => "rup with a long trail",
            RupWide => "rup over one wide row",
            RedAutoDischarge => "red auto-discharged proofgoals",
            CnfWideClause => "cnf formula cross-check",
        }
    }

    /// The formula file's extension, which is how both the checker and the
    /// cross-check resolve the format.
    fn formula_extension(self) -> &'static str {
        match self {
            CnfWideClause => "cnf",
            _ => "opb",
        }
    }

    /// `(counter, minimum)`: what the `kernel-verify:` line must show, so the
    /// trial cannot pass because the work stopped being done — a step that
    /// turned into a skip would otherwise look like a large speed-up.
    fn must_verify(self, n: usize) -> (&'static str, usize) {
        match self {
            PolChurn => ("pol", POL_LINES),
            LitStash | WeakenStash => ("pol", 1),
            RupChain | RupWide => ("rup", 1),
            RedAutoDischarge => ("implication", n * RED_LINES),
            // `N formula constraint(s) ... cross-checked against the file on
            // disk`. The whole shape is that comparison, and a stand-down
            // (an unreadable file, a reader refusal) reports zero here while
            // costing nothing -- exactly the speed-up this assertion exists
            // to refuse.
            CnfWideClause => ("formula", 1),
        }
    }

    /// Whether the shape's whole run must sit inside the proved fragment.
    /// `red` carries its unmodelled witness step by construction.
    fn fully_covered(self) -> bool {
        self != RedAutoDischarge
    }

    fn write(self, dir: &Path, n: usize) -> (PathBuf, PathBuf) {
        let opb = dir.join(format!(
            "perf_{}.{}",
            self as usize,
            self.formula_extension()
        ));
        let pbp = dir.join(format!("perf_{}.pbp", self as usize));
        let mut f = std::io::BufWriter::new(std::fs::File::create(&opb).unwrap());
        let mut p = std::io::BufWriter::new(std::fs::File::create(&pbp).unwrap());
        writeln!(p, "pseudo-Boolean proof version 3.0").unwrap();
        match self {
            PolChurn => {
                writeln!(f, "* #variable= {n} #constraint= 2").unwrap();
                for coeff in [2, 3] {
                    for v in 1..=n {
                        write!(f, "{coeff} {}x{v} ", if coeff == 3 { "~" } else { "" }).unwrap();
                    }
                    writeln!(f, ">= {n} ;").unwrap();
                }
                writeln!(p, "f 2;").unwrap();
                for _ in 0..POL_LINES {
                    writeln!(p, "pol 1 2 + 2 * 2 d s;").unwrap();
                }
            }
            LitStash | WeakenStash => {
                // One n-term row, and one `pol` line that either adds n
                // literal axioms to it or weakens all n variables away.
                writeln!(f, "* #variable= {n} #constraint= 1").unwrap();
                for v in 1..=n {
                    write!(f, "1 x{v} ").unwrap();
                }
                writeln!(f, ">= 1 ;").unwrap();
                writeln!(p, "f 1;").unwrap();
                write!(p, "pol 1").unwrap();
                let op = if self == LitStash { '+' } else { 'w' };
                for v in 1..=n {
                    write!(p, " x{v} {op}").unwrap();
                }
                writeln!(p, " ;").unwrap();
            }
            RupChain => {
                // A unit and an implication chain: propagating x1 walks the
                // whole chain, so the trail is n long and every reason is a
                // two-term clause.
                writeln!(f, "* #variable= {n} #constraint= {n}").unwrap();
                writeln!(f, "1 x1 >= 1 ;").unwrap();
                for v in 2..=n {
                    writeln!(f, "1 ~x{} 1 x{v} >= 1 ;", v - 1).unwrap();
                }
                writeln!(p, "f {n};").unwrap();
                writeln!(p, "rup 1 x{n} >= 1 ;").unwrap();
            }
            RupWide => {
                // One n-term cardinality row that propagates all n of its
                // literals, and a unit that then conflicts. Hinted, so the
                // bridge's own propagation search runs as well as the kernel's
                // certificate replay.
                writeln!(f, "* #variable= {n} #constraint= 2").unwrap();
                for v in 1..=n {
                    write!(f, "1 x{v} ").unwrap();
                }
                writeln!(f, ">= {n} ;").unwrap();
                writeln!(f, "1 ~x1 >= 1 ;").unwrap();
                writeln!(p, "f 2;").unwrap();
                writeln!(p, "rup >= 1 : 1 2 ;").unwrap();
            }
            RedAutoDischarge => {
                // Every constraint contains `x0`, so the witness `x0 -> 1`
                // satisfies all n of them: none becomes a proof goal, and all
                // n are discharged inside goal generation on the implication
                // `C |= C|w`. Each `red` line therefore costs n substitutions
                // and n proved implication chains under the flag.
                writeln!(f, "* #variable= {} #constraint= {n}", n + RED_LINES + 2).unwrap();
                for v in 1..=n {
                    writeln!(f, "1 x0 1 y{v} >= 1 ;").unwrap();
                }
                writeln!(p, "f {n};").unwrap();
                for k in 1..=RED_LINES {
                    writeln!(p, "red 1 x0 1 z{k} >= 1 : x0 -> 1 ;").unwrap();
                }
            }
            CnfWideClause => {
                // One DIMACS clause of n distinct literals, plus a second,
                // tiny clause so the constraint count is not one. The proof
                // does nothing at all: the work being timed is `shadow_init`
                // reading the file a second time through
                // `veripb-second-reader` and comparing the two readings, and
                // any proof step would only add noise to that measurement.
                writeln!(f, "p cnf {n} 2").unwrap();
                for v in 1..=n {
                    // Alternate the sign so the dedup key is exercised as the
                    // (variable, polarity) pair it is, not just a variable.
                    write!(f, "{}{v} ", if v % 2 == 0 { "-" } else { "" }).unwrap();
                }
                writeln!(f, "0").unwrap();
                writeln!(f, "1 0").unwrap();
                writeln!(p, "f 2;").unwrap();
            }
        }
        writeln!(p, "output NONE;").unwrap();
        writeln!(p, "conclusion NONE;").unwrap();
        writeln!(p, "end pseudo-Boolean proof;").unwrap();
        drop(f);
        drop(p);
        (opb, pbp)
    }
}

/// The value of `<count> <label>` in the summary line.
fn counter(summary: &str, label: &str) -> usize {
    // Token-wise, so that `implication` does not match inside
    // `substituted-implication`.
    let tokens: Vec<&str> = summary.split_whitespace().collect();
    tokens
        .windows(2)
        .find(|w| w[1].trim_end_matches(',') == label)
        .and_then(|w| w[0].parse().ok())
        .unwrap_or_else(|| panic!("no `{label}` counter in: {summary}"))
}

fn run(shape: Shape, n: usize, opb: &Path, pbp: &Path, kernel_verify: bool) -> Duration {
    let mut cmd = std::process::Command::new(env!("CARGO_BIN_EXE_veripb"));
    if kernel_verify {
        cmd.arg("--kernel-verify");
    }
    let start = Instant::now();
    let out = cmd.arg(opb).arg(pbp).output().unwrap();
    let elapsed = start.elapsed();
    assert!(
        out.status.success(),
        "the synthetic {} instance must verify (kernel_verify={kernel_verify}): {}",
        shape.name(),
        String::from_utf8_lossy(&out.stderr)
    );
    if kernel_verify {
        let stdout = String::from_utf8_lossy(&out.stdout);
        let summary = stdout
            .lines()
            .find(|l| l.starts_with("kernel-verify:"))
            .expect("kernel-verify summary line");
        let (label, minimum) = shape.must_verify(n);
        let got = counter(summary, label);
        assert!(
            got >= minimum,
            "the {} shape must still exercise its path (>= {minimum} {label}, got {got}): {summary}",
            shape.name()
        );
        assert!(
            !shape.fully_covered() || summary.contains("nothing outside the proved fragment"),
            "the {} shape must stay inside the proved fragment, or it is timing a skip: {summary}",
            shape.name()
        );
    }
    elapsed
}

/// `flagged - plain`, floored at zero, as a best-of-three of each side.
///
/// The minimum is the right statistic for a lower bound on cost: it is the run
/// least disturbed by whatever else the machine is doing. The two sides are
/// measured **interleaved** rather than in two phases, because the quantity
/// that matters is their *difference*: a load transient confined to one phase
/// would otherwise land entirely in the numerator of the growth ratio, which
/// is the mechanism behind the one false alarm this guard has produced.
fn overhead(shape: Shape, n: usize, opb: &Path, pbp: &Path) -> (Duration, Duration, Duration) {
    let mut plain = Duration::MAX;
    let mut flagged = Duration::MAX;
    for _ in 0..3 {
        plain = plain.min(run(shape, n, opb, pbp, false));
        flagged = flagged.min(run(shape, n, opb, pbp, true));
    }
    (plain, flagged, flagged.saturating_sub(plain))
}

fn measure(shape: Shape, n: usize, dir: &Path) -> Result<(Duration, Duration), String> {
    let (opb, pbp) = shape.write(dir, n);
    // Warm-up, to keep file-cache cost out of the first measurement.
    run(shape, n, &opb, &pbp, false);
    let (plain, flagged, over) = overhead(shape, n, &opb, &pbp);
    let budget = plain * BUDGET_FACTOR + BUDGET_CONSTANT;
    if flagged > budget {
        return Err(format!(
            "kernel-verify overhead on the {} shape at n={n} exceeds its budget: \
             plain={plain:?}, flagged={flagged:?}, budget={budget:?}",
            shape.name()
        ));
    }
    Ok((over, flagged))
}

fn main() {
    let args = libtest_mimic::Arguments::from_args();
    // ONE trial: libtest-mimic runs trials in parallel by default, and
    // concurrent trials would contend for the CPU and corrupt each other's
    // timings. The shapes are measured sequentially inside it.
    let tests = vec![
        libtest_mimic::Trial::test(
            "kernel-verify overhead stays linear across every replay shape",
            || {
                // These budgets are calibrated against the release binary, which
                // is the one users run and the only one whose speed is a claim
                // this repository makes. An unoptimized build misses them by an
                // order of magnitude for reasons that say nothing about the
                // kernel replay -- and the default test profile is dev, so
                // without this the guard is a false alarm rather than a signal.
                // `targo --unverified test --release` is where it bites.
                if cfg!(debug_assertions) {
                    eprintln!(
                        "skipped: the overhead budgets are calibrated for the \
                     release profile; run `targo --unverified test --release \
                     --test kernel_verify_perf` to exercise this guard"
                    );
                    return Ok(());
                }
                let dir = tempfile::tempdir().unwrap();
                let mut report = String::new();
                for &(shape, base) in SHAPES {
                    // Each measurement is an interleaved best-of-three of the
                    // plain and the flagged run, which is what absorbs machine
                    // jitter. If the smaller overhead lands under `GROWTH_FLOOR`
                    // the ratio would be dividing noise, so `n` is doubled and the
                    // pair re-measured until it clears -- the growth check is
                    // never silently skipped, on any machine.
                    let mut n = base;
                    let (small, large, flagged) = loop {
                        let (small, _) = measure(shape, n, dir.path())?;
                        let (large, flagged) = measure(shape, 2 * n, dir.path())?;
                        if small >= GROWTH_FLOOR {
                            break (small, large, flagged);
                        }
                        let doublings = (n / base).trailing_zeros();
                        if doublings >= MAX_ESCALATIONS {
                            return Err(format!(
                                "the {} shape's kernel-verify overhead is still {small:?} at \
                             n={n}, below the {GROWTH_FLOOR:?} floor after {MAX_ESCALATIONS} \
                             doublings from its base of {base}, so its growth cap -- the only \
                             super-linearity check this guard has -- cannot be evaluated at \
                             all. Raise that shape's base size in `SHAPES`.\n{report}",
                                shape.name()
                            )
                            .into());
                        }
                        report.push_str(&format!(
                            "  {:<26} n={n:<7} overhead {small:?} below the {GROWTH_FLOOR:?} \
                         floor; escalating to n={}\n",
                            shape.name(),
                            2 * n
                        ));
                        n *= 2;
                    };

                    // A ratio over the cap is re-measured before it fails: it is a
                    // wall-clock quantity with a real false-alarm rate, and a perf
                    // guard that cries wolf is a guard people learn to re-run.
                    // Below-floor retries count as "not a violation": a
                    // measurement that small is not evidence of anything.
                    let mut attempts = vec![Some(large.as_secs_f64() / small.as_secs_f64())];
                    while attempts.len() < GROWTH_ATTEMPTS
                        && attempts
                            .last()
                            .is_some_and(|g| g.is_some_and(|g| g > GROWTH_CAP))
                    {
                        let (small, _) = measure(shape, n, dir.path())?;
                        let (large, _) = measure(shape, 2 * n, dir.path())?;
                        attempts.push(
                            (small >= GROWTH_FLOOR)
                                .then(|| large.as_secs_f64() / small.as_secs_f64()),
                        );
                    }
                    let ratios = attempts
                        .iter()
                        .map(|g| match g {
                            Some(g) => format!("{g:.2}"),
                            None => "below-floor".to_string(),
                        })
                        .collect::<Vec<_>>()
                        .join(", ");
                    report.push_str(&format!(
                        "  {:<26} n={n:<7} overhead {small:?} -> {large:?} \
                     (flagged {flagged:?}, growth {ratios})\n",
                        shape.name()
                    ));
                    if attempts.iter().all(|g| g.is_some_and(|g| g > GROWTH_CAP)) {
                        return Err(format!(
                            "kernel-verify overhead on the {} shape grows super-linearly: \
                         {small:?} at n={n} vs {large:?} at n={}, growth {ratios} over \
                         {} independent measurements, against a cap of {GROWTH_CAP} \
                         (a quadratic doubles to ~4x)\n{report}",
                            shape.name(),
                            2 * n,
                            attempts.len()
                        )
                        .into());
                    }
                }
                // Printed only on `--nocapture`, but it is what makes a future
                // budget adjustment a measurement rather than a guess.
                println!("kernel-verify replay overhead by shape:\n{report}");
                Ok(())
            },
        )
        // In the dev profile the trial is *ignored* rather than trivially
        // passing, so the run summary reads `0 passed; 1 ignored` instead of an
        // `ok` for a trial that measured nothing -- the convention
        // `tests/integration.rs` and `tests/kernel_verify.rs` already use for
        // excluded instances. The in-body `cfg!(debug_assertions)` early return
        // stays as well, because `--include-ignored` still runs the body and must
        // not turn a deliberate ignored-run into a spurious budget failure.
        .with_ignored_flag(cfg!(debug_assertions)),
    ];
    libtest_mimic::run(&args, tests).exit();
}
