//! `--kernel-verify` corpus pins.
//!
//! Five properties. Only the first runs over the whole instance corpus; the
//! second and third run over the *accepted* corpus (`tests/instances/correct/`)
//! and the last two over named instances:
//!
//! 1. **Verdict-neutrality** (in-process, whole corpus): the flag never changes
//!    accept vs reject; a kernel/checker divergence turns an accept into a
//!    reject and fails here.
//! 2. **Coverage snapshot** (via the binary, accepted corpus only): the per-instance
//!    `kernel-verify:` summary — how many pol/rup/contradiction/solution/
//!    implication checks were re-derived and what was skipped — must match
//!    `tests/kernel_verify_expected.txt` byte for byte. A hook that silently
//!    goes dead (a check that stops firing) shows up as a count drop; a step
//!    that silently stops being counted shows up as a skip drop. Regenerate
//!    deliberately with `KERNEL_VERIFY_BLESS=1 targo --unverified test --release
//!    --test kernel_verify` after reviewing the diff.
//! 3. **Composition snapshot**, in the same file under the `[compose]`
//!    keys: the per-instance `kernel-compose:` line, which says whether the
//!    run's refutation is certified end to end by the shadow database and
//!    what the taint census is. A regression here means a rule stopped
//!    feeding the shadow, or started feeding it something it should not.
//!    (Items 2 and 3 are one trial over one file; they are listed apart
//!    because they pin different things about the same run.)
//! 4. **Pinned fully-composed instances**, so that "every corpus instance
//!    reports NOT composed" cannot become the silently passing steady state:
//!    the `COMPOSED_PINS` corpus instances, plus a synthetic `rup` refutation
//!    built in a temp directory.
//! 5. **Formula cross-check pins** (`FORMULA_CROSS_CHECK_PINS`): the
//!    independent reader in `veripb-second-reader` must agree with what the
//!    checker stored, on named instances chosen to span `.opb`, `.cnf`,
//!    `.wcnf` and a `max:` objective.
//!
//! The `INTEGRATION-TEST:` marker vocabulary is `tests/integration.rs`'s and
//! is honoured here too, `lenient-header-counts` included: an instance run
//! without a flag it needs is rejected for a reason that has nothing to do
//! with what it pins, which makes its neutrality trial pass vacuously and
//! drops it out of the coverage snapshot.
//!
//! Instances marked `INTEGRATION-TEST: ignore(check)` or `ignore(both)` run
//! as *ignored* trials and stay out of the coverage snapshot (the plain
//! checker rejects them for unrelated reasons); `ignore(elaborate)` instances
//! still check and are therefore included. How many shipped instances carry an
//! exclusion marker is not written down here, because it has changed twice and
//! the sentence that recorded it went stale both times: read the `N ignored`
//! figure in this harness's own run summary, which is exactly what the marker
//! is routed through so that an exclusion is visible rather than a silently
//! missing trial. What is worth knowing is the *shape*: an excluded instance
//! is one the plain checker rejects for a reason unrelated to what it pins,
//! and only an instance under `correct/` was ever in the coverage snapshot to
//! begin with.

use anyhow::Context as _;
use std::collections::BTreeMap;
use std::io::BufRead;
use std::path::{Path, PathBuf};

fn main() {
    let args = libtest_mimic::Arguments::from_args();
    let mut tests = vec![];
    let mut snapshot_instances: Vec<(String, PathBuf, Flags)> = vec![];

    for correct in [true, false] {
        for version in ["version2", "version3"] {
            for derivation in glob::glob(&format!(
                "./tests/instances/{}/{version}/*.pbp",
                if correct { "correct" } else { "incorrect" }
            ))
            .unwrap()
            .flatten()
            {
                let id = derivation.file_stem().unwrap().to_str().unwrap();
                let marker = if version == "version2" { '*' } else { '%' };
                let mut second_line = String::new();
                let mut reader = std::io::BufReader::new(
                    std::fs::File::open(&derivation).expect("failed to read derivation"),
                );
                reader.read_line(&mut second_line).unwrap();
                second_line.clear();
                reader.read_line(&mut second_line).unwrap();
                // Only a broken *check* excludes an instance; ignore(elaborate)
                // instances still exercise the checking path. An excluded
                // instance becomes an *ignored* trial rather than vanishing,
                // so `cargo test`'s "N ignored" line makes the exclusion a
                // visible event instead of a missing one.
                let trimmed = second_line.trim();
                let ignored = trimmed == format!("{marker} INTEGRATION-TEST: ignore(check)")
                    || trimmed == format!("{marker} INTEGRATION-TEST: ignore(both)");
                let force_checked_deletion =
                    trimmed != format!("{marker} INTEGRATION-TEST: allow-unchecked-deletion");
                // Same marker vocabulary as `tests/integration.rs`. Without it an accepted
                // instance whose `p cnf` header deliberately disagrees with its file would be
                // rejected here for that reason alone: the neutrality trial would pass
                // vacuously (both runs reject) and the instance would silently drop out of the
                // coverage snapshot.
                let lenient_header_counts =
                    trimmed == format!("{marker} INTEGRATION-TEST: lenient-header-counts");
                let flags = Flags {
                    force_checked_deletion,
                    lenient_header_counts,
                };

                if correct && !ignored {
                    snapshot_instances.push((
                        format!("{version}::{id}"),
                        derivation.clone(),
                        flags,
                    ));
                }

                let deriv = derivation.clone();
                tests.push(
                    libtest_mimic::Trial::test(
                        format!("{version}::{id} (kernel-verify verdict-neutral)"),
                        move || {
                            check_neutrality(&deriv, flags).map_err(|e| format!("{e:#}").into())
                        },
                    )
                    .with_ignored_flag(ignored),
                );
            }
        }
    }

    snapshot_instances.sort();
    tests.push(libtest_mimic::Trial::test(
        "coverage snapshot matches tests/kernel_verify_expected.txt",
        move || check_snapshot(&snapshot_instances).map_err(|e| format!("{e:#}").into()),
    ));

    for pin in COMPOSED_PINS {
        tests.push(libtest_mimic::Trial::test(
            format!("version3::{pin} composes end to end"),
            move || check_composed(pin).map_err(|e| format!("{e:#}").into()),
        ));
    }
    tests.push(libtest_mimic::Trial::test(
        "a synthetic rup refutation composes end to end",
        || check_rup_composes().map_err(|e| format!("{e:#}").into()),
    ));

    tests.push(libtest_mimic::Trial::test(
        "end-to-end coverage has not gone backwards",
        || check_coverage_floor().map_err(|e| format!("{e:#}").into()),
    ));

    for pin in FORMULA_CROSS_CHECK_PINS {
        tests.push(libtest_mimic::Trial::test(
            format!("version3::{} cross-checks its formula file", pin.0),
            move || check_formula_cross_check(pin).map_err(|e| format!("{e:#}").into()),
        ));
    }

    libtest_mimic::run(&args, tests).exit();
}

/// The end-to-end coverage floor, read off the snapshot the run just agreed
/// with.
///
/// The snapshot pins coverage EXACTLY, which is the stronger check but points
/// the wrong way for this one question: a snapshot is blessed, and a bless
/// accepts a drop as readily as a gain. Nothing else in this file objects if
/// composition walks from sixteen instances down to three, so long as the
/// expected file is regenerated in the same commit. These three numbers are
/// the direction: they may rise and be re-pinned, and a fall is an error.
///
/// `COMPOSED_FLOOR` is the count that matters most and the one most easily
/// misread. Of the corpus, most instances have no refutation conclusion to
/// compose at all (a decision or optimization run ends in a bound, not a
/// contradiction), and counting those as successes turns 66 into 308. They
/// are excluded here: the floor is over instances that actually reach a
/// refutation, of which 66 do, and ALL 66 currently carry a kernel-justified
/// chain all the way to it. That ratio is the honest end-to-end number for
/// this checker.
///
/// They compose under ONE induction, `VeriPbCore.DbOkF`, but its verdict has
/// three shapes and the distinction is not bookkeeping -- it is what each run
/// is entitled to claim:
///
/// - 24 by `full_unsat`: the stored formula is unsatisfiable.
/// - 37 by `full_complete` reporting a BOUND: no assignment satisfying it has
///   objective value below the established bound. Such a formula is typically
///   SATISFIABLE -- and for the `obji` and asserted-bound runs nothing
///   achieving the bound is exhibited at all, which that leg does not require.
/// - 5 by `full_complete` reporting an ENUMERATION: it has no models beyond
///   the ones exhibited.
///
/// A run that logged a solution cannot claim the first, so the summary names
/// the theorem it actually used rather than the strongest one available.
///
/// `NOT_COMPOSED_CEILING` is ZERO, which makes it the sharpest pin in this
/// file: any instance that stops composing fails here, with no slack at all.
const COMPOSED_FLOOR: usize = 66;

/// Steps re-derived by the proved kernel across the accepted corpus, summed
/// over every per-rule counter in the snapshot. This is the breadth number:
/// it falls if a rule stops being routed through the kernel, even when every
/// instance still reaches the same verdict.
const REDERIVED_STEPS_FLOOR: usize = 5485;

/// Instances that reach a refutation but cannot compose. A CEILING, not a
/// floor: it falls as the proved fragment grows, and a rise means a step that
/// used to be kernel-justified now is not.
const NOT_COMPOSED_CEILING: usize = 0;

/// Check the three coverage magnitudes against their pins, from the expected
/// snapshot -- which the trial above has already checked against this run, so
/// reading it here is reading what actually happened.
fn check_coverage_floor() -> anyhow::Result<()> {
    let text = std::fs::read_to_string("./tests/kernel_verify_expected.txt")
        .context("read tests/kernel_verify_expected.txt")?;
    let (mut composed, mut not_composed, mut steps) = (0usize, 0usize, 0usize);
    for line in text.lines() {
        if line.contains("[compose]") {
            // An instance with no refutation conclusion is neither a success
            // nor a failure of composition, and is counted as neither.
            if line.contains("no refutation conclusion") {
            } else if line.contains("NOT composed") {
                not_composed += 1;
            } else {
                composed += 1;
            }
        } else {
            steps += rederived_steps(line);
        }
    }

    let mut wrong = Vec::new();
    if composed < COMPOSED_FLOOR {
        wrong.push(format!(
            "{composed} instance(s) compose end to end, below the pinned floor of \
             {COMPOSED_FLOOR}"
        ));
    }
    if steps < REDERIVED_STEPS_FLOOR {
        wrong.push(format!(
            "{steps} step(s) re-derived by the kernel, below the pinned floor of \
             {REDERIVED_STEPS_FLOOR}"
        ));
    }
    if not_composed > NOT_COMPOSED_CEILING {
        wrong.push(format!(
            "{not_composed} instance(s) reach a refutation without composing, above the \
             pinned ceiling of {NOT_COMPOSED_CEILING}"
        ));
    }
    if !wrong.is_empty() {
        anyhow::bail!(
            "end-to-end coverage went backwards:\n  {}\n\nThese pins only move one way. \
             If the drop is intended, say so in the commit message and edit the constants \
             in tests/kernel_verify.rs; regenerating the snapshot alone will NOT silence \
             this.",
            wrong.join("\n  ")
        );
    }
    Ok(())
}

/// Sum the per-rule "re-derived by the proved kernel" counters on one
/// `kernel-verify:` line. Counters are matched by NAME rather than by
/// position, so a new rule appearing in the line adds to the total instead of
/// shifting it, and a rule that disappears takes its count with it.
fn rederived_steps(line: &str) -> usize {
    const RULES: &[&str] = &[
        "pol",
        "rup",
        "contradiction",
        "solution",
        "implication",
        "substituted-implication",
        "trivial",
        "db-lookup",
    ];
    let Some((_, body)) = line.split_once("kernel-verify: ") else {
        return 0;
    };
    let Some((counters, _)) = body.split_once(" check(s) re-derived") else {
        return 0;
    };
    counters
        .split(", ")
        .filter_map(|field| {
            let (n, name) = field.trim().split_once(' ')?;
            RULES.contains(&name).then(|| n.parse::<usize>().ok())?
        })
        .sum()
}

/// Instances whose refutation must be certified end to end by the shadow
/// database, one per leg of the `DbOk` induction:
///
/// - `conclusion_UNSAT_no_hint` — `DbOk.init`: the stored formula already
///   contains the contradiction, so the composition rests on the formula
///   load alone;
/// - `variable_form_division` — `DbOk.derive`: a pure `pol` chain (with
///   `e` lookups) derives the contradiction from the formula.
///
/// Pinning these keeps "everything reports NOT composed" from becoming a
/// silently passing steady state: a regression that stops feeding the
/// shadow shows up here as a hard failure, not as snapshot churn.
const COMPOSED_PINS: &[&str] = &["conclusion_UNSAT_no_hint", "variable_form_division"];

/// One instance per input format, with the number of formula constraints and
/// formula objectives the file cross-check must account for.
///
/// The coverage snapshot already carries these counts, but a snapshot is
/// re-blessed and a pin is not: without these, the cross-check going dead
/// everywhere at once would read as an ordinary diff. Each entry is also the
/// only place the *format* coverage is stated — the corpus is overwhelmingly
/// `.opb` (hundreds of files, against 7 `.cnf` and 3 `.wcnf`), so a reader
/// with a broken DIMACS path would otherwise barely show up.
///
/// `solution_logging_max_objective` is here rather than a plainer OPB
/// instance because it is the corpus's only `max:` objective, and the
/// maximize-to-minimize negation is a format decision the reader has to
/// mirror.
const FORMULA_CROSS_CHECK_PINS: &[(&str, usize, usize)] = &[
    ("variable_form_division", 4, 0),
    ("solution_logging_max_objective", 3, 1),
    ("cnf_opposing_literals", 2, 0),
    ("wcnf_literal_spelling_canonical", 2, 1),
];

fn formula_for(derivation: &Path) -> PathBuf {
    for ext in ["opb", "cnf", "wcnf"] {
        let f = derivation.with_extension(ext);
        if f.exists() {
            return f;
        }
    }
    derivation.with_extension("opb")
}

/// The sibling `.outopb`, when the instance has one.
///
/// An `output ... FILE` step needs it as the third positional argument;
/// without it the run dies at the `output` line with `NoOutputFormulaGiven`
/// before reaching a verdict, which makes the neutrality trial pass
/// vacuously (both runs reject, for a reason that has nothing to do with the
/// flag) and drops the instance from the coverage snapshot entirely. This
/// mirrors `tests/integration.rs`.
fn output_formula_for(derivation: &Path) -> Option<PathBuf> {
    let f = derivation.with_extension("outopb");
    f.exists().then_some(f)
}

/// The command-line flags an instance's `INTEGRATION-TEST:` marker asks for.
///
/// The vocabulary is `tests/integration.rs`'s; both harnesses have to honour it, or an instance
/// that needs a flag is checked here without it and rejected for an unrelated reason.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Flags {
    force_checked_deletion: bool,
    lenient_header_counts: bool,
}

impl Flags {
    /// What the hand-written pins run with: deletion checked, header counts strict. Every
    /// instance they name is an ordinary `.opb`/`.cnf` whose header agrees with its file.
    fn pinned() -> Self {
        Flags {
            force_checked_deletion: true,
            lenient_header_counts: false,
        }
    }
}

fn run(derivation: &Path, flags: Flags, kernel_verify: bool) -> bool {
    let args = veripb::args::Args {
        formula: formula_for(derivation),
        output_formula: output_formula_for(derivation),
        derivation: derivation.to_path_buf(),
        print_verification_result: false,
        force_checked_deletion: flags.force_checked_deletion,
        lenient_header_counts: flags.lenient_header_counts,
        kernel_verify,
        ..Default::default()
    };
    veripb::run_checker(args).is_ok()
}

fn check_neutrality(derivation: &Path, flags: Flags) -> anyhow::Result<()> {
    let plain = run(derivation, flags, false);
    let kernel = run(derivation, flags, true);
    if plain != kernel {
        anyhow::bail!(
            "verdict changed under --kernel-verify: plain accept={plain}, kernel-verify accept={kernel}"
        );
    }
    Ok(())
}

/// Run the shipped binary and pull the `kernel-verify:` coverage line and
/// the `kernel-compose:` run-level composition line.
///
/// The two are snapshotted under separate keys (`name` and `name
/// [compose]`) so that a coverage change and a composition change never
/// hide inside one diff line.
fn summary_lines(derivation: &Path, flags: Flags) -> anyhow::Result<Option<(String, String)>> {
    let mut cmd = std::process::Command::new(env!("CARGO_BIN_EXE_veripb"));
    if flags.force_checked_deletion {
        cmd.arg("--force-checked-deletion");
    }
    if flags.lenient_header_counts {
        cmd.arg("--lenient-header-counts");
    }
    let out = cmd
        .arg("--kernel-verify")
        .arg(formula_for(derivation))
        .arg(derivation)
        // The third positional argument, when the instance has one.
        // `Option<PathBuf>` is `IntoIterator`, so this is a no-op otherwise.
        .args(output_formula_for(derivation))
        .output()?;
    if !out.status.success() {
        // The neutrality trials report rejects; the snapshot only covers
        // accepted instances.
        return Ok(None);
    }
    let stdout = String::from_utf8_lossy(&out.stdout);
    let pick = |prefix: &str| {
        stdout
            .lines()
            .find(|l| l.starts_with(prefix))
            .map(|l| l.to_string())
    };
    match (pick("kernel-verify:"), pick("kernel-compose:")) {
        (Some(verify), Some(compose)) => Ok(Some((verify, compose))),
        // Both lines are printed together at the end of an accepted run, so
        // one without the other means the summary hook went dead.
        (v, c) => anyhow::bail!(
            "expected both kernel-verify and kernel-compose summary lines, got {v:?} / {c:?}"
        ),
    }
}

/// Assert that a corpus instance's run is fully composed and that nothing in
/// it fell outside the proved fragment.
fn check_composed(id: &str) -> anyhow::Result<()> {
    let derivation = PathBuf::from(format!("./tests/instances/correct/version3/{id}.pbp"));
    let Some((verify, compose)) = summary_lines(&derivation, Flags::pinned())? else {
        anyhow::bail!("{id} did not verify under --kernel-verify");
    };
    assert_composed(id, &verify, &compose)
}

/// Assert that an instance's formula file was read a second time, by
/// `veripb-second-reader`, and found to agree with what the checker stored.
fn check_formula_cross_check(pin: &(&str, usize, usize)) -> anyhow::Result<()> {
    let (id, constraints, objectives) = *pin;
    let derivation = PathBuf::from(format!("./tests/instances/correct/version3/{id}.pbp"));
    let Some((verify, _)) = summary_lines(&derivation, Flags::pinned())? else {
        anyhow::bail!("{id} did not verify under --kernel-verify");
    };
    let expected = format!(
        "{constraints} formula constraint(s) and {objectives} formula objective(s) \
         cross-checked against the file on disk"
    );
    if !verify.contains(&expected) {
        anyhow::bail!("{id} did not report `{expected}`:\n  {verify}");
    }
    // A skip here would mean the second reader stood down, which for a
    // shipped instance means it no longer reads the format.
    if verify.contains("formula-file-unreadable")
        || verify.contains("formula-file-not-rereadable")
        || verify.contains("formula-second-reader-refused")
        || verify.contains("formula-not-kernel-representable")
    {
        anyhow::bail!("{id}'s formula cross-check stood down:\n  {verify}");
    }
    Ok(())
}

fn assert_composed(id: &str, verify: &str, compose: &str) -> anyhow::Result<()> {
    if !compose.starts_with("kernel-compose: COMPOSED") {
        anyhow::bail!(
            "{id} is no longer certified end to end by the shadow database:\n  {compose}"
        );
    }
    // Composition is per-slot, so a run can compose while carrying taints on
    // unrelated branches; these instances are pinned precisely because they
    // have no unmodelled step at all, so any taint means the run changed
    // shape and the pin stopped testing what it was chosen to test.
    //
    // UNJUSTIFIED slots only. A subproof PREMISE is not a taint in this sense
    // -- it is the assumption the subproof discharges, and pinning it to zero
    // would say these instances must never open a subproof, which is not what
    // they were chosen to test.
    if !compose.contains("0 unjustified slot(s)") {
        anyhow::bail!("{id} composed, but the shadow now carries taints:\n  {compose}");
    }
    if !verify.contains("nothing outside the proved fragment") {
        anyhow::bail!("{id} left steps outside the proved fragment:\n  {verify}");
    }
    Ok(())
}

/// The `rup` leg of the composition, which the corpus does not exercise: no
/// shipped instance both concludes `UNSAT` and derives its contradiction by
/// plain reverse unit propagation. The two clauses below have exactly the
/// four-model refutation `x1 x2 | ~x1 | ~x2` needs, and the contradiction is
/// the RUP conclusion itself, so a composed verdict here means a
/// `DStep.rupS` slot really did reach `checker_sound`.
fn check_rup_composes() -> anyhow::Result<()> {
    let dir = tempfile::tempdir()?;
    let opb = dir.path().join("rup_compose.opb");
    let pbp = dir.path().join("rup_compose.pbp");
    std::fs::write(
        &opb,
        "* #variable= 2 #constraint= 3\n\
         1 x1 1 x2 >= 1 ;\n\
         1 ~x1 1 x2 >= 1 ;\n\
         1 ~x2 >= 1 ;\n",
    )?;
    std::fs::write(
        &pbp,
        "pseudo-Boolean proof version 3.0\n\
         f 3;\n\
         rup >= 1 ;\n\
         output NONE;\n\
         conclusion UNSAT;\n\
         end pseudo-Boolean proof;\n",
    )?;
    let Some((verify, compose)) = summary_lines(&pbp, Flags::pinned())? else {
        anyhow::bail!("the synthetic rup refutation did not verify under --kernel-verify");
    };
    if !verify.contains("1 rup") {
        anyhow::bail!("the rup step was not kernel-verified:\n  {verify}");
    }
    assert_composed("synthetic rup refutation", &verify, &compose)
}

fn check_snapshot(instances: &[(String, PathBuf, Flags)]) -> anyhow::Result<()> {
    let mut actual: BTreeMap<String, String> = BTreeMap::new();
    for (name, derivation, flags) in instances {
        if let Some((verify, compose)) = summary_lines(derivation, *flags)? {
            actual.insert(name.clone(), verify);
            actual.insert(format!("{name} [compose]"), compose);
        }
    }
    let rendered: String = actual.iter().map(|(k, v)| format!("{k}: {v}\n")).collect();

    // An instance that produces no summary line is pinned by nothing at all —
    // and its neutrality trial passes vacuously too, both runs having failed
    // for the same unrelated reason. That is how eight `*output*` instances
    // sat uncovered: the harness did not pass their `.outopb`. Checked before
    // the bless early-return, so a re-bless cannot absorb a coverage drop.
    let uncovered: Vec<&str> = instances
        .iter()
        .map(|(name, _, _)| name.as_str())
        .filter(|name| !actual.contains_key(*name))
        .collect();
    if !uncovered.is_empty() {
        anyhow::bail!(
            "{} correct instance(s) produced no kernel-verify summary line and are therefore \
             pinned by nothing (their neutrality trial passes vacuously too): {}",
            uncovered.len(),
            uncovered.join(", ")
        );
    }

    let expected_path = Path::new("tests/kernel_verify_expected.txt");
    if std::env::var_os("KERNEL_VERIFY_BLESS").is_some() {
        std::fs::write(expected_path, &rendered)?;
        return Ok(());
    }
    let expected = std::fs::read_to_string(expected_path).map_err(|e| {
        anyhow::anyhow!(
            "missing {} ({e}); generate it with KERNEL_VERIFY_BLESS=1",
            expected_path.display()
        )
    })?;
    if expected != rendered {
        let diff: Vec<String> = {
            let exp: BTreeMap<&str, &str> = expected
                .lines()
                .filter_map(|l| l.split_once(": "))
                .collect();
            let act: BTreeMap<&str, &str> = rendered
                .lines()
                .filter_map(|l| l.split_once(": "))
                .collect();
            let mut d = vec![];
            for (k, v) in &act {
                match exp.get(k) {
                    None => d.push(format!("+ {k}: {v}")),
                    Some(e) if e != v => {
                        d.push(format!("- {k}: {e}"));
                        d.push(format!("+ {k}: {v}"));
                    }
                    _ => {}
                }
            }
            for (k, v) in &exp {
                if !act.contains_key(k) {
                    d.push(format!("- {k}: {v}"));
                }
            }
            d
        };
        anyhow::bail!(
            "kernel-verify coverage drifted from the blessed snapshot; review and re-bless with KERNEL_VERIFY_BLESS=1 if intended:\n{}",
            diff.join("\n")
        );
    }
    Ok(())
}
