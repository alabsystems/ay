//! Every observable output must be a function of the input — not just the
//! elaborated proof.
//!
//! `tests/elaboration_deterministic.rs` pins the elaborated artifact. It is
//! not the only thing a consumer sees. This test pins the rest: the verdict
//! line, the exit code, the whole of stderr (error messages and warnings
//! included), the `--kernel-verify` summary counters and composition census,
//! `--trace` output, and the `--stats` report with its one wall-clock figure
//! masked. It runs the *incorrect* corpus as well as the correct one, because
//! a refusal that varies in its reason is as bad as a verdict that varies, and
//! the refusal paths are the least travelled in the checker.
//!
//! Three defects of exactly that shape were found and fixed alongside this
//! file, all of them an iteration over `Context::preserved_variables` (or a
//! set compared against it) — an `ahash::AHashSet` whose default `RandomState`
//! seeds itself from runtime randomness once per process:
//!
//! 1. `Context::print_preserved_set` printed the `Preserved set:` trace line in
//!    hash order. Measured before the fix: `--trace` on
//!    `correct/version3/add_preserved_var_trivial` produced *twenty distinct
//!    outputs over twenty runs*, differing only in the order of that line;
//!    seven corpus instances varied in all.
//! 2. `rules::equal_preserved` built the `epreserved` set-mismatch refusal by
//!    iterating the difference of two such sets. An `epreserved` disagreeing
//!    on six variables printed *twelve distinct messages over twelve runs*.
//! 3. `rules::output` built the `output`-file preserved-set mismatch refusal
//!    the same way: *ten distinct messages over ten runs*.
//! 4. `rules::solution_logging` walked the preserved set in hash order looking
//!    for a variable the propagated solution leaves unassigned, and refused on
//!    the first one it reached. A `solx` leaving seven preserved variables
//!    unassigned named *six distinct variables over fifteen runs*.
//!
//! None of these was a wrong verdict — the verdict, exit code, error variant
//! and elaborated bytes were identical every time, and only the order the
//! variables were named in moved. They matter for the reason the elaboration
//! defect mattered: a checker whose behaviour is not a function of its input
//! cannot be diffed, cannot be regression-tested, and hides a defect that
//! appears under one iteration order and not another as flaky rather than
//! absent.
//!
//! Cases 2, 3 and 4 are *not* reachable from the corpus — no shipped instance
//! disagrees on more than one preserved variable, or leaves more than one
//! unassigned — so this file constructs them, as
//! `refusal_reason_is_a_function_of_its_input`. Cases like these are why the
//! corpus sweep alone is not enough: the refusal paths are exactly the ones a
//! corpus of mostly-correct proofs does not reach.
//!
//! Like `elaboration_deterministic`, this runs the shipped binary rather than
//! the library: the randomness is per *process*, so two runs inside one test
//! process would share a seed and agree even with the bug present.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Runs per instance. The randomness is re-seeded per process, so two
/// processes already discriminate; a third makes a small-set coincidence
/// (where few permutations exist) correspondingly less likely. Determinism is
/// a fixed point, so extra runs can never make this test flaky — only
/// stricter.
const RUNS: usize = 3;

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// The observable modes. `elab` is deliberately absent: it is
/// `elaboration_deterministic`'s job, and duplicating it here would double
/// this file's cost for nothing.
const MODES: [&str; 4] = ["check", "kernel-verify", "trace", "stats"];

struct Instance {
    formula: PathBuf,
    derivation: PathBuf,
    output_formula: Option<PathBuf>,
    /// Mirrors `tests/integration.rs`: checked deletion is forced unless the
    /// derivation's second line opts out.
    force_checked_deletion: bool,
    lenient_header_counts: bool,
}

/// Collect the corpus the way `tests/integration.rs` does, so the runs here
/// are the runs that test actually performs.
fn corpus() -> Vec<Instance> {
    let root = repo_root().join("tests/instances");
    let mut out = Vec::new();
    for correct in ["correct", "incorrect"] {
        for version in ["version2", "version3"] {
            let dir = root.join(correct).join(version);
            let mut entries: Vec<PathBuf> = std::fs::read_dir(&dir)
                .unwrap_or_else(|e| panic!("cannot list {}: {e}", dir.display()))
                .flatten()
                .map(|e| e.path())
                .filter(|p| p.extension().is_some_and(|e| e == "pbp"))
                .collect();
            entries.sort();
            for derivation in entries {
                let formula = ["opb", "cnf", "wcnf"]
                    .iter()
                    .map(|ext| derivation.with_extension(ext))
                    .find(|c| c.exists())
                    .unwrap_or_else(|| derivation.with_extension("opb"));
                let output_formula = derivation.with_extension("outopb");
                let output_formula = output_formula.exists().then_some(output_formula);
                let second = second_line(&derivation);
                let comment = if version == "version2" { "*" } else { "%" };
                out.push(Instance {
                    force_checked_deletion: second
                        != format!("{comment} INTEGRATION-TEST: allow-unchecked-deletion"),
                    lenient_header_counts: second
                        == format!("{comment} INTEGRATION-TEST: lenient-header-counts"),
                    formula,
                    derivation,
                    output_formula,
                });
            }
        }
    }
    out
}

fn second_line(path: &Path) -> String {
    let text = std::fs::read_to_string(path).unwrap_or_default();
    text.lines().nth(1).unwrap_or_default().trim().to_owned()
}

/// Everything a caller of the binary can observe, as one comparable string.
fn observe(instance: &Instance, mode: &str) -> String {
    let mut command = Command::new(env!("CARGO_BIN_EXE_veripb"));
    if instance.force_checked_deletion {
        command.arg("-c");
    }
    if instance.lenient_header_counts {
        command.arg("--lenient-header-counts");
    }
    match mode {
        "check" => {}
        "kernel-verify" => {
            command.arg("--kernel-verify");
        }
        "trace" => {
            command.arg("--trace");
        }
        "stats" => {
            command.arg("--stats");
        }
        other => panic!("unknown mode {other}"),
    }
    command.arg(&instance.formula).arg(&instance.derivation);
    if let Some(output_formula) = &instance.output_formula {
        command.arg(output_formula);
    }
    let out = command.output().expect("failed to run veripb");
    format!(
        "exit: {:?}\n--- stdout ---\n{}--- stderr ---\n{}",
        out.status.code(),
        mask_timings(&String::from_utf8_lossy(&out.stdout)),
        String::from_utf8_lossy(&out.stderr),
    )
}

/// `--stats` reports a wall-clock time, which is legitimately not a function
/// of the input. Mask that number and hold everything around it. Nothing else
/// `--stats` prints is a timing.
fn mask_timings(text: &str) -> String {
    text.lines()
        .map(|line| {
            // `c statistic: time <what>: <elapsed> s`
            if let Some((before, rest)) = line.split_once("c statistic: time ")
                && let Some((what, _)) = rest.split_once(": ")
            {
                return format!("{before}c statistic: time {what}: <MASKED> s\n");
            }
            // `c statistic: custom timer '<name>': <elapsed> s` -- upstream's
            // `timer` feature. A timer REPORTS THE CLOCK, so its elapsed field
            // is not a function of the input and never can be; masking it keeps
            // every other line of `--stats` on those instances under this test
            // rather than dropping the instances from the corpus.
            if let Some((before, rest)) = line.split_once("c statistic: custom timer ")
                && let Some((name, _)) = rest.split_once(": ")
            {
                return format!("{before}c statistic: custom timer {name}: <MASKED> s\n");
            }
            format!("{line}\n")
        })
        .collect()
}

/// Two proofs whose *refusal* names a set of variables, which no corpus
/// instance does with more than one variable in it.
///
/// Written into a temporary directory rather than added to
/// `tests/instances/incorrect`, so the integration corpus and its counts are
/// untouched.
fn refusal_probes(dir: &Path) -> Vec<Instance> {
    let formula = "* #variable= 8 #constraint= 1\n\
                   preserved: x1 x2 x3 x4 x5 x6 x7 x8;\n\
                   1 x1 +1 x2 >= 1 ;\n";

    // `epreserved` naming a set that disagrees with the checker's own on six
    // variables: `CheckingError::PreservedEqualsSetMismatch` lists them.
    let epreserved_opb = dir.join("epreserved.opb");
    let epreserved_pbp = dir.join("epreserved.pbp");
    std::fs::write(&epreserved_opb, formula).expect("write probe formula");
    std::fs::write(
        &epreserved_pbp,
        "pseudo-Boolean proof version 3.0\n\
         f 1;\n\
         epreserved x1 x2;\n\
         output NONE;\n\
         conclusion NONE;\n\
         end pseudo-Boolean proof;\n",
    )
    .expect("write probe derivation");

    // An `output` file whose `preserved:` line disagrees with the checker's
    // set in both directions: `CheckingError::OutputPreservedVarsMismatch`
    // lists the missing variables and the additional ones.
    let output_opb = dir.join("output.opb");
    let output_pbp = dir.join("output.pbp");
    let output_out = dir.join("output.outopb");
    std::fs::write(
        &output_opb,
        "* #variable= 3 #constraint= 3\n\
         preserved: x1 x2 x3;\n\
         1 ~x1 1 ~x2 >= 1 ;\n\
         1 ~x1 1 ~x3 >= 1 ;\n\
         1 ~x2 1 ~x3 >= 1 ;\n",
    )
    .expect("write probe formula");
    std::fs::write(
        &output_pbp,
        "pseudo-Boolean proof version 3.0\n\
         f 3;\n\
         red 1 ~x4 1 x1 >= 1 : x4 0 ;\n\
         core id -1;\n\
         red 1 x4 1 ~x1 >= 1 : x4 1 ;\n\
         core id -1;\n\
         preserved_add x4 : 1 x1 >= 1 ;\n\
         pol 1 4 +;\n\
         core id -1;\n\
         pol 2 4 +;\n\
         core id -1;\n\
         preserved_rm x1 : 1 x4 >= 1 ;\n\
         del id 1;\n\
         del id 2;\n\
         del id 4 : x1 1 ;\n\
         del id 5 : x1 0 ;\n\
         output EQUIENUMERABLE FILE;\n\
         conclusion NONE;\n\
         end pseudo-Boolean proof;\n",
    )
    .expect("write probe derivation");
    std::fs::write(
        &output_out,
        "* #variable= 8 #constraint= 3\n\
         preserved: x5 x6 x7 x8;\n\
         1 ~x4 1 ~x2 >= 1 ;\n\
         1 ~x4 1 ~x3 >= 1 ;\n\
         1 ~x2 1 ~x3 >= 1 ;\n",
    )
    .expect("write probe output formula");

    // A `solx` that leaves seven of the eight preserved variables unassigned:
    // `CheckingError::SolutionExcludingPreservedVarUnassigned` names one of
    // them, and which one it names is the order the set was walked in.
    let unassigned_opb = dir.join("unassigned.opb");
    let unassigned_pbp = dir.join("unassigned.pbp");
    std::fs::write(&unassigned_opb, formula).expect("write probe formula");
    std::fs::write(
        &unassigned_pbp,
        "pseudo-Boolean proof version 3.0\n\
         f 1;\n\
         solx x1;\n\
         output NONE;\n\
         conclusion NONE;\n\
         end pseudo-Boolean proof;\n",
    )
    .expect("write probe derivation");

    vec![
        Instance {
            formula: epreserved_opb,
            derivation: epreserved_pbp,
            output_formula: None,
            force_checked_deletion: true,
            lenient_header_counts: false,
        },
        Instance {
            formula: output_opb,
            derivation: output_pbp,
            output_formula: Some(output_out),
            force_checked_deletion: true,
            lenient_header_counts: false,
        },
        Instance {
            formula: unassigned_opb,
            derivation: unassigned_pbp,
            output_formula: None,
            force_checked_deletion: true,
            lenient_header_counts: false,
        },
    ]
}

/// Compare `RUNS` fresh processes per (instance, mode) and report every field
/// that moved.
fn sweep(instances: &[Instance], modes: &[&str]) -> (usize, Vec<String>) {
    let threads = std::thread::available_parallelism()
        .map(std::num::NonZeroUsize::get)
        .unwrap_or(4)
        .min(8);
    let chunk = instances.len().div_ceil(threads).max(1);
    let results: Vec<(usize, Vec<String>)> = std::thread::scope(|scope| {
        let handles: Vec<_> = instances
            .chunks(chunk)
            .map(|slice| {
                scope.spawn(move || {
                    let mut compared = 0usize;
                    let mut differing = Vec::new();
                    for instance in slice {
                        for mode in modes {
                            let first = observe(instance, mode);
                            compared += 1;
                            for run in 1..RUNS {
                                let again = observe(instance, mode);
                                if again != first {
                                    differing.push(format!(
                                        "{} (--{mode}): run 1 and run {} differ\n{}",
                                        instance.derivation.display(),
                                        run + 1,
                                        first_difference(&first, &again),
                                    ));
                                    break;
                                }
                            }
                        }
                    }
                    (compared, differing)
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().expect("sweep thread panicked"))
            .collect()
    });
    let compared = results.iter().map(|(c, _)| c).sum();
    let differing = results.into_iter().flat_map(|(_, d)| d).collect();
    (compared, differing)
}

/// The first line that differs, so a failure names the unstable output rather
/// than dumping two whole traces.
fn first_difference(a: &str, b: &str) -> String {
    for (n, (x, y)) in a.lines().zip(b.lines()).enumerate() {
        if x != y {
            return format!("      line {}:\n        {x:?}\n        {y:?}", n + 1);
        }
    }
    format!(
        "      (no differing line; {} vs {} lines)",
        a.lines().count(),
        b.lines().count()
    )
}

fn report(what: &str, compared: usize, differing: Vec<String>) {
    assert!(
        differing.is_empty(),
        "{what} is not a function of its input in {} case(s):\n  {}\n\n\
         Look for an iteration over a container whose order is not a function \
         of the input — a randomly seeded `ahash` state (`AHashMap::new`, \
         `AHashSet::new`, `HashMap::default`), or a set keyed by `ByAddress` \
         or by a raw pointer, whose order is the allocator's and varies under \
         ASLR whatever the seed. Fix it with a fixed seed if the keys are \
         values, or with a stable sort key if they are addresses. See this \
         file's header and `tests/elaboration_deterministic.rs`.",
        differing.len(),
        differing.join("\n  "),
    );
    assert!(compared > 0, "{what}: nothing was compared");
}

/// The verdict, the exit code, stderr in full, the `--kernel-verify` counters
/// and census, `--trace`, and `--stats` are the same on every run, for every
/// corpus instance — the incorrect ones included.
#[test]
fn observable_output_is_a_function_of_its_input() {
    let instances = corpus();
    assert!(
        instances.len() > 400,
        "found only {} corpus instances; the corpus walk has gone stale",
        instances.len()
    );
    let (compared, differing) = sweep(&instances, &MODES);
    report("observable output", compared, differing);
    assert!(
        compared > 400 * MODES.len(),
        "only {compared} (instance, mode) pair(s) were compared; this test is \
         no longer measuring the corpus"
    );
}

/// A refusal that names a *set* of variables names them in the same order on
/// every run.
///
/// These two refusals are unreachable from the shipped corpus, so they are
/// constructed here. Both were measured to print a different message on every
/// run before the fix.
#[test]
fn refusal_reason_is_a_function_of_its_input() {
    let dir = tempfile::tempdir().expect("failed to create temporary directory");
    let probes = refusal_probes(dir.path());

    // Each probe must actually reach the refusal it is built for; a probe that
    // has silently started failing earlier (a parse error, say) would pin
    // nothing while still passing.
    for (probe, expected) in probes.iter().zip([
        "does not match the current set of preserved variables",
        "do not match the current set of preserved variables",
        "is unassigned by the solution",
    ]) {
        let observed = observe(probe, "check");
        assert!(
            observed.contains(expected),
            "probe {} no longer reaches its refusal (expected {expected:?}):\n{observed}",
            probe.derivation.display(),
        );
    }

    let (compared, differing) = sweep(&probes, &["check"]);
    report("refusal reason", compared, differing);
}
