use std::{
    ffi::OsStr,
    io::BufRead,
    path::{Path, PathBuf},
};

use anyhow::Context;

// NOTE: integration tests that should be ignored (typically because they are known to fail) can be
// marked with the following on the second line of the derivation file:
// <cmt> INTEGRATION-TEST: ignore(<what>)
// where <cmt> is * for version 2 or % for version 3, and <what> is one of check, elaborate, or both.
//
// The second line also accepts:
// <cmt> INTEGRATION-TEST: allow-unchecked-deletion
// <cmt> INTEGRATION-TEST: lenient-header-counts
// The latter runs the DIMACS CNF header check in warn-only mode, which is what
// `--lenient-header-counts` does on the command line. It is needed to pin defects that only a
// header-count-mismatching file can express; checks that must hold regardless of that flag (such
// as the variable-index range check) belong in instances that carry it.

fn main() {
    let args = libtest_mimic::Arguments::from_args();
    let mut tests = vec![];

    for correct in [true, false] {
        for version in ["version2", "version3"] {
            let ignore_both_string = if version == "version2" {
                "* INTEGRATION-TEST: ignore(both)"
            } else {
                "% INTEGRATION-TEST: ignore(both)"
            };
            for derivation in glob::glob(&format!(
                "./tests/instances/{}/{version}/*.pbp",
                if correct { "correct" } else { "incorrect" }
            ))
            .unwrap()
            .flatten()
            {
                let id = derivation.file_stem().unwrap().to_str().unwrap();
                let mut second_line = String::new();
                let mut reader = std::io::BufReader::new(
                    std::fs::File::open(&derivation).expect("failed to read derivation"),
                );
                reader
                    .read_line(&mut second_line)
                    .expect("failed to read first line of derivation file");
                second_line.clear();
                reader
                    .read_line(&mut second_line)
                    .expect("failed to read second line of derivation file");
                let second_line = second_line;
                let comment = if version == "version2" { "*" } else { "%" };
                let force_checked_deletion = second_line.trim()
                    != format!("{comment} INTEGRATION-TEST: allow-unchecked-deletion");
                let lenient_header_counts = second_line.trim()
                    == format!("{comment} INTEGRATION-TEST: lenient-header-counts");
                for elaborate in [true, false] {
                    let deriv = derivation.clone();
                    let trial = libtest_mimic::Trial::test(
                        format!(
                            "{version}::{id} ({} - expected {})",
                            if elaborate { "elaborate" } else { "check" },
                            if correct { "correct" } else { "incorrect" }
                        ),
                        move || {
                            run_test(
                                deriv,
                                correct,
                                elaborate,
                                force_checked_deletion,
                                lenient_header_counts,
                            )
                            .map_err(|e| format!("{e:#}").into())
                        },
                    );
                    // If the test is known-bad, ignore it
                    let ignored = second_line.trim() == ignore_both_string
                        || second_line.trim()
                            == format!(
                                "{} INTEGRATION-TEST: ignore({})",
                                if version == "version2" { "*" } else { "%" },
                                if elaborate { "elaborate" } else { "check" }
                            );
                    tests.push(trial.with_ignored_flag(ignored));
                }
            }
        }
    }

    libtest_mimic::run(&args, tests).exit();
}

fn run_test<P>(
    derivation: P,
    correct: bool,
    elaborate: bool,
    force_checked_deletion: bool,
    lenient_header_counts: bool,
) -> anyhow::Result<()>
where
    P: AsRef<Path>,
{
    // Temporary kernel file if elaborating
    // This is automatically deleted when `kernel_proof` is dropped
    let kernel_proof = if elaborate {
        Some(tempfile::NamedTempFile::new().expect("failed to create temporary kernel proof file"))
    } else {
        None
    };

    // The formula is the sibling file with a supported formula extension; the format is then
    // inferred from that extension by the checker itself.
    let formula = ["opb", "cnf", "wcnf"]
        .iter()
        .map(|extension| derivation.as_ref().with_extension(extension))
        .find(|candidate| candidate.exists())
        .unwrap_or_else(|| derivation.as_ref().with_extension("opb"));
    let output_formula = derivation.as_ref().with_extension("outopb");
    let output_formula = if output_formula.exists() {
        Some(output_formula)
    } else {
        None
    };
    let res = run_veripb(
        formula.clone(),
        derivation.as_ref().to_path_buf(),
        output_formula.clone(),
        kernel_proof
            .as_ref()
            .map(|kernel| kernel.path().to_path_buf()),
        force_checked_deletion,
        lenient_header_counts,
    );

    // Does this instance declare that it is refused by the PARSER? Two of the
    // twenty-seven defects are genuine reader defects; every other instance
    // must be refused at checking level, or it has stopped being evidence for
    // what it claims to reproduce.
    let declares_parse_refusal = [
        Some(formula.as_path()),
        Some(derivation.as_ref()),
        output_formula.as_deref(),
    ]
    .into_iter()
    .flatten()
    .any(|p| {
        std::fs::read_to_string(p)
            .map(|t| t.contains("% refused-at: parse"))
            .unwrap_or(false)
    });

    verify_veripb_result(res, correct, declares_parse_refusal).with_context(|| {
        format!(
            "{} proof yielded unexpected result",
            if elaborate { "elaborating" } else { "checking" }
        )
    })?;

    if let Some(kernel_proof) = kernel_proof {
        assert!(elaborate);
        if correct {
            test_elaborated_proof(
                formula,
                kernel_proof.path().to_path_buf(),
                output_formula,
                force_checked_deletion,
                lenient_header_counts,
            )?;
        }
    } else {
        assert!(!elaborate);
    }

    Ok(())
}

fn test_elaborated_proof(
    formula: PathBuf,
    kernel_proof: PathBuf,
    output_formula: Option<PathBuf>,
    force_checked_deletion: bool,
    lenient_header_counts: bool,
) -> anyhow::Result<()> {
    // Run VeriPB on the kernel proof
    let res = run_veripb(
        formula.clone(),
        kernel_proof.clone(),
        output_formula.clone(),
        None,
        force_checked_deletion,
        lenient_header_counts,
    );

    verify_veripb_result(res, true, false)
        .context("checking kernel proof yielded unexpected result")?;

    // Run kernel proof through formally verified checker. CakePB reads OPB and DIMACS CNF only,
    // so a WCNF instance is checked by this crate alone.
    let mut cake_pb = match formula.extension().and_then(OsStr::to_str) {
        Some("opb") => std::process::Command::new("cake_pb"),
        Some("cnf") => std::process::Command::new("cake_pb_cnf"),
        _ => return Ok(()),
    };
    if let Some(output_formula) = output_formula {
        cake_pb.args([
            formula.to_str().unwrap(),
            kernel_proof.to_str().unwrap(),
            output_formula.to_str().unwrap(),
        ]);
    } else {
        cake_pb.args([formula.to_str().unwrap(), kernel_proof.to_str().unwrap()]);
    }
    match cake_pb.output() {
        Ok(o) => {
            anyhow::ensure!(
                o.stderr.is_empty(),
                format!(
                    "checking kernel proof with CakePB yielded unexpected result:\n\t{}",
                    String::from_utf8(o.stderr).unwrap(),
                )
            );
        }
        // Handle errors with running CakePB, like CakePB not being installed.
        Err(err) => match err.kind() {
            std::io::ErrorKind::NotFound => {}
            _ => return Err(err).context("failed to run CakePB"),
        },
    }

    Ok(())
}

fn verify_veripb_result(
    result: anyhow::Result<()>,
    expected_correct: bool,
    declares_parse_refusal: bool,
) -> anyhow::Result<()> {
    if expected_correct {
        result?;
        Ok(())
    } else {
        let Err(err) = result else {
            anyhow::bail!("expected proof to be incorrect, but VeriPB returned no error");
        };
        // The "good" errors for an incorrect instance -- but NOT all of them
        // are interchangeable.
        //
        // An audit found that replacing a reproducer's body with one
        // unparsable line left the whole workspace green: a `ParserError`
        // scored identically to the checking refusal the instance was written
        // to pin, so an instance could stop reproducing its defect entirely
        // and nothing noticed. These files ARE the evidence for the
        // wrong-verdict claims, so "it was refused" is not enough -- it has to
        // be refused for the reason it exists to demonstrate.
        //
        // So a checking-level refusal is accepted by default, and a
        // PARSE-level refusal only when the instance declares it. Two defects
        // (the OPB one-item-per-line reader and the CNF header reader) are
        // genuinely parser defects and say so with a `% refused-at: parse`
        // line; for every other instance a parse error now fails the test.
        // `ForwardsCheckerError::Parse` WRAPS a `ParserError`, so testing the
        // outermost type first would let a parse failure in through this arm
        // and never reach the parse check below -- which is exactly what the
        // audit's mutation exploited.
        let err = match err.downcast::<veripb_checker::error::ForwardsCheckerError>() {
            Ok(veripb_checker::error::ForwardsCheckerError::Parse(inner)) => {
                if declares_parse_refusal {
                    return Ok(());
                }
                anyhow::bail!(
                    "this instance was refused by the PARSER ({inner}), but it does \
                     not declare `% refused-at: parse`. An incorrect instance is \
                     evidence for a specific defect, and a proof that merely \
                     stopped parsing is not that evidence -- if the file was \
                     edited, restore what it reproduced; if it really is a reader \
                     defect, declare it."
                );
            }
            Ok(_) => return Ok(()),
            Err(err) => err,
        };
        let Err(err) = err.downcast::<veripb_checker::error::CheckingError>() else {
            return Ok(());
        };
        let Err(err) = err.downcast::<veripb_propagator::error::PropagatorError>() else {
            return Ok(());
        };
        let Err(err) = err.downcast::<veripb_parser::error::ParserError>() else {
            if declares_parse_refusal {
                return Ok(());
            }
            anyhow::bail!(
                "this instance was refused by the PARSER, but it does not declare \
                 `% refused-at: parse`. An incorrect instance is evidence for a \
                 specific defect, and a proof that merely stopped parsing is not \
                 that evidence -- if the file was edited, restore what it \
                 reproduced; if it really is a reader defect, declare it."
            );
        };
        Err(err)
    }
}

fn run_veripb(
    formula: PathBuf,
    derivation: PathBuf,
    output_formula: Option<PathBuf>,
    kernel_proof: Option<PathBuf>,
    force_checked_deletion: bool,
    lenient_header_counts: bool,
) -> anyhow::Result<()> {
    let args = veripb::args::Args {
        formula,
        derivation,
        output_formula,
        elaborate: kernel_proof.map(Some),
        print_verification_result: false,
        force_checked_deletion,
        lenient_header_counts,
        ..Default::default()
    };
    // The outcome (verified / verified under weakened guarantees) only affects
    // the exit code of the binary; these tests care about accept vs reject.
    veripb::run_checker(args).map(|_outcome| ())
}
