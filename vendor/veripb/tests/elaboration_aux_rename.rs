//! Elaborating a version-2 order's auxiliary variables into the version-3
//! namespace, and the two ways it can fail.
//!
//! Version 3 requires an order's `aux`, `fresh_aux_1` and `fresh_aux_2` names to
//! be `$`-prefixed — its grammar reads those lists with `is_var_allowed =
//! false, is_aux_allowed = true` and accepts nothing else — and the version-2
//! dialect cannot spell `$` at all. Since `-e` always emits version 3, a
//! version-2 order with auxiliary variables used to elaborate at exit 0 into an
//! artifact that died at parse. The fix renames those variables in the
//! name table, so every occurrence moves together.
//!
//! A rename mid-run has two ways to be wrong, and both are refusals rather than
//! silent breakage:
//!
//! 1. **Too late.** The artifact is written as checking proceeds, so a rename
//!    only reaches lines not yet written. Renaming a variable an *earlier* line
//!    already used — one from the formula, say — would rename some occurrences
//!    and not others: a partial rename that parses and means something else.
//!    `AuxVarNotFreshForElaboration`.
//!
//! 2. **Too broad.** The rename is right for the three auxiliary lists and
//!    wrong for `left`, `right` and `fresh_right`, which version 3 reads with
//!    the opposite setting and which reject a `$` name. A version-2 proof that
//!    used `q1` as an auxiliary variable of one order and then as a `left`
//!    variable of a second elaborated into a proof that died at parse —
//!    "Expected a variable or `;` but found `$q1`" — which is the exact
//!    signature the rename was added to remove, with the two namespaces
//!    swapped. `RenamedAuxVarInPlainList`.
//!
//! Both refusals are on the *elaboration* path only: the proofs are valid and
//! still verify without `-e`, which is why they are pinned here rather than
//! filed under `tests/instances/incorrect/`. A constraint may still mention the
//! renamed variable — `$q1` is a legal name in a version-3 constraint and such
//! an artifact re-checks — so it is only the variable lists that are guarded.

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

/// The corpus instance `correct/version2/pre_order_aux_vars`, minus its header
/// comment, as the known-good order to build on.
///
/// Read from the corpus rather than hand-rolled: its transitivity proof uses
/// relative constraint ids, and a `spec` block shifts them — the same
/// arithmetic that produced the reflexivity-hint defect. Copying a proof that
/// is already pinned to verify avoids inventing a second one that has to be
/// debugged.
fn corpus_order() -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/instances/correct/version2/pre_order_aux_vars.pbp");
    let body = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
    let from = body
        .find("\nf 1\n")
        .expect("the instance starts its proof with `f 1`");
    let to = body.find("output NONE").expect("the instance has a footer");
    body[from + 1..to].to_string()
}

fn formula_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/instances/correct/version2/pre_order_aux_vars.opb")
}

fn proof(extra: &str) -> String {
    format!(
        "pseudo-Boolean proof version 2.0\n{}{extra}output NONE\nconclusion NONE\nend pseudo-Boolean proof\n",
        corpus_order()
    )
}

struct Run {
    stdout: String,
    stderr: String,
    code: Option<i32>,
}

impl Run {
    fn verdicts(&self) -> Vec<&str> {
        self.stdout
            .lines()
            .filter(|l| l.starts_with("s "))
            .collect()
    }
    fn context(&self) -> String {
        format!(
            "--- stdout ---\n{}--- stderr ---\n{}",
            self.stdout, self.stderr
        )
    }
}

/// Run the checker, optionally elaborating into `out`.
fn run(proof_text: &str, out: Option<&PathBuf>) -> Run {
    let dir = tempfile::tempdir().expect("failed to create temporary directory");
    let write = |name: &str, contents: &str| -> PathBuf {
        let path = dir.path().join(name);
        let mut file = std::fs::File::create(&path).expect("failed to create temporary file");
        file.write_all(contents.as_bytes())
            .expect("failed to write test input");
        path
    };
    let formula = formula_path();
    let _ = &write;
    let derivation = write("p.pbp", proof_text);
    let mut command = Command::new(env!("CARGO_BIN_EXE_veripb"));
    if let Some(out) = out {
        command.arg("-e").arg(out);
    }
    let output = command
        .arg(&formula)
        .arg(&derivation)
        .output()
        .expect("failed to run veripb");
    Run {
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        code: output.status.code(),
    }
}

/// The ordinary case: one order with auxiliary variables elaborates, and the
/// elaborated proof re-checks to the same verdict.
#[test]
fn a_version_2_order_with_auxiliary_variables_round_trips() {
    let text = proof("");
    let before = run(&text, None);
    assert_eq!(before.verdicts(), vec!["s VERIFIED NO CONCLUSION"]);

    let dir = tempfile::tempdir().expect("temporary directory");
    let elaborated = dir.path().join("out.pbp");
    let run_e = run(&text, Some(&elaborated));
    assert_eq!(
        run_e.code,
        Some(0),
        "elaboration failed on a proof that verifies:\n{}",
        run_e.context()
    );

    let body = std::fs::read_to_string(&elaborated).expect("elaborated proof");
    assert!(
        body.contains("aux $q1"),
        "the auxiliary variable was not given the version-3 spelling:\n{body}"
    );
    assert!(
        !body.contains(" q1"),
        "an occurrence of `q1` survived the rename, which is the partial rename \
         the name-table approach exists to prevent:\n{body}"
    );

    // The elaborated proof must itself check out, with the same verdict.
    let formula = formula_path();
    let recheck = Command::new(env!("CARGO_BIN_EXE_veripb"))
        .arg(&formula)
        .arg(&elaborated)
        .output()
        .expect("failed to run veripb");
    let stdout = String::from_utf8_lossy(&recheck.stdout);
    assert!(
        stdout.contains("s VERIFIED NO CONCLUSION"),
        "the elaborated proof does not re-check:\n{stdout}{}",
        String::from_utf8_lossy(&recheck.stderr)
    );
}

/// Reusing an auxiliary name in a plain variable list is refused at elaboration,
/// in all three list positions — and the proof still verifies without `-e`.
#[test]
fn reusing_an_auxiliary_name_in_a_plain_list_is_refused_at_elaboration() {
    let second = |left: &str, right: &str, fresh_right: &str| {
        format!(
            "pre_order two\n\
             \x20   vars\n\
             \x20       left {left}\n\
             \x20       right {right}\n\
             \x20       aux\n\
             \x20   end\n\
             \x20   def\n\
             \x20       -1 {left} 1 {right} >= 0 ;\n\
             \x20   end\n\
             \x20   transitivity\n\
             \x20       vars\n\
             \x20           fresh_right {fresh_right}\n\
             \x20       end\n\
             \x20       proof\n\
             \x20           proofgoal #1\n\
             \x20               p -2 -3 + -1 +\n\
             \x20           end -1\n\
             \x20       end\n\
             \x20   end\n\
             end\n"
        )
    };
    let cases = [
        ("left", second("q1", "r1", "s1")),
        ("right", second("m1", "q1", "s1")),
        ("fresh_right", second("m1", "r1", "q1")),
    ];
    for (position, block) in cases {
        let text = proof(&block);

        let dir = tempfile::tempdir().expect("temporary directory");
        let elaborated = dir.path().join("out.pbp");
        let result = run(&text, Some(&elaborated));
        assert_eq!(
            result.code,
            Some(1),
            "reusing an auxiliary name as `{position}` must refuse to elaborate \
             rather than write an artifact that does not parse:\n{}",
            result.context()
        );
        assert!(
            result
                .stderr
                .contains("is an auxiliary variable of an earlier order"),
            "elaboration refused `{position}`, but not for the reason this test \
             is about:\n{}",
            result.context()
        );
        // Elaboration writes as it checks, so a refused run leaves a truncated
        // file behind. That is not a claim about anything -- the exit code is
        // the signal -- but a consumer must not be able to mistake it for a
        // proof, so it must not verify.
        if elaborated.is_file() {
            let leftover = Command::new(env!("CARGO_BIN_EXE_veripb"))
                .arg(formula_path())
                .arg(&elaborated)
                .output()
                .expect("failed to run veripb");
            assert_ne!(
                leftover.status.code(),
                Some(0),
                "the partial artifact left by a refused elaboration of \
                 `{position}` verifies on its own, so a consumer reading the \
                 file rather than the exit code would be misled:\n{}",
                String::from_utf8_lossy(&leftover.stdout)
            );
        }
    }
}

/// The literal-list positions: `load_order`, a logged solution, and a
/// `conclusion` solution hint are read by version 3 with the same
/// `is_aux_allowed = false` as the variable lists, and each is expressible in
/// version 2 — the first guard covered `left`/`right`/`fresh_right` and
/// believed that was the whole set. Measured before the extension: each of
/// these verified at exit 0, elaborated at exit 0, and produced an artifact
/// that died at parse.
#[test]
fn reusing_an_auxiliary_name_in_a_literal_position_is_refused_at_elaboration() {
    let cases = [
        ("load_order", "load_order simple q1\n", false),
        ("sol", "sol x1 x2 q1\n", false),
        ("conclusion hint", "conclusion SAT : x1 x2 q1", true),
    ];
    for (position, line, is_conclusion) in cases {
        let text = if is_conclusion {
            format!(
                "pseudo-Boolean proof version 2.0\n{}output NONE\n{line}\nend pseudo-Boolean proof\n",
                corpus_order()
            )
        } else {
            format!(
                "pseudo-Boolean proof version 2.0\n{}{line}output NONE\nconclusion NONE\nend pseudo-Boolean proof\n",
                corpus_order()
            )
        };
        let plain = run(&text, None);
        assert_eq!(
            plain.code,
            Some(0),
            "the `{position}` probe must verify without `-e` — it is a valid \
             proof, and the refusal below is about elaboration only:\n{}",
            plain.context()
        );
        let dir = tempfile::tempdir().expect("temporary directory");
        let elaborated = dir.path().join("out.pbp");
        let result = run(&text, Some(&elaborated));
        assert_eq!(
            result.code,
            Some(1),
            "reusing an auxiliary name in `{position}` must refuse to elaborate \
             rather than write an artifact that does not parse:\n{}",
            result.context()
        );
        assert!(
            result
                .stderr
                .contains("is an auxiliary variable of an earlier order"),
            "elaboration refused `{position}`, but not for the reason this test \
             is about:\n{}",
            result.context()
        );
    }
}

/// The `left` case still verifies without `-e`.
///
/// The refusal above is about what can be *written*, not about what is true;
/// filing these proofs as incorrect would be a false claim about the checker.
#[test]
fn the_refused_proofs_are_valid_without_elaboration() {
    let block = "pre_order two\n    vars\n        left q1\n        right r1\n        aux\n    end\n    def\n        -1 q1 1 r1 >= 0 ;\n    end\n    transitivity\n        vars\n            fresh_right s1\n        end\n        proof\n            proofgoal #1\n                p -2 -3 + -1 +\n            end -1\n        end\n    end\nend\n";
    let text = proof(block);
    let result = run(&text, None);
    assert_eq!(
        result.verdicts(),
        vec!["s VERIFIED NO CONCLUSION"],
        "the proof is valid and must still verify without `-e`:\n{}",
        result.context()
    );
    assert_eq!(result.code, Some(0));
}
