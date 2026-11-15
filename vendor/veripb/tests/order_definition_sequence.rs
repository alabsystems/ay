//! An order definition is a *sequence*, and the checker enforces it in both
//! proof dialects.
//!
//! `def_order`/`pre_order` admits `vars`, then an optional `spec`, then `def`,
//! then an optional `transitivity`, then an optional `reflexivity`, then
//! `end` — each block once, only in that position. The order is not
//! presentation: every side condition of an order is checked against the
//! definition that `def` supplies, and the blocks that check them read that
//! definition *as it stands when they run*.
//!
//! `OrderProofRule` builds the transitivity obligations by iterating
//! `constructed_order.definition` at the moment `proof` runs, one proofgoal
//! per definition constraint. Written before `def`, that iteration is over an
//! empty list — so `proof` immediately followed by `end` discharged
//! transitivity for a relation that did not exist yet, and the order's closing
//! `end` then skipped the real check because `transitivity_proven` was already
//! set. A `def` supplying a 3-cycle afterwards was accepted as a preorder, and
//! one `dom` chased the cycle to the empty contradiction: an
//! exactly-one-of-three formula satisfied by `x1 = 1` verified as
//! `s VERIFIED UNSATISFIABLE`, at exit 0, under default flags.
//!
//! Only the version-3 grammar enforced the sequence — `Parser::def_order_rule`
//! reads the blocks in that order and errors on anything else — and the
//! version-2 parser dispatches every line through one flat match. That is the
//! same shape as wrong verdict 23 one level down: 23 pinned *which* rules may
//! appear inside an order definition, this pins *when*. The sequence now lives
//! in `veripb_checker::order_context::OrderPhase`, in the checker, where both
//! front ends are held to it.
//!
//! Two of the cases below were **accepted** before the ladder existed —
//! `transitivity` twice, and `spec` after `transitivity` — and neither was
//! reachable through the version-3 parser. They are the reason this is a
//! sequence check and not a single guard on `transitivity`.

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

/// Exactly-one-of-three. Satisfied by `x1 = 1, x2 = 0, x3 = 0` and its two
/// rotations, so any refutation of it is a wrong verdict; small enough that all
/// eight assignments can be checked by hand.
const FORMULA: &str = "\
* #variable= 3 #constraint= 4
1 x1 1 x2 1 x3 >= 1 ;
1 ~x1 1 ~x2 >= 1 ;
1 ~x2 1 ~x3 >= 1 ;
1 ~x3 1 ~x1 >= 1 ;
";

const VARS: &str = "\
    vars
        left u1
        right v1
        aux
    end
";

const DEF: &str = "\
    def
        -1 u1 1 v1 >= 0 ;
    end
";

/// A complete, valid transitivity block for the one-variable order above.
const TRANSITIVITY: &str = "\
    transitivity
        vars
            fresh_right w1
        end
        proof
            proofgoal #1
                p -2 -3 + -1 +
            end -1
        end
    end
";

fn proof(body: &str) -> String {
    format!(
        "pseudo-Boolean proof version 2.0\nf 4\npre_order simple\n{body}end\n\
         output NONE\nconclusion NONE\nend pseudo-Boolean proof\n"
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

fn run(proof: &str) -> Run {
    let dir = tempfile::tempdir().expect("failed to create temporary directory");
    let write = |name: &str, contents: &str| -> PathBuf {
        let path = dir.path().join(name);
        let mut file = std::fs::File::create(&path).expect("failed to create temporary file");
        file.write_all(contents.as_bytes())
            .expect("failed to write test input");
        path
    };
    let formula = write("f.opb", FORMULA);
    let derivation = write("p.pbp", proof);
    let output = Command::new(env!("CARGO_BIN_EXE_veripb"))
        .arg("--opb")
        .arg(&formula)
        .arg(&derivation)
        .output()
        .expect("failed to run veripb binary");
    Run {
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        code: output.status.code(),
    }
}

/// Every way of writing the blocks out of sequence, and what makes each one
/// unsafe rather than merely unusual.
const OUT_OF_SEQUENCE: &[(&str, &str)] = &[
    (
        "transitivity before def",
        "the transitivity obligations are the definition constraints as they \
         stand when `proof` runs, so this proves transitivity of the empty \
         relation and sets the flag the order's `end` trusts",
    ),
    ("reflexivity before def", "the same, for reflexivity"),
    (
        "vars re-opened after def",
        "`left` and `right` would be re-paired with names the definition \
         constraints do not mention, and every consumer zips the two lists \
         with `izip!`",
    ),
    (
        "def twice",
        "the second `def` grows the definition after the side conditions have \
         been checked against the first",
    ),
    (
        "transitivity twice",
        "the second block proves its obligations and overwrites the flag the \
         first set, so the last block silently wins",
    ),
    (
        "spec after transitivity",
        "the specification is a premise of the transitivity and reflexivity \
         proofs; arriving afterwards, it was never a premise of the proofs \
         that are supposed to hold under it",
    ),
    (
        "no def at all",
        "the definition is empty, so every side condition holds vacuously and \
         the order relates nothing -- which `load_order` would then accept",
    ),
];

fn body_for(case: &str) -> String {
    match case {
        "transitivity before def" => format!("{VARS}{TRANSITIVITY}{DEF}"),
        "reflexivity before def" => {
            format!("{VARS}    reflexivity\n        proof\n        end\n    end\n{DEF}")
        }
        "vars re-opened after def" => format!(
            "{VARS}{DEF}{TRANSITIVITY}    vars\n        left u2\n        right v2\n        aux\n    end\n"
        ),
        "def twice" => format!("{VARS}{DEF}{DEF}{TRANSITIVITY}"),
        "transitivity twice" => format!("{VARS}{DEF}{TRANSITIVITY}{TRANSITIVITY}"),
        "spec after transitivity" => {
            format!("{VARS}{DEF}{TRANSITIVITY}    spec\n    end\n")
        }
        "no def at all" => format!("{VARS}{TRANSITIVITY}"),
        other => panic!("no body for case `{other}`"),
    }
}

/// No out-of-sequence block is accepted, in either dialect.
#[test]
fn an_order_definition_out_of_sequence_is_refused() {
    for (case, why) in OUT_OF_SEQUENCE {
        let result = run(&proof(&body_for(case)));
        assert!(
            result.verdicts().is_empty(),
            "`{case}` produced a verdict, but {why}:\n{}",
            result.context()
        );
        assert!(
            !result.stderr.contains("INTERNAL ERROR in VeriPB"),
            "`{case}` crashed instead of being refused:\n{}",
            result.context()
        );
        assert_eq!(
            result.code,
            Some(1),
            "`{case}` must exit with the ordinary checking-error status:\n{}",
            result.context()
        );
    }
}

/// The refusal is about *sequence*, and says so.
///
/// Without this, the test above would be satisfied by any refusal at all —
/// including the incidental ones the checker already produced for some of
/// these shapes before the ladder existed (an out-of-bounds constraint id, an
/// unprovable reflexivity), which is precisely why two of the seven were
/// accepted and nobody noticed.
#[test]
fn the_refusal_names_the_sequence() {
    for (case, _) in OUT_OF_SEQUENCE {
        let result = run(&proof(&body_for(case)));
        assert!(
            result.stderr.contains("out of sequence"),
            "`{case}` was refused, but not for being out of sequence -- so this \
             probe is passing for an unrelated reason:\n{}",
            result.context()
        );
    }
}

/// The sequence the format defines is accepted, with and without each optional
/// block.
///
/// A ladder that refused everything would satisfy both tests above.
#[test]
fn the_defined_sequence_is_accepted() {
    let reflexivity = "    reflexivity\n        proof\n            proofgoal #1\n                p -1\n            end -1\n        end\n    end\n";
    // Each case carries an explicit `transitivity` block: this order's
    // relation is not one the checker autoproves transitive, and a positive
    // control has to be a proof that really verifies rather than one that
    // happens to be accepted.
    let cases: &[(&str, String)] = &[
        (
            "vars, def, transitivity",
            format!("{VARS}{DEF}{TRANSITIVITY}"),
        ),
        (
            "vars, def, transitivity, reflexivity",
            format!("{VARS}{DEF}{TRANSITIVITY}{reflexivity}"),
        ),
        (
            "vars, spec, def, transitivity",
            format!("{VARS}    spec\n    end\n{DEF}{TRANSITIVITY}"),
        ),
    ];
    for (case, body) in cases {
        let result = run(&proof(body));
        assert_eq!(
            result.verdicts(),
            vec!["s VERIFIED NO CONCLUSION"],
            "the sequence `{case}` is the one the format defines and must be \
             accepted:\n{}",
            result.context()
        );
        assert_eq!(result.code, Some(0));
    }
}
