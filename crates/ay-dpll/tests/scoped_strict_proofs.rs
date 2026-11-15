// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict UNSAT certification inside push/pop sessions and over deductive-checksgen's
//! reachability encoding (VC-context design step 5; superproject
//! DECISION_QUEUE D16).
//!
//! THREE CLAIMS, EACH WITH ITS NEGATIVE CONTROL.
//!
//! 1. **A session row certifies exactly as the same row solved fresh.** The
//!    captured context-trie session (`session_split_conjunct/`) lost four of
//!    five UNSAT rows to "native bounded BV/LIA proof replay failed: step tN
//!    assumes term t1 outside the supplied problem obligation". The design
//!    note read that as the replay scoping its problem to the innermost push.
//!    It was not a scope defect: every one of those rows failed identically as
//!    a FRESH one-shot query, because each ends in a violation that
//!    constant-folds to `false` beside `bv2nat` bridge facts, and the bounded
//!    BV/LIA bundle assumed the canonical `false` root, which the strict
//!    premise scope admits only where the author wrote `false` literally. The
//!    lane now declines such a query and the ordinary lanes certify the folded
//!    root from its authored surface. Control: a satisfiable root beside the
//!    same bridge is still `sat`.
//!
//! 2. **A popped assertion never reaches a later proof.** Its absence from the
//!    later proof — whose cheapest refutation it would otherwise be — is
//!    measured; and the same bound refuted beside its contradiction in a popped
//!    scope is `sat` alone afterwards.
//!
//! 3. **The reachability encoding certifies.** deductive-checksgen spells a join's
//!    condition as a fresh `R_J == Or(..)` definition; preprocessing then
//!    substituted every definition into the next and constant-folded the
//!    result, leaving a leaf no bridge derives from any one authored conjunct,
//!    and the strict checker refused the whole refutation ("step t0 uses
//!    unverified trust rule"). The unrewritten authored replay re-decides the
//!    exact authored roots without in-place substitution, and its proof —
//!    a case split through the asserted definition, in checked rules — is
//!    installed only through the strict gate. Control: each fixture's SAT
//!    mutant (one range fact dropped, z3 5.1.0 `sat`) is never refuted. The
//!    content-free `Unreachable` rows and the two-path join of `a5` certify
//!    through the text lane, print checked proofs in one SMT-LIB session, and
//!    certify through one native-API session (`a5` through the ordinary
//!    substituted proof, once the checked OR reorder bridge reaches the scalar
//!    replay lane; see its test).
//!
//! A fourth, smaller fix rides along: when the checked-SAT bridge transports
//! a literal across a BOOLEAN definition `b ≡ φ` it now emits `equiv_pos1`/`2`
//! instead of an `eq_congruent_pred` lemma over a non-application, which the
//! strict checker (rightly) refused.

use std::path::PathBuf;

#[path = "scoped_strict_proofs/verdict_independence.rs"]
mod verdict_independence;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// `UnknownReason` spellings that mean ay DECIDED and then WITHHELD.
const DECIDED_THEN_WITHHELD: &[&str] = &["SelfCheckRejected", "ProofTrusted", "InternalError"];

fn fixture(dir: &str, name: &str) -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(dir)
        .join(name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

/// Every `check-sat` verdict of `script`, the last unknown reason, and every
/// output of the run.
fn verdicts(script: &str) -> (Vec<String>, Option<String>, Vec<String>) {
    let commands = parse(script).unwrap_or_else(|e| panic!("parse: {e}"));
    let mut executor = Executor::new();
    let outputs = executor
        .execute_all(&commands)
        .unwrap_or_else(|e| panic!("execute: {e}"));
    let verdicts = outputs
        .iter()
        .map(|line| line.trim().to_string())
        .filter(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .collect();
    let reason = executor.unknown_reason().map(|r| format!("{r:?}"));
    (verdicts, reason, outputs)
}

fn assert_certified_unsat(label: &str, script: &str) {
    let (verdicts, reason, _) = verdicts(script);
    let withheld = verdicts.iter().any(|v| v == "unknown")
        && reason
            .as_deref()
            .is_some_and(|r| DECIDED_THEN_WITHHELD.iter().any(|w| r.contains(w)));
    assert!(!withheld, "{label}: DECIDED and then WITHHELD ({reason:?})");
    assert_eq!(verdicts, vec!["unsat"], "{label}: ({reason:?})");
}

fn assert_never_refuted(label: &str, script: &str) {
    let (verdicts, reason, _) = verdicts(script);
    assert!(
        !verdicts.iter().any(|v| v == "unsat"),
        "{label}: a SATISFIABLE query was refuted ({reason:?})"
    );
    assert_eq!(verdicts, vec!["sat"], "{label}: ({reason:?})");
}

/// A bridge fact the bounded BV/LIA lane takes, beside `root`.
fn bv_bridge_query(root: &str) -> String {
    format!(
        "(set-option :produce-proofs true)
(set-logic ALL)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (= c (bv2nat (bvand ((_ int2bv 64) a) ((_ int2bv 64) b)))))
(assert {root})
(check-sat)
"
    )
}

/// CLAIM 1, the class. Every route by which an authored root elaborates to
/// the canonical `false` certifies beside a `bv2nat` bridge.
#[test]
#[timeout(120_000)]
fn a_root_folding_to_false_beside_a_bv_bridge_certifies() {
    for root in [
        "(< (- 8 1) 0)",
        "(= 0 1)",
        "(distinct 3 3)",
        "(and (< 1 2) (> 1 2))",
        "(= (bvadd #x01 #x01) #x03)",
        "(bvult #x05 #x02)",
    ] {
        assert_certified_unsat(root, &bv_bridge_query(root));
    }
    // A LITERAL `false` is an authorized premise and keeps its lane.
    assert_certified_unsat("false", &bv_bridge_query("false"));
}

/// CLAIM 1, control: the decline is not a verdict. A root folding to `true`
/// (and a satisfiable one) beside the same bridge stays `sat`.
#[test]
#[timeout(120_000)]
fn a_satisfiable_root_beside_a_bv_bridge_is_never_refuted() {
    for root in ["(< 1 2)", "(>= c 0)"] {
        assert_never_refuted(root, &bv_bridge_query(root));
    }
}

/// CLAIM 1, the captured session. Each row certifies in the session and as a
/// fresh one-shot query rebuilt from the session's stack at that check.
#[test]
#[timeout(600_000)]
fn a_session_row_certifies_like_the_same_row_solved_fresh() {
    let script = fixture("session_split_conjunct", "ever_init_n10_rows_16_20.smt2");
    let (session, reason, _) = verdicts(&script);
    assert_eq!(
        session,
        vec!["unsat"; 5],
        "every session row is refuted and certified ({reason:?})"
    );

    // Rebuild each row fresh: the header, then the assertions live at that
    // check, then one `check-sat`.
    let mut header = Vec::new();
    let mut stack: Vec<Vec<&str>> = vec![Vec::new()];
    let mut rows = Vec::new();
    for line in script.lines() {
        let line = line.trim();
        if line.starts_with("(push") {
            stack.push(Vec::new());
        } else if line.starts_with("(pop") {
            stack.pop();
        } else if line.starts_with("(assert") {
            if let Some(frame) = stack.last_mut() {
                frame.push(line);
            }
        } else if line.starts_with("(check-sat") {
            let mut row = header.join("\n");
            for frame in &stack {
                for assertion in frame {
                    row.push('\n');
                    row.push_str(assertion);
                }
            }
            row.push_str("\n(check-sat)\n");
            rows.push(row);
        } else if line.starts_with('(') {
            header.push(line);
        }
    }
    assert_eq!(rows.len(), 5);
    for (index, row) in rows.iter().enumerate() {
        assert_certified_unsat(&format!("fresh row {index}"), row);
    }
}

/// CLAIM 2. A contradiction in a popped scope never reaches a later proof.
#[test]
#[timeout(120_000)]
fn a_popped_assertion_is_never_a_premise_of_a_later_proof() {
    let script = "(set-option :produce-proofs true)
(set-logic QF_LIA)
(declare-const popped_premise Bool)
(declare-const x Int)
(push 1)
(assert popped_premise)
(assert (not popped_premise))
(check-sat)
(pop 1)
(push 1)
(assert (> x 5))
(assert (< x 3))
(check-sat)
(get-proof)
(pop 1)
";
    let (verdicts, _, outputs) = verdicts(script);
    assert_eq!(verdicts, vec!["unsat", "unsat"], "{outputs:?}");
    let proof = outputs
        .iter()
        .find(|line| line.contains("assume"))
        .unwrap_or_else(|| panic!("the second refutation prints a proof: {outputs:?}"));
    assert!(
        !proof.contains("popped_premise"),
        "a popped assertion reached a later proof:\n{proof}"
    );
}

/// CLAIM 2, the learned-state half: the bound refuted beside its
/// contradiction inside a popped scope is satisfiable alone afterwards.
#[test]
#[timeout(120_000)]
fn a_popped_refutation_leaves_no_learned_contradiction_behind() {
    let script = "(set-option :produce-proofs true)
(set-logic QF_LIA)
(declare-const x Int)
(push 1)
(assert (> x 5))
(assert (< x 3))
(check-sat)
(pop 1)
(push 1)
(assert (> x 5))
(check-sat)
(pop 1)
";
    let (verdicts, reason, _) = verdicts(script);
    assert_eq!(verdicts, vec!["unsat", "sat"], "({reason:?})");
}

/// CLAIM 3. The reachability-encoded rows certify; their SAT mutants never
/// are refuted.
#[test]
#[timeout(600_000)]
fn the_reach_encoding_rows_certify_and_their_mutants_stay_sat() {
    for name in [
        "coroutine_resume_saturated_unreachable",
        "path_budget_async_sentinel",
    ] {
        let dir = "deductive_checksgen_reach_encoding";
        assert_certified_unsat(name, &fixture(dir, &format!("{name}.smt2")));
        assert_never_refuted(name, &fixture(dir, &format!("{name}_sat_mutant.smt2")));
    }
}

/// The reach-encoding session rows, in order, with the verdict each must get.
const REACH_SESSION_ROWS: [(&str, &str); 8] = [
    ("coroutine_resume_saturated_unreachable", "unsat"),
    ("coroutine_resume_saturated_unreachable_sat_mutant", "sat"),
    ("path_budget_async_sentinel", "unsat"),
    ("path_budget_async_sentinel_sat_mutant", "sat"),
    ("path_budget_async_sentinel", "unsat"),
    ("a5_two_next_if_ok_sym_reach", "unsat"),
    ("a5_two_next_if_ok_sym_reach_sat_mutant", "sat"),
    ("a5_two_next_if_ok_sym_reach", "unsat"),
];

/// Every declaration of the session rows, once each, in first-seen order —
/// how the in-process lane opens a session (`ExecutionSession::new` takes the
/// declarations as its header). The fixtures agree on every shared symbol.
fn reach_session_declarations() -> String {
    let mut declarations: Vec<String> = Vec::new();
    for (name, _) in REACH_SESSION_ROWS {
        let text = fixture(
            "deductive_checksgen_reach_encoding",
            &format!("{name}.smt2"),
        );
        for line in text.lines().filter(|line| line.starts_with("(declare")) {
            if !declarations.iter().any(|seen| seen == line) {
                declarations.push(line.to_string());
            }
        }
    }
    declarations.join("\n")
}

/// A fixture's assertions alone.
fn row_assertions(name: &str) -> String {
    fixture(
        "deductive_checksgen_reach_encoding",
        &format!("{name}.smt2"),
    )
    .lines()
    .filter(|line| line.starts_with("(assert"))
    .collect::<Vec<_>>()
    .join("\n")
}

/// CLAIM 3 inside one SMT-LIB session shaped like the in-process lane's —
/// declarations once, each row's assertions in its own scope, the same row
/// asked twice — with every refutation's `(get-proof)` printed as a document
/// with no `hole` or `trust` step.
#[test]
#[timeout(600_000)]
fn the_reach_encoding_rows_print_their_proofs_in_one_session() {
    let mut script = String::from("(set-option :produce-proofs true)\n(set-logic QF_LIA)\n");
    script.push_str(&reach_session_declarations());
    for (name, expected) in REACH_SESSION_ROWS {
        script.push_str("\n(push 1)\n");
        script.push_str(&row_assertions(name));
        script.push_str("\n(check-sat)\n");
        if expected == "unsat" {
            script.push_str("(get-proof)\n");
        }
        script.push_str("(pop 1)");
    }
    let (verdicts, reason, outputs) = verdicts(&script);
    let expected: Vec<&str> = REACH_SESSION_ROWS.iter().map(|&(_, v)| v).collect();
    assert_eq!(verdicts, expected, "({reason:?})");
    let proofs: Vec<&String> = outputs
        .iter()
        .filter(|line| line.contains("(assume "))
        .collect();
    let refutations = REACH_SESSION_ROWS
        .iter()
        .filter(|&&(_, verdict)| verdict == "unsat")
        .count();
    assert_eq!(
        proofs.len(),
        refutations,
        "every refutation prints its proof: {outputs:?}"
    );
    for proof in proofs {
        assert!(
            !proof.contains("(error")
                && !proof.contains(":rule hole")
                && !proof.contains(":rule trust"),
            "a session refutation printed an unchecked document:\n{proof}"
        );
    }
}

/// CLAIM 3's two-path join: the reachability-encoded join of
/// `a5_two_next_if_ok_sym` (`R_bb5 == Or(and R_bb2 (not c), and R_bb2 c)`).
/// Its substituted proof kept one premiseless leaf (the authored index
/// disjunction after `a__slice_len |-> _13` substitution, re-sorted by
/// `mk_or`) until the checked or_pos/or_neg reorder bridge
/// (`proof_propagated_rewrite/connective_reorder.rs`) reached the scalar
/// replay lane. Since main db768acbd the unrewritten replay ALSO certifies it
/// without the bridge, so the second half pins the lane: with the replay off
/// (kill switch, this thread only) the ordinary proof certifies alone (without
/// the bridge: `unknown`, self-check-rejected, measured 2026-10-07).
#[test]
#[timeout(300_000)]
fn the_reach_encoded_a5_join_certifies_and_its_mutant_stays_sat() {
    let dir = "deductive_checksgen_reach_encoding";
    let row = fixture(dir, "a5_two_next_if_ok_sym_reach.smt2");
    let mutant = fixture(dir, "a5_two_next_if_ok_sym_reach_sat_mutant.smt2");
    assert_certified_unsat("a5 reach row", &row);
    assert_never_refuted("a5 mutant", &mutant);
    let mut flags = ay_core::misc_cli_flags().clone();
    flags.no_consequence_replay = true;
    let _replay_off = ay_core::misc_test_override::set(flags);
    assert_certified_unsat("a5 reach row, replay off", &row);
    assert_never_refuted("a5 mutant, replay off", &mutant);
}

/// A query over a BOOLEAN definition, decided without variable substitution
/// (the unrewritten replay's posture): `b ≡ (< x y)`, `b` and `(>= x y)`. The
/// checked-SAT bridge transports `b` to `(< x y)` across the definition; that
/// step is `equiv_pos2`, not a congruence over a predicate application.
fn boolean_definition_query(conflict: &str) -> String {
    format!(
        "(set-option :produce-proofs true)
(set-option :ay-proof-no-varsubst true)
(set-logic QF_LIA)
(declare-fun b () Bool)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (and (= b (< x y)) b {conflict}))
(check-sat)
"
    )
}

#[test]
#[timeout(120_000)]
fn a_boolean_definition_transport_certifies_without_substitution() {
    assert_certified_unsat(
        "b = (< x y), b, x >= y",
        &boolean_definition_query("(>= x y)"),
    );
    assert_never_refuted(
        "b = (< x y), b, x < y",
        &boolean_definition_query("(< x y)"),
    );
}

/// The fixture's SMT-LIB body without its option, logic and query lines.
fn row_body(text: &str) -> String {
    text.lines()
        .filter(|line| {
            let line = line.trim_start();
            !(line.starts_with(';')
                || line.starts_with("(set-option")
                || line.starts_with("(set-logic")
                || line.starts_with("(check-sat"))
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// CLAIM 3 through the native API the in-process lane drives, as ONE session:
/// the rows' declarations once, then every row in its own scope of one
/// solver, each UNSAT row's exported artifact strictly verified and printed
/// without a `hole` or `trust` step, each SAT mutant decided `sat` in a later
/// scope of the same solver — so neither a certified row's proof state nor
/// its premises survive the `pop` into the next row.
#[test]
#[timeout(600_000)]
fn the_reach_encoding_rows_certify_in_one_api_session() {
    use ay_dpll::api::{Logic, Solver, StrictProofVerdict};

    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA solver");
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(&reach_session_declarations())
        .expect("declarations");
    for name in [
        "coroutine_resume_saturated_unreachable",
        "path_budget_async_sentinel",
        "a5_two_next_if_ok_sym_reach",
    ] {
        for (file, refuted) in [
            (name.to_string(), true),
            (format!("{name}_sat_mutant"), false),
        ] {
            solver.push();
            solver
                .parse_smtlib2(&row_assertions(&file))
                .unwrap_or_else(|e| panic!("{file}: {e}"));
            let result = solver.check_sat();
            if refuted {
                assert!(result.is_unsat(), "{file}: {result:?}");
                let artifact = solver
                    .export_last_unsat_artifact()
                    .unwrap_or_else(|| panic!("{file}: an UNSAT exports its artifact"));
                assert!(
                    matches!(artifact.strict_verdict, StrictProofVerdict::Verified(_)),
                    "{file}: {:?}",
                    artifact.strict_verdict
                );
                assert!(
                    artifact.alethe.contains("(assume ")
                        && !artifact.alethe.contains(":rule hole")
                        && !artifact.alethe.contains(":rule trust"),
                    "{file}: the artifact renders a checked document:\n{}",
                    artifact.alethe
                );
            } else {
                assert!(result.is_sat(), "{file}: {result:?}");
            }
            solver.pop();
        }
    }
}
