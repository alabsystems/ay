// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! REACHABILITY for the fold-to-`false` promoter: the production `execute_all`
//! path in the mode a proof-artifact consumer actually runs in.
//!
//! The unit test beside the promoter proves its accepting step cannot be fooled.
//! It cannot prove anything ever builds the state. These do: an ordinary
//! SMT-LIB script whose authored assertion the preprocessor folds to `false`,
//! under `(set-option :produce-proofs true)`.
//!
//! Measured before the promoter, every accepting case here printed `unknown`:
//!
//! ```text
//! computed UNSAT rejected by mandatory strict certification:
//! strict UNSAT proof validation failed: step t0 uses unsupported hole rule
//! ```
//!
//! That `t0` is `false_source::set_empty_hole` — the ENTIRE proof erased to one
//! unattributed step, because the fold kept no record of the rewrite. Under an
//! explicit artifact request, independent query authority may not substitute
//! for the missing derivation (`nested_row_auxiliary_hole_fails_closed_when_alethe_artifact_is_required`
//! pins that), so a correct UNSAT was withdrawn. The promoter records the
//! argument instead, and the funnel's ORDINARY strict path accepts it.

use ay_dpll::Executor;
use ay_frontend::parse;

fn run(script: &str) -> (Vec<String>, Option<String>) {
    let commands = parse(script).expect("fixture script must parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("fixture script must run");
    let proof = if outputs.last().map(String::as_str) == Some("unsat") {
        let get_proof = parse("(get-proof)").expect("(get-proof) must parse");
        exec.execute_all(&get_proof)
            .ok()
            .and_then(|out| out.last().cloned())
    } else {
        None
    };
    (outputs, proof)
}

fn run_with_proofs(body: &str) -> (Vec<String>, Option<String>) {
    run(&format!("(set-option :produce-proofs true)\n{body}"))
}

/// Every step of a published closed-constant refutation, as EXACT WIRE TEXT.
///
/// A rule-NAME `contains` is not enough, and this table is where that was
/// measured. The assertion it replaces was `proof.contains(":rule
/// th_resolution")`, which is true only of the WEAKER shape — a
/// `BvLiaTautology` step printing `hole`, discharged by one `th_resolution`.
/// The moment the ground-linear rebuild took these queries the old assertion
/// failed for reporting a WIN. The tempting repair,
/// `contains(":rule th_resolution") || contains(":rule resolution")`, rots the
/// same way one notch weaker: it passes on the `hole`-bearing shape too, so it
/// could never see this gap close OR re-open. Pin the bytes instead.
///
/// The last two rows are not in the original defect report. They generalise
/// the fix past the two-disjunct case it was found on: three disjuncts, and a
/// NEGATED disjunct whose resolution operands are the mirror image.
const PUBLISHED_REFUTATIONS: [(&str, &str); 7] = [
    (
        "(< 2 0)",
        "(assume t0 (< 2 0))\n\
         (step t1 (cl (not (< 2 0))) :rule la_generic :args (1))\n\
         (step t2 (cl) :rule resolution :premises (t1 t0))",
    ),
    (
        "(>= 2 32)",
        "(assume t0 (>= 2 32))\n\
         (step t1 (cl (not (>= 2 32))) :rule la_generic :args (1))\n\
         (step t2 (cl) :rule resolution :premises (t1 t0))",
    ),
    (
        "(or (< 2 0) (>= 2 32))",
        "(assume t0 (or (< 2 0) (>= 2 32)))\n\
         (step t1 (cl (< 2 0) (>= 2 32)) :rule or :premises (t0))\n\
         (step t2 (cl (not (< 2 0))) :rule la_generic :args (1))\n\
         (step t3 (cl (>= 2 32)) :rule resolution :premises (t2 t1))\n\
         (step t4 (cl (not (>= 2 32))) :rule la_generic :args (1))\n\
         (step t5 (cl) :rule resolution :premises (t4 t3))",
    ),
    (
        "(or (< 0 0) (>= 0 64))",
        "(assume t0 (or (< 0 0) (>= 0 64)))\n\
         (step t1 (cl (< 0 0) (>= 0 64)) :rule or :premises (t0))\n\
         (step t2 (cl (not (< 0 0))) :rule la_generic :args (1))\n\
         (step t3 (cl (>= 0 64)) :rule resolution :premises (t2 t1))\n\
         (step t4 (cl (not (>= 0 64))) :rule la_generic :args (1))\n\
         (step t5 (cl) :rule resolution :premises (t4 t3))",
    ),
    (
        "(or (< 2 0) (> 2 4294967295))",
        "(assume t0 (or (< 2 0) (> 2 4294967295)))\n\
         (step t1 (cl (< 2 0) (> 2 4294967295)) :rule or :premises (t0))\n\
         (step t2 (cl (not (< 2 0))) :rule la_generic :args (1))\n\
         (step t3 (cl (> 2 4294967295)) :rule resolution :premises (t2 t1))\n\
         (step t4 (cl (not (> 2 4294967295))) :rule la_generic :args (1))\n\
         (step t5 (cl) :rule resolution :premises (t4 t3))",
    ),
    (
        "(or (< 2 0) (>= 2 32) (> 2 4294967295))",
        "(assume t0 (or (< 2 0) (>= 2 32) (> 2 4294967295)))\n\
         (step t1 (cl (< 2 0) (>= 2 32) (> 2 4294967295)) :rule or :premises (t0))\n\
         (step t2 (cl (not (< 2 0))) :rule la_generic :args (1))\n\
         (step t3 (cl (>= 2 32) (> 2 4294967295)) :rule resolution :premises (t2 t1))\n\
         (step t4 (cl (not (>= 2 32))) :rule la_generic :args (1))\n\
         (step t5 (cl (> 2 4294967295)) :rule resolution :premises (t4 t3))\n\
         (step t6 (cl (not (> 2 4294967295))) :rule la_generic :args (1))\n\
         (step t7 (cl) :rule resolution :premises (t6 t5))",
    ),
    (
        "(or (not (>= 2 0)) (>= 2 32))",
        "(assume t0 (or (not (>= 2 0)) (>= 2 32)))\n\
         (step t1 (cl (not (>= 2 0)) (>= 2 32)) :rule or :premises (t0))\n\
         (step t2 (cl (>= 2 0)) :rule la_generic :args (1))\n\
         (step t3 (cl (>= 2 32)) :rule resolution :premises (t1 t2))\n\
         (step t4 (cl (not (>= 2 32))) :rule la_generic :args (1))\n\
         (step t5 (cl) :rule resolution :premises (t4 t3))",
    ),
];

/// `(id, premises, is_empty_clause)` for every `assume` / `step` line.
fn proof_steps(proof: &str) -> Vec<(String, Vec<String>, bool)> {
    proof
        .lines()
        .filter_map(|line| {
            let line = line.trim();
            let body = line
                .strip_prefix("(step ")
                .or_else(|| line.strip_prefix("(assume "))?;
            let id = body.split_whitespace().next()?.to_string();
            let premises = line
                .split_once(":premises (")
                .and_then(|(_, tail)| tail.split_once(')'))
                .map(|(inside, _)| inside.split_whitespace().map(str::to_string).collect())
                .unwrap_or_default();
            // A non-empty clause always has a literal after `(cl`, so ` (cl) `
            // identifies the empty clause and nothing else.
            Some((id, premises, line.contains(" (cl) ")))
        })
        .collect()
}

/// Every step the EMPTY clause rests on, TRANSITIVELY.
///
/// "`t0` occurs somewhere in the document" is NOT the property under test: a
/// dead `assume` the refutation never consumes satisfies that while the empty
/// clause still comes from nowhere. Walk the `:premises` edges instead.
fn empty_clause_support(proof: &str) -> Vec<String> {
    let steps = proof_steps(proof);
    let mut pending: Vec<String> = steps
        .iter()
        .filter(|(_, _, empty)| *empty)
        .map(|(id, _, _)| id.clone())
        .collect();
    let mut support: Vec<String> = Vec::new();
    while let Some(id) = pending.pop() {
        if support.contains(&id) {
            continue;
        }
        support.push(id.clone());
        if let Some((_, premises, _)) = steps.iter().find(|(step, _, _)| *step == id) {
            pending.extend(premises.iter().cloned());
        }
    }
    support
}

/// The `trust-certify::certify_closed_constant_contradiction` shape: a
/// disjunction of CLOSED order atoms, every disjunct constant-false. This is
/// the query `finish_certificate` puts to AY (`AyProofBackend::new_with_proofs`
/// -> `set_produce_proofs(true)`, no `:check-proofs-strict`) before it will
/// re-check a kernel term, and its gate is `Ok(AyProofResult::Unsat { .. })` —
/// AY's VERDICT. A withdrawal there closes the clean-CIC lane outright.
///
/// MEASURED at the parent of this commit: the two ATOMIC rows already
/// published the `la_generic` derivation the table records, while EVERY
/// disjunctive row published
///
/// ```text
/// (step t1 (cl (not (or (< 2 0) (>= 2 32)))) :rule hole)
/// (step t2 (cl) :rule th_resolution :premises (t1 t0))
/// ```
///
/// — a `BvLiaTautology` certificate AY re-derives internally but cannot name
/// on the Alethe wire. Same contradiction, same constants; one shipped
/// checkable and one did not.
#[test]
fn closed_constant_order_atoms_publish_a_checked_refutation() {
    for (assertion, published) in PUBLISHED_REFUTATIONS {
        let (outputs, proof) = run_with_proofs(&format!(
            "(set-logic QF_LIA)\n(assert {assertion})\n(check-sat)\n"
        ));
        assert_eq!(
            outputs.last().map(String::as_str),
            Some("unsat"),
            "{assertion}: the closed-constant contradiction lane needs a plain \
             Unsat verdict, got {outputs:?}"
        );

        // The proof is ANCHORED on the author's own assertion, not erased. A
        // bare `(step t0 (cl) :rule hole)` has no `assume` at all, so this is
        // the discriminator between "recorded" and "erased".
        let proof = proof.expect("a published UNSAT must export its artifact");
        assert!(
            proof.contains(&format!("(assume t0 {assertion})")),
            "{assertion}: the refutation must assume the AUTHORED assertion \
             verbatim, or an external checker cannot match it to the problem \
             premises:\n{proof}"
        );

        // NOTHING is held on trust. `hole` is what the pinned checker reports
        // as `holey`, and what mandatory certification declines by name.
        // Ordered BEFORE the byte pin deliberately: a regression that reopens
        // the gap should report the property it broke, not a text diff.
        assert!(
            !proof.contains(":rule hole"),
            "{assertion}: a closed-constant contradiction is re-derivable from \
             constants alone; no step of it may ship as a hole:\n{proof}"
        );

        // The assumption is genuinely CONSUMED: the empty clause depends on
        // `t0` through the premise graph, not merely alongside it.
        assert!(
            proof_steps(&proof).iter().any(|(_, _, empty)| *empty),
            "{assertion}: the document must derive an empty clause at all, or \
             there is nothing to walk back from:\n{proof}"
        );
        let support = empty_clause_support(&proof);
        assert!(
            support.iter().any(|id| id == "t0"),
            "{assertion}: `(cl)` must be TRANSITIVELY premised on the authored \
             assumption; reached {support:?} instead:\n{proof}"
        );

        // EVERY EMITTED STEP, as exact wire text. `trim_end` drops only the
        // document's terminating newline; no step text is normalized.
        assert_eq!(
            proof.trim_end(),
            published,
            "{assertion}: the published refutation changed byte for byte"
        );
    }
}

/// The promoter must never manufacture a refutation. Same fold machinery, a
/// true disjunct, so the query has a model.
#[test]
fn a_satisfiable_closed_constant_disjunction_stays_sat() {
    for assertion in [
        "(or (< 2 0) (>= 2 1))",
        "(>= 2 1)",
        "(or (< 0 1) (>= 0 64))",
        // n-ary, with the TRUE disjunct last: the disjunction rebuild peels
        // left to right, so this is the row that would catch a peel that
        // stopped checking once the prefix was refuted.
        "(or (< 2 0) (>= 2 32) (>= 2 1))",
    ] {
        let (outputs, _) = run_with_proofs(&format!(
            "(set-logic QF_LIA)\n(assert {assertion})\n(check-sat)\n"
        ));
        assert_eq!(
            outputs.last().map(String::as_str),
            Some("sat"),
            "{assertion} has a model and must never be published as a \
             refutation: {outputs:?}"
        );
    }
}

/// Requesting the artifact must not change the VERDICT. Before the promoter it
/// did — the caller who asked for MORE evidence got the weaker answer.
#[test]
fn the_same_query_agrees_with_and_without_an_artifact_request() {
    let body = "(set-logic QF_LIA)\n(assert (or (< 2 0) (>= 2 32)))\n(check-sat)\n";
    let (with_artifact, _) = run_with_proofs(body);
    let (without_artifact, _) = run(body);

    assert_eq!(
        with_artifact.last(),
        without_artifact.last(),
        "requesting a proof artifact must not change the verdict"
    );
}

/// THE BOUNDARY, pinned deliberately. The VerifierConsumer bare-claim obligation writes
/// its BV literals as `(_ bv1 64)`; the override-aware printer renders them
/// `#x0000000000000001`, so `rebuilt_root_prints_as_authored` refuses the
/// round-trip and the promoter declines. That guard is right — a premise an
/// external checker cannot match to the problem is strictly worse than the hole
/// it would replace (`authored_conjunct_eval`'s own rationale) — so the honest
/// state is a decline, and this pin records it.
///
/// EXPECTED TO GO RED IN THE GOOD DIRECTION once the printer and the surface
/// agree on bit-vector literal notation. A `sat` here would be the alarm.
#[test]
fn a_bitvector_literal_query_declines_the_promoter_and_stays_unknown() {
    let (outputs, _) = run_with_proofs(
        "(set-logic QF_BV)
(declare-const x (_ BitVec 64))
(declare-const r (_ BitVec 64))
(assert (= r (bvlshr x (_ bv1 64))))
(assert (not (bvule (_ bv0 64) (_ bv1 64))))
(check-sat)
",
    );
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unknown"),
        "the round-trip guard declines BV literal notation; a `sat` here would \
         mean the promoter published a model as a refutation: {outputs:?}"
    );
}
