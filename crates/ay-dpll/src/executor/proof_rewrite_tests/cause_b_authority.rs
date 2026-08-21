// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `proof_rewrite_tests.rs` to preserve the existing test
// fully qualified names.

// #cause-b-parsed-gate / #cause-b-narrow-split
//
// Two pins that must move TOGETHER or not at all:
//
//   1. With no parsed-assertion prefix (the `--z3-mode` / `--no-proof` /
//      competition configuration, `set_retain_parsed_assertions(false)`,
//      #rss-vs-z3), the ASSUMPTION-AUTHORITY passes STILL RUN. They reason
//      purely over canonical `TermId`s; only the surface-syntax half needs the
//      frontend ASTs. Before 540fe30fb the shared early return switched both
//      halves off, so every foreign leaf stayed a bare `Assume`,
//      `UnauthorizedAssumption` is not trust-eligible in `unsat_cert.rs`, and
//      89 computed-correct refutations published `unknown` once 66538b006f made
//      the certificate mandatory.
//
//   2. `derive_conjunct_assumptions_from_problem_roots` must NOT run in that
//      configuration. Running the whole tail there was measured over 2,166
//      non-QF_Datatypes instances at +301 gained / 12 LOST / 0 wrong, and all
//      12 losses are that one pass: 8 are a re-validation blowup it triggers by
//      restructuring the proof (`QF_IDL/parity`; `04.100.graph` 0.05s ->
//      139-167s) and 4 are a malformed `and_pos` it emits and then rejects
//      ("clause must contain the and gate literal and the indexed conjunct",
//      spanning `QF_IDL/parity`, `QF_IDL/sep/hardware` and `QF_LIA/convert`).
//      Cause B does not need it — demotion alone restores the verdict.
// ---------------------------------------------------------------------------

/// `(and a b)` asserted as the single problem assertion, with the parsed
/// prefix retained or dropped. Returns `(exec, root, a, b)`.
#[cfg(test)]
fn cause_b_and_root_fixture(retain_parsed: bool) -> (Executor, TermId, TermId, TermId) {
    let mut exec = Executor::new();
    exec.ctx.set_retain_parsed_assertions(retain_parsed);
    let a = exec.ctx.terms.mk_var("cause-b-a", Sort::Bool);
    let b = exec.ctx.terms.mk_var("cause-b-b", Sort::Bool);
    let root = exec.ctx.terms.mk_and(vec![a, b]);
    exec.ctx.add_transient_assertion_with_parsed(
        root,
        ay_frontend::command::Term::Symbol("cause-b-root".to_string()),
    );
    assert_eq!(
        exec.ctx.assertions_parsed().is_empty(),
        !retain_parsed,
        "fixture did not model the requested retention configuration"
    );
    (exec, root, a, b)
}

#[cfg(test)]
fn cause_b_surviving_assumes(proof: &Proof) -> Vec<TermId> {
    proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Assume(term) => Some(*term),
            _ => None,
        })
        .collect()
}

#[cfg(test)]
fn cause_b_has_trust_clause(proof: &Proof, term: TermId) -> bool {
    proof.steps.iter().any(|step| {
        matches!(
            step,
            ProofStep::Step { rule: AletheRule::Trust, clause, .. }
                if clause.as_slice() == [term]
        )
    })
}

#[cfg(test)]
fn cause_b_has_and_pos(proof: &Proof) -> bool {
    proof.steps.iter().any(|step| {
        matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::AndPos(_),
                ..
            }
        )
    })
}

/// REGRESSION (#cause-b-parsed-gate): with the parsed prefix dropped, a foreign
/// assume is still DEMOTED to `trust`, so the certification funnel's
/// `discharge_trust_steps_for_certification` can reach it.
///
/// Fails before 540fe30fb: `apply_input_syntax_rewrites_to_proof` returned
/// immediately, the foreign assume survived verbatim, and strict certification
/// rejected the whole refutation with `UnauthorizedAssumption` — an error that
/// is NOT trust-eligible, so the discharge rescue never ran.
#[test]
fn cause_b_authority_passes_run_without_parsed_retention() {
    let (mut exec, root, a, _b) = cause_b_and_root_fixture(false);
    let lane_axiom = exec.ctx.terms.mk_var("cause-b-lane-axiom", Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(root, None);
    proof.add_assume(a, None);
    proof.add_assume(lane_axiom, None);

    exec.apply_input_syntax_rewrites_to_proof(&mut proof);

    let surviving = cause_b_surviving_assumes(&proof);
    assert!(
        surviving.contains(&root),
        "the authored root must remain an assume"
    );
    assert!(
        !surviving.contains(&lane_axiom),
        "the foreign lane axiom must not survive as a bare `assume`: that is exactly \
         the leaf that makes strict certification report UnauthorizedAssumption, which \
         unsat_cert.rs cannot re-discharge"
    );
    assert!(
        cause_b_has_trust_clause(&proof, lane_axiom),
        "the foreign lane axiom must be demoted to a `trust` clause so the \
         certification funnel's discharge path can re-derive it"
    );
}

/// PIN (#cause-b-narrow-split): the COSTLY pass must NOT run when the parsed
/// prefix was dropped.
///
/// `derive_conjunct_assumptions_from_problem_roots` is the sole source of all
/// 12 measured out-of-division losses (8 re-validation blowups + 4 malformed
/// `and_pos`). In the retention-off configuration the conjunct assume must
/// therefore be DEMOTED to `trust` — never derived through `and_pos`.
///
/// The retention-ON control in the same test is what makes this a pin on the
/// CONFIGURATION rather than on the pass being dead everywhere: flip the split
/// back to "run the whole tail" and the first assertion fires; delete the pass
/// outright and the control fires.
#[test]
fn cause_b_costly_derivation_pass_is_gated_off_without_parsed_retention() {
    // Retention OFF — the narrowed subset.
    let (mut exec, root, a, _b) = cause_b_and_root_fixture(false);
    let mut proof = Proof::new();
    proof.add_assume(root, None);
    proof.add_assume(a, None);
    exec.apply_input_syntax_rewrites_to_proof(&mut proof);

    assert!(
        !cause_b_has_and_pos(&proof),
        "derive_conjunct_assumptions_from_problem_roots must NOT run without a parsed \
         prefix: it is the measured cause of all 12 out-of-division losses (8 \
         re-validation blowups in QF_IDL/parity, 4 malformed and_pos in \
         QF_IDL/parity + QF_IDL/sep/hardware + QF_LIA/convert), and cause B does not \
         need it"
    );
    assert!(
        cause_b_has_trust_clause(&proof, a),
        "the conjunct assume must instead be demoted to `trust`, which the \
         certification funnel discharges independently"
    );

    // Retention ON — the control. Same fixture, same proof shape; here the
    // derivation pass is expected to fire, so the pin above is about the
    // configuration, not about the pass being unreachable.
    let (mut exec_on, root_on, a_on, _b_on) = cause_b_and_root_fixture(true);
    let mut proof_on = Proof::new();
    proof_on.add_assume(root_on, None);
    proof_on.add_assume(a_on, None);
    exec_on.apply_input_syntax_rewrites_to_proof(&mut proof_on);
    assert!(
        cause_b_has_and_pos(&proof_on),
        "CONTROL: with a parsed prefix retained, the conjunct must still be DERIVED \
         via and_pos — the narrow split changes the retention-off path only"
    );
}

/// BOUNDARY (#cause-b-parsed-gate, negative test): the split must not widen the
/// certification boundary. A solver-minted term gains no problem authority, and
/// a proof that assumes it directly is still hard-rejected.
///
/// This is the test that distinguishes "fixed the closure" from "removed the
/// check": the SAME term the pass above demotes to `trust` is shown here to
/// enter no obligation.
#[test]
fn cause_b_foreign_term_never_gains_problem_authority() {
    let (mut exec, root, a, _b) = cause_b_and_root_fixture(false);
    let forged = exec.ctx.terms.mk_var("cause-b-forged-premise", Sort::Bool);

    let obligation = exec.problem_assertions_for_strict_proof();
    assert!(
        obligation.contains(&root),
        "the authored root must be in the obligation"
    );
    assert!(
        !obligation.contains(&forged),
        "BOUNDARY BREACH: a solver-minted term entered the problem obligation"
    );
    assert!(
        !obligation.contains(&a),
        "the and-conjunct must NOT be added to the obligation either; it is admitted \
         by the checker's own `and`-closure, or DERIVED, or demoted — never by \
         widening the frozen obligation"
    );

    let mut proof = Proof::new();
    proof.add_assume(root, None);
    proof.add_assume(forged, None);
    exec.apply_input_syntax_rewrites_to_proof(&mut proof);
    let obligation_after = exec.problem_assertions_for_strict_proof();
    assert_eq!(
        obligation, obligation_after,
        "the authority passes must never mutate the frozen obligation"
    );

    let mut forged_proof = Proof::new();
    forged_proof.add_assume(root, None);
    forged_proof.add_assume(forged, None);
    let error = exec
        .check_proof_strict_with_datatypes(&forged_proof)
        .expect_err("an unauthorized assume must still be rejected");
    assert!(
        matches!(
            error,
            ay_proof::ProofCheckError::UnauthorizedAssumption { term, .. } if term == forged
        ),
        "expected UnauthorizedAssumption on the forged premise, got {error:?}"
    );
}
