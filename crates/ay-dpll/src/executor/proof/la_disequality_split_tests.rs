// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Wire-exact and falsify-once audit for the n-guard `la_disequality`
//! backbone.

use super::*;
use ay_core::Sort;
use ay_frontend::parse;

/// The standalone expression-split family (#6660). MEASURED: the arithmetic
/// branch's blocking clause is recorded as `ArithClauseTautology`, a kind AY's
/// strict checker RE-DERIVES and the pinned calculus cannot spell, so the
/// published step was `:rule hole` while the whole document already passed
/// `check_proof_strict`.
///
/// The head equality carries a surface override that FLIPS its printed
/// operands (`(= z (+ x y))` in the DAG, `(= (+ x y) z)` on the wire), so the
/// in-place n-guard split fails closed on it — a DAG-ordered `la_disequality`
/// would print `(or (= A B) (not (<= B A)) (not (<= A B)))`, which the pinned
/// external checker rejects. The whole-proof authored lane owns this family
/// instead: it works from the SURFACE roots, so its split is print-correct.
#[test]
fn standalone_expression_split_publishes_the_exact_la_disequality_wire_text() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const gate Bool)
        (declare-const x Real)
        (declare-const y Real)
        (declare-const z Real)
        (assert (= x 1.0))
        (assert (= y 0.0))
        (assert (= z 1.0))
        (assert (not gate))
        (assert (or gate (not (= (+ x y) z))))
        (check-sat)
        (get-proof)
    "#;
    let mut exec = Executor::new();
    let commands = parse(input).expect("parse the standalone expression-split input");
    let outputs = exec
        .execute_all(&commands)
        .expect("execute the standalone expression-split input");
    assert_eq!(outputs[0], "unsat");
    let proof = &outputs[1];

    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "the guarded-equality leaf must not stay unproved:\n{proof}"
    );
    // The split is the pinned rule's rigid shape, with the two bounds in
    // FORWARD then REVERSE order of the PRINTED equality operands, and both
    // sides of it are ordinary Farkas implications of the three equalities.
    for line in [
        "(step t5 (cl (not (= x 1.0)) (not (= y 0.0)) (not (= z 1.0)) (<= (+ x y) z)) :rule la_generic :args (-1 -1 1 1))",
        "(step t8 (cl (<= (+ x y) z)) :rule resolution :premises (t7 t2))",
        "(step t9 (cl (not (= x 1.0)) (not (= y 0.0)) (not (= z 1.0)) (<= z (+ x y))) :rule la_generic :args (1 1 -1 1))",
        "(step t12 (cl (<= z (+ x y))) :rule resolution :premises (t11 t2))",
        "(step t13 (cl (or (= (+ x y) z) (not (<= (+ x y) z)) (not (<= z (+ x y))))) :rule la_disequality)",
        "(step t14 (cl (= (+ x y) z) (not (<= (+ x y) z)) (not (<= z (+ x y)))) :rule or :premises (t13))",
        "(step t15 (cl (= (+ x y) z) (not (<= z (+ x y)))) :rule resolution :premises (t14 t8))",
        "(step t16 (cl (= (+ x y) z)) :rule resolution :premises (t15 t12))",
        "(step t19 (cl) :rule resolution :premises (t16 t18))",
    ] {
        assert!(
            proof.contains(line),
            "missing exact wire line:\n{line}\nin:\n{proof}"
        );
    }

    let internal = exec.last_proof().expect("a published UNSAT proof");
    let quality = ay_proof::check_proof_with_quality(internal, exec.terms())
        .expect("the published proof must check");
    assert_eq!(quality.hole_count, 0, "{quality:?}\n{proof}");
    assert_eq!(quality.trust_count, 0, "{quality:?}\n{proof}");
}

/// The in-place n-guard split must DECLINE this leaf, and say so through the
/// planner itself: the printed shape would not be the rule's. Pinning the
/// decline here is what stops a later "simplification" of the print-shape
/// authentication from turning a holey document into a rejected one.
#[test]
fn flipped_equality_override_declines_the_in_place_split() {
    let mut exec = Executor::new();
    let x = real_var(&mut exec, "flip_x");
    let y = real_var(&mut exec, "flip_y");
    let z = real_var(&mut exec, "flip_z");
    let sum = exec
        .ctx
        .terms
        .mk_app(Symbol::named("+"), [x, y], Sort::Real);
    // DAG order `(= z (+ x y))`, printed as the file's `(= (+ x y) z)`.
    let equality = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [z, sum], Sort::Bool);
    let bounds = [
        atom(&mut exec, ">=", x, 1),
        atom(&mut exec, "<=", x, 1),
        atom(&mut exec, ">=", y, 0),
        atom(&mut exec, "<=", y, 0),
        atom(&mut exec, ">=", z, 1),
        atom(&mut exec, "<=", z, 1),
    ];
    let guards: Vec<TermId> = bounds
        .iter()
        .map(|&bound| exec.ctx.terms.mk_not_raw(bound))
        .collect();
    let mut leaf = vec![equality];
    leaf.extend_from_slice(&guards);

    // Without the override the leaf IS derivable: both legs certify and the
    // printed shape is the rule's.
    assert!(
        exec.plan_la_disequality_split_fragment(&leaf).is_some(),
        "the override-free orientation must be derivable"
    );

    // With the flipping override it must not be.
    let mut overrides = ay_core::kani_compat::DetHashMap::default();
    let _ = overrides.insert(equality, "(= (+ flip_x flip_y) flip_z)".to_string());
    exec.last_proof_term_overrides = Some(overrides);
    assert!(
        exec.plan_la_disequality_split_fragment(&leaf).is_none(),
        "a flipped print of the head equality must fail closed"
    );
}

fn real_var(exec: &mut Executor, name: &str) -> TermId {
    exec.ctx.terms.mk_var(name, Sort::Real)
}

fn real_constant(exec: &mut Executor, value: i64) -> TermId {
    exec.ctx
        .terms
        .mk_rational(num_rational::BigRational::from(BigInt::from(value)))
}

fn atom(exec: &mut Executor, operator: &str, left: TermId, value: i64) -> TermId {
    let right = real_constant(exec, value);
    exec.ctx
        .terms
        .mk_app(Symbol::named(operator), [left, right], Sort::Bool)
}

/// Build the six-step split byte-for-byte as the planner would emit it — same
/// rules, same order, same clause shapes — but with an all-ones coefficient
/// vector instead of a re-verified certificate, then close it against the
/// assumptions so the document ends in the empty clause. Any refusal can then
/// only come from the derivation itself.
fn plant_split_document(
    exec: &mut Executor,
    equality: TermId,
    sum: TermId,
    z: TermId,
    bounds: &[TermId],
    guards: &[TermId],
    leaf: &[TermId],
) -> Proof {
    let le_st = exec
        .ctx
        .terms
        .mk_app(Symbol::named("<="), [sum, z], Sort::Bool);
    let le_ts = exec
        .ctx
        .terms
        .mk_app(Symbol::named("<="), [z, sum], Sort::Bool);
    let not_le_st = exec.ctx.terms.mk_not_raw(le_st);
    let not_le_ts = exec.ctx.terms.mk_not_raw(le_ts);
    let not_equality = exec.ctx.terms.mk_not_raw(equality);
    let or_term = exec.ctx.terms.mk_app(
        Symbol::named("or"),
        [equality, not_le_st, not_le_ts],
        Sort::Bool,
    );

    let mut forged = Proof::new();
    let bound_assumes: Vec<ProofId> = bounds
        .iter()
        .map(|&bound| forged.add_assume(bound, None))
        .collect();
    let diseq_assume = forged.add_assume(not_equality, None);
    let split = forged.add_rule_step(
        AletheRule::LaDisequality,
        vec![or_term],
        Vec::new(),
        Vec::new(),
    );
    let flat = forged.add_rule_step(
        AletheRule::Or,
        vec![equality, not_le_st, not_le_ts],
        vec![split],
        Vec::new(),
    );
    let ones = FarkasAnnotation::from_ints(&[1, 1, 1, 1, 1]);
    let mut forward = vec![le_st];
    forward.extend_from_slice(guards);
    let forward_leg = forged.add_step(ProofStep::TheoryLemma {
        theory: "LRA".to_string(),
        clause: forward,
        farkas: Some(ones.clone()),
        kind: TheoryLemmaKind::LraFarkas,
        lia: None,
    });
    let mut reverse = vec![le_ts];
    reverse.extend_from_slice(guards);
    let reverse_leg = forged.add_step(ProofStep::TheoryLemma {
        theory: "LRA".to_string(),
        clause: reverse,
        farkas: Some(ones),
        kind: TheoryLemmaKind::LraFarkas,
        lia: None,
    });
    let mut residual = vec![equality, not_le_ts];
    residual.extend_from_slice(guards);
    let after_forward = forged.add_rule_step(
        AletheRule::Resolution,
        residual,
        vec![flat, forward_leg],
        Vec::new(),
    );
    let mut current = forged.add_rule_step(
        AletheRule::Resolution,
        leaf.to_vec(),
        vec![after_forward, reverse_leg],
        Vec::new(),
    );
    let mut open = leaf.to_vec();
    for (&bound, &assume) in bounds.iter().zip(bound_assumes.iter()) {
        let complement = exec.ctx.terms.mk_not_raw(bound);
        open.retain(|&literal| literal != complement);
        current = forged.add_resolution(open.clone(), bound, current, assume);
    }
    let _ = forged.add_resolution(Vec::new(), equality, current, diseq_assume);
    forged
}

/// FALSIFY-ONCE. The guard set constrains `x` and `y` but leaves `z` free, so
/// `x + y = z` does NOT follow and the whole assertion set is SATISFIABLE
/// (`x = 1, y = 0, z = 5`). A byte-identical planted derivation — the same six
/// steps, the same rules, in the same order, with the coefficient vector the
/// sound case would carry — must be refused by the untouched strict checker,
/// and the planner must decline to build it in the first place.
#[test]
fn planted_split_over_a_satisfiable_instance_is_rejected() {
    // The instance really is satisfiable; the planted document below claims a
    // refutation of it.
    let sat_input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (declare-const z Real)
        (assert (>= x 1.0))
        (assert (<= x 1.0))
        (assert (>= y 0.0))
        (assert (<= y 0.0))
        (assert (not (= (+ x y) z)))
        (check-sat)
    "#;
    let mut probe = Executor::new();
    let commands = parse(sat_input).expect("parse the satisfiable probe");
    let outputs = probe
        .execute_all(&commands)
        .expect("execute the satisfiable probe");
    assert_eq!(
        outputs[0], "sat",
        "the falsify-once fixture must be satisfiable"
    );

    let mut exec = Executor::new();
    let x = real_var(&mut exec, "la_split_x");
    let y = real_var(&mut exec, "la_split_y");
    let z = real_var(&mut exec, "la_split_z");
    let sum = exec
        .ctx
        .terms
        .mk_app(Symbol::named("+"), [x, y], Sort::Real);
    let equality = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [sum, z], Sort::Bool);
    let bounds = [
        atom(&mut exec, ">=", x, 1),
        atom(&mut exec, "<=", x, 1),
        atom(&mut exec, ">=", y, 0),
        atom(&mut exec, "<=", y, 0),
    ];
    let guards: Vec<TermId> = bounds
        .iter()
        .map(|&bound| exec.ctx.terms.mk_not_raw(bound))
        .collect();
    let mut leaf = vec![equality];
    leaf.extend_from_slice(&guards);

    // (1) The planner declines: neither leg has a re-verified certificate.
    assert!(
        exec.plan_la_disequality_split_fragment(&leaf).is_none(),
        "a satisfiable guard set must not yield a split fragment"
    );

    // (2) The planted document, terminating in the empty clause so the
    //     refusal can only come from the derivation itself.
    let forged = plant_split_document(&mut exec, equality, sum, z, &bounds, &guards, &leaf);
    let rejection = ay_proof::check_proof_strict(&forged, &exec.ctx.terms)
        .expect_err("a planted refutation of a satisfiable instance must be refused");
    assert!(
        !matches!(rejection, ay_proof::ProofCheckError::ResourceLimit),
        "the planted derivation must be refused on the merits, not by a cap: {rejection}"
    );
}

/// The `la_disequality` tautology is position-sensitive. Two documents that
/// differ ONLY in the operand order inside the split's `or` term must get
/// opposite verdicts from the untouched strict checker — that is what stops a
/// planner from "helpfully" reordering the split.
#[test]
fn swapped_split_bounds_flip_the_strict_verdict() {
    let mut exec = Executor::new();
    let x = real_var(&mut exec, "la_swap_x");
    let z = real_var(&mut exec, "la_swap_z");
    let equality = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [x, z], Sort::Bool);
    let le_xz = exec
        .ctx
        .terms
        .mk_app(Symbol::named("<="), [x, z], Sort::Bool);
    let le_zx = exec
        .ctx
        .terms
        .mk_app(Symbol::named("<="), [z, x], Sort::Bool);
    let not_le_xz = exec.ctx.terms.mk_not_raw(le_xz);
    let not_le_zx = exec.ctx.terms.mk_not_raw(le_zx);
    let not_equality = exec.ctx.terms.mk_not_raw(equality);

    let build = |exec: &mut Executor, disjuncts: [TermId; 3]| -> Proof {
        let or_term = exec
            .ctx
            .terms
            .mk_app(Symbol::named("or"), disjuncts, Sort::Bool);
        let mut proof = Proof::new();
        let diseq = proof.add_assume(not_equality, None);
        let forward = proof.add_assume(le_xz, None);
        let reverse = proof.add_assume(le_zx, None);
        let split = proof.add_rule_step(
            AletheRule::LaDisequality,
            vec![or_term],
            Vec::new(),
            Vec::new(),
        );
        let flat = proof.add_rule_step(AletheRule::Or, disjuncts.to_vec(), vec![split], Vec::new());
        let without_equality =
            proof.add_resolution(vec![not_le_xz, not_le_zx], equality, flat, diseq);
        let without_forward =
            proof.add_resolution(vec![not_le_zx], le_xz, without_equality, forward);
        let _ = proof.add_resolution(Vec::new(), le_zx, without_forward, reverse);
        proof
    };

    let sound = build(&mut exec, [equality, not_le_xz, not_le_zx]);
    assert!(
        ay_proof::check_proof_strict(&sound, &exec.ctx.terms).is_ok(),
        "the canonical operand order must be accepted"
    );
    let swapped = build(&mut exec, [equality, not_le_zx, not_le_xz]);
    assert!(
        ay_proof::check_proof_strict(&swapped, &exec.ctx.terms).is_err(),
        "a swapped la_disequality split must be refused"
    );
}

/// The planner is fail-closed on SHAPE as well as on evidence: a leaf whose
/// head is not a positive same-sorted arithmetic equality, or that carries a
/// guard `la_generic` cannot read, keeps its hole.
#[test]
fn non_arithmetic_shapes_keep_their_hole() {
    let mut exec = Executor::new();
    let x = real_var(&mut exec, "la_shape_x");
    let y = real_var(&mut exec, "la_shape_y");
    let z = real_var(&mut exec, "la_shape_z");
    let sum = exec
        .ctx
        .terms
        .mk_app(Symbol::named("+"), [x, y], Sort::Real);
    let equality = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [sum, z], Sort::Bool);
    let bound = atom(&mut exec, ">=", x, 1);
    let guard = exec.ctx.terms.mk_not_raw(bound);

    // No guards at all.
    assert!(exec
        .plan_la_disequality_split_fragment(&[equality])
        .is_none());
    // A NEGATED equality head: the `la_disequality` conclusion puts the
    // positive equality first, so this shape belongs to another backbone.
    let negated = exec.ctx.terms.mk_not_raw(equality);
    assert!(exec
        .plan_la_disequality_split_fragment(&[negated, guard])
        .is_none());
    // A Boolean guard `la_generic` cannot read.
    let gate = exec.ctx.terms.mk_var("la_shape_gate", Sort::Bool);
    assert!(exec
        .plan_la_disequality_split_fragment(&[equality, gate])
        .is_none());
    // A Bool-sorted equality head.
    let other_gate = exec.ctx.terms.mk_var("la_shape_gate_other", Sort::Bool);
    let boolean_equality =
        exec.ctx
            .terms
            .mk_app(Symbol::named("="), [gate, other_gate], Sort::Bool);
    assert!(exec
        .plan_la_disequality_split_fragment(&[boolean_equality, guard])
        .is_none());
}

/// END TO END for the in-place lane. A THREE-disjunct guard blocks the
/// whole-proof authored lane (which admits only a binary authored
/// disjunction), so the residual arithmetic leaf must reach this backbone and
/// be derived in place — reproducing its own clause, so the downstream
/// resolution chain is untouched.
#[test]
fn three_disjunct_guard_reaches_the_in_place_n_guard_split() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const g1 Bool)
        (declare-const g2 Bool)
        (declare-const x Real)
        (declare-const y Real)
        (declare-const z Real)
        (assert (= x 1.0))
        (assert (= y 0.0))
        (assert (= z 1.0))
        (assert (not g1))
        (assert (not g2))
        (assert (or g1 g2 (not (= z (+ x y)))))
        (check-sat)
        (get-proof)
    "#;
    let mut exec = Executor::new();
    let commands = parse(input).expect("parse the three-disjunct input");
    let outputs = exec
        .execute_all(&commands)
        .expect("execute the three-disjunct input");
    assert_eq!(outputs[0], "unsat");
    let proof = &outputs[1];
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "no unproved step may survive:\n{proof}"
    );
    for line in [
        "(step t27 (cl (or (= z (+ x y)) (not (<= z (+ x y))) (not (<= (+ x y) z)))) :rule la_disequality)",
        "(step t28 (cl (= z (+ x y)) (not (<= z (+ x y))) (not (<= (+ x y) z))) :rule or :premises (t27))",
    ] {
        assert!(
            proof.contains(line),
            "missing exact wire line:\n{line}\nin:\n{proof}"
        );
    }
    // Exactly one split, two legs, and a terminal resolution that reproduces
    // the leaf's own clause.
    assert_eq!(proof.matches(":rule la_disequality").count(), 1, "{proof}");

    let internal = exec.last_proof().expect("a published UNSAT proof");
    let quality = ay_proof::check_proof_with_quality(internal, exec.terms())
        .expect("the spliced proof must still check");
    assert_eq!(quality.hole_count, 0, "{quality:?}\n{proof}");
    assert_eq!(quality.trust_count, 0, "{quality:?}\n{proof}");
}
