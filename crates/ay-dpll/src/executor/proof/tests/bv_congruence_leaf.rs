// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// `concat (ite (= msb #b1) ones zeros) w` — external-codegen's decoded spelling of a
/// sign extension of `w`, as its A64 SMULL obligation writes it.
fn spelled_sign_extend(terms: &mut TermStore, word: TermId, width: u32) -> TermId {
    let msb = terms.mk_app(
        Symbol::indexed("extract", vec![width - 1, width - 1]),
        [word],
        Sort::bitvec(1),
    );
    let one = terms.mk_bitvec(BigInt::from(1), 1);
    let is_negative = terms.mk_app(Symbol::named("="), [msb, one], Sort::Bool);
    let ones = terms.mk_bitvec((BigInt::from(1) << width) - 1, width);
    let zeros = terms.mk_bitvec(BigInt::from(0), width);
    let fill = terms.mk_ite_raw(is_negative, ones, zeros);
    terms.mk_app(
        Symbol::named("concat"),
        [fill, word],
        Sort::bitvec(2 * width),
    )
}

/// Two spellings of a sign extension under one shared wide `bvmul` differ only
/// below the multiplier. The walker must prove them equal operand by operand —
/// two small `BvBitBlast` leaves lifted by one `cong` — instead of declining
/// and leaving the whole 64-bit multiplier miter to the recognizer, which no
/// solve budget closes (external-codegen row 2049).
#[test]
fn congruence_walker_lifts_sign_extend_spellings_through_a_wide_product() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(32));
    let y = terms.mk_var("y", Sort::bitvec(32));
    let spelled_x = spelled_sign_extend(&mut terms, x, 32);
    let spelled_y = spelled_sign_extend(&mut terms, y, 32);
    let sext_x = terms.mk_app(
        Symbol::indexed("sign_extend", vec![32]),
        [x],
        Sort::bitvec(64),
    );
    let sext_y = terms.mk_app(
        Symbol::indexed("sign_extend", vec![32]),
        [y],
        Sort::bitvec(64),
    );
    let left = terms.mk_app(
        Symbol::named("bvmul"),
        [spelled_x, spelled_y],
        Sort::bitvec(64),
    );
    let right = terms.mk_app(Symbol::named("bvmul"), [sext_x, sext_y], Sort::bitvec(64));

    let mut proof = Proof::new();
    let step = add_bvand_commutative_congruence_proof(&mut terms, &mut proof, left, right)
        .expect("the walker must lift the operand identities through bvmul");
    assert!(
        matches!(
            &proof.steps[step.0 as usize],
            ProofStep::Step {
                rule: AletheRule::Cong,
                premises,
                ..
            } if premises.len() == 2
        ),
        "the root must be a cong over both operands; got {:#?}",
        proof.steps
    );
    // Both operand identities rest on ONE joint lemma: a strict walk admits a
    // single expensive BV lemma, and each 32-bit leaf alone would be one.
    let lemmas: Vec<_> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::TheoryLemma { clause, kind, .. } => Some((clause.clone(), *kind)),
            _ => None,
        })
        .collect();
    assert_eq!(
        lemmas.len(),
        1,
        "one joint leaf lemma; got {:#?}",
        proof.steps
    );
    let (clause, kind) = &lemmas[0];
    assert_eq!(*kind, TheoryLemmaKind::BvBitBlast);
    assert!(
        matches!(terms.get(clause[0]), TermData::App(Symbol::Named(name), args) if name == "and" && args.len() == 2),
        "the joint lemma must conjoin the two operand identities"
    );
    // Close the refutation exactly as the collapse promotion does.
    let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let negated = terms.mk_not_raw(equality);
    let assume = proof.add_assume(negated, None);
    proof.add_resolution(vec![], equality, assume, step);
    let quality = ay_proof::check_proof_strict(&proof, &terms)
        .expect("the congruence certificate must pass strict replay");
    assert_eq!(quality.trust_count, 0);
    assert_eq!(quality.hole_count, 0);

    // The same walk over a FALSE operand pair (zero- instead of sign-extension)
    // is refused by the recognizer and leaves no step behind.
    let zext_x = terms.mk_app(
        Symbol::indexed("zero_extend", vec![32]),
        [x],
        Sort::bitvec(64),
    );
    let wrong = terms.mk_app(Symbol::named("bvmul"), [zext_x, sext_y], Sort::bitvec(64));
    let mut refused = Proof::new();
    assert!(
        add_bvand_commutative_congruence_proof(&mut terms, &mut refused, left, wrong).is_none()
    );
    assert!(refused.steps.is_empty(), "failed candidates must roll back");
}

/// A walk with ONE differing leaf emits that leaf's own lemma (no joint
/// conjunction is re-decided), so the per-leaf recognizer check is the only
/// semantic gate there: a single false operand pair must be refused.
#[test]
fn congruence_walker_refuses_a_single_false_bounded_leaf() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(32));
    let y = terms.mk_var("y", Sort::bitvec(64));
    let spelled_x = spelled_sign_extend(&mut terms, x, 32);
    let zext_x = terms.mk_app(
        Symbol::indexed("zero_extend", vec![32]),
        [x],
        Sort::bitvec(64),
    );
    let left = terms.mk_app(Symbol::named("bvmul"), [spelled_x, y], Sort::bitvec(64));
    let wrong = terms.mk_app(Symbol::named("bvmul"), [zext_x, y], Sort::bitvec(64));
    let mut refused = Proof::new();
    assert!(
        add_bvand_commutative_congruence_proof(&mut terms, &mut refused, left, wrong).is_none()
    );
    assert!(refused.steps.is_empty(), "failed candidates must roll back");
}

/// End to end: external-codegen's A64 SMULL obligation (row 2049) at its real width is
/// UNSAT with a strict, hole-free certificate inside a modest budget. Before
/// the general congruence leaf, the elaborator collapsed the assertion but the
/// proof reconstruction bit-blasted the whole 64-bit multiplier miter and ran
/// out the clock, turning the UNSAT into `unknown`.
#[test]
fn qf_bv_smull_sign_extend_spelling_collapse_is_fully_checked() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-option :timeout 30000)
        (set-logic QF_BV)
        (declare-const x7 (_ BitVec 64))
        (declare-const x12 (_ BitVec 64))
        (assert (not (= (bvmul (concat (ite (= ((_ extract 31 31) ((_ extract 31 0) x12)) (_ bv1 1)) (_ bv4294967295 32) (_ bv0 32)) ((_ extract 31 0) x12)) (concat (ite (= ((_ extract 31 31) ((_ extract 31 0) x7)) (_ bv1 1)) (_ bv4294967295 32) (_ bv0 32)) ((_ extract 31 0) x7))) (bvmul ((_ sign_extend 32) ((_ extract 31 0) x12)) ((_ sign_extend 32) ((_ extract 31 0) x7))))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, ["unsat"]);
    let text = exec.get_proof();
    assert!(text.contains(":rule cong"), "{text}");
    assert!(!text.contains(":rule hole"), "{text}");
    assert!(!text.contains(":rule trust"), "{text}");
    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    let quality = ay_proof::check_proof_strict(proof, &exec.ctx.terms)
        .expect("the SMULL collapse certificate must pass strict replay");
    assert_eq!(quality.trust_count, 0);
    assert_eq!(quality.hole_count, 0);
}

/// An arithmetic identity is not a general leaf. `7x + 21 = 7(x + 3)` at 64
/// bits (external-codegen row 1100) has different heads at the root, but handing it to
/// the bit-blast recognizer means refuting a constant-multiplier miter; the
/// walker must decline at once and leave it to the polynomial lanes the
/// collapse promotion tries next.
#[test]
fn congruence_walker_leaves_arithmetic_identities_to_the_polynomial_lanes() {
    let mut terms = TermStore::new();
    let sort = Sort::bitvec(64);
    let x = terms.mk_var("x", sort.clone());
    let seven = terms.mk_bitvec(BigInt::from(7), 64);
    let three = terms.mk_bitvec(BigInt::from(3), 64);
    let twenty_one = terms.mk_bitvec(BigInt::from(21), 64);
    let scaled = terms.mk_app(Symbol::named("bvmul"), [seven, x], sort.clone());
    let left = terms.mk_app(Symbol::named("bvadd"), [twenty_one, scaled], sort.clone());
    let shifted = terms.mk_app(Symbol::named("bvadd"), [three, x], sort.clone());
    let right = terms.mk_app(Symbol::named("bvmul"), [seven, shifted], sort);

    let mut proof = Proof::new();
    assert!(add_bvand_commutative_congruence_proof(&mut terms, &mut proof, left, right).is_none());
    assert!(proof.steps.is_empty(), "failed candidates must roll back");
}
