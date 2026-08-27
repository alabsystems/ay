// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[test]
fn test_qf_bv_idempotent_collapse_is_strict_checkable() {
    // `(not (= (bvand x x) x))` is the negation of a small-width BV tautology, so
    // the term builder folds `bvand x x → x` and the whole assertion collapses to
    // `false`, degenerating the proof to a single empty-clause `trust` step.
    // `promote_bv_identity_collapse` reconstructs assume + a `BvBitBlast` lemma
    // (re-validated by exhaustive bounded evaluation over the 16 values of a
    // 4-bit x) + resolution — trust-free.
    // The faithful recursive builder closes a range of small-width BV identities:
    // idempotence, self-cancellation to a constant, nested ops, and the
    // width-changing ops (extract / concat / repeat / extend).
    let cases = [
        // (proof needle, assertion body) — Alethe may normalize literal spellings.
        ("bvand", "(not (= (bvand x x) x))"),
        ("bvor", "(not (= (bvor x x) x))"),
        ("bvxor", "(not (= (bvxor x x) #x0))"),
        ("#b0000", "(not (= (bvand x (_ bv0 4)) (_ bv0 4)))"),
        ("bvnot", "(not (= (bvnot (bvnot x)) x))"),
        ("extract", "(not (= ((_ extract 3 0) x) x))"),
        ("repeat", "(not (= ((_ repeat 1) x) x))"),
        (
            "concat",
            "(not (= (concat ((_ extract 3 2) x) ((_ extract 1 0) x)) x))",
        ),
        ("zero_extend", "(not (= ((_ zero_extend 0) x) x))"),
    ];
    for (proof_needle, body) in cases {
        let input = format!(
            r#"
            (set-option :produce-proofs true)
            (set-logic QF_BV)
            (declare-const x (_ BitVec 4))
            (assert {body})
            (check-sat)
        "#
        );
        let commands = parse(&input).unwrap();
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).unwrap();
        assert_eq!(outputs, vec!["unsat"], "{body} must be UNSAT");
        let text = exec.get_proof();
        assert!(
            !text.contains(":rule trust"),
            "{body} collapse must not fall back to trust; got:\n{text}"
        );
        assert!(
            text.contains(proof_needle),
            "reconstructed proof should carry `{proof_needle}`; got:\n{text}"
        );
        let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
        match ay_proof::check_proof_strict(proof, &exec.ctx.terms) {
            Ok(quality) => assert_eq!(
                quality.trust_count, 0,
                "strict: zero trust steps for {body}"
            ),
            Err(e) => panic!("{body} proof must pass strict check, got {e:?}"),
        }
    }
}

/// SOUNDNESS FLOOR for the `bvand x 0` absorbing-element collapse promotion.
///
/// `test_qf_bv_idempotent_collapse_is_strict_checkable` proves the TRUE tautology
/// `(= (bvand x (_ bv0 4)) (_ bv0 4))` is promoted to a strict-checkable
/// `BvBitBlast` lemma rather than an unchecked hole. That promotion is only sound
/// because the classifier's `recognize_bv_bitblast` gate and the strict checker's
/// `validate_bv_bitblast` both RE-DERIVE the conflict semantically instead of
/// trusting the clause's shape. Corrupt the constant so the "conflict" is FALSE —
/// `(bvand x 0) = 1` holds for no 4-bit `x` — and pin both halves of that gate:
///   1. the classifier must NOT recognize the corrupted equality (so no promoter
///      could ever anchor a `BvBitBlast` lemma on it), and
///   2. a hand-forged `BvBitBlast` lemma over it must be REJECTED by the strict
///      checker with `InvalidTheoryLemma`, never mistaken for a real refutation.
/// A wrong `unsat` is catastrophic; an honest hole is safe. This guards the exact
/// recognize/validate boundary the absorbing-element promotion leans on.
#[test]
fn bvand_zero_corrupted_conflict_is_neither_recognized_nor_strict_checkable() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_var("bvand-zero-x", Sort::bitvec(4));
    let zero = exec.ctx.terms.mk_bitvec(BigInt::from(0), 4);
    let one = exec.ctx.terms.mk_bitvec(BigInt::from(1), 4);

    // RAW `(bvand x #b0000)`: `mk_app` interns the application WITHOUT the
    // `mk_bvand` absorbing fold (`x & 0 -> 0`), exactly as the faithful collapse
    // rebuild (`build_bv_pterm`) constructs it before promotion.
    let bvand_x_zero =
        exec.ctx
            .terms
            .mk_app(Symbol::named("bvand"), vec![x, zero], Sort::bitvec(4));
    assert!(
        matches!(
            exec.ctx.terms.get(bvand_x_zero),
            TermData::App(sym, args)
                if sym.name() == "bvand" && args.as_slice() == [x, zero]
        ),
        "fixture must hold the RAW bvand application, not the folded zero constant"
    );

    // Control: the genuine absorbing-element tautology `(bvand x 0) = 0` IS a
    // bit-blast tautology and must be recognized (this is what the promoter anchors).
    let honest_eq = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![bvand_x_zero, zero], Sort::Bool);
    assert!(
        ay_proof::recognize_bv_bitblast(&exec.ctx.terms, &[honest_eq]),
        "the true absorbing-element tautology must be recognized as a bit-blast lemma"
    );

    // Mutation: `(bvand x 0) = 1` is FALSE for every x, so it is NOT a bit-blast
    // tautology and must NOT be recognized (no promoter may anchor a lemma on it).
    let corrupted_eq =
        exec.ctx
            .terms
            .mk_app(Symbol::named("="), vec![bvand_x_zero, one], Sort::Bool);
    assert!(
        !ay_proof::recognize_bv_bitblast(&exec.ctx.terms, &[corrupted_eq]),
        "a FALSE BV equality must never be classified as a bit-blast tautology"
    );

    // A hand-forged refutation anchoring a `BvBitBlast` lemma on the corrupted
    // equality must be REJECTED by the strict checker at the theory-lemma boundary
    // (the checker re-derives the conflict and finds the clause falsifiable). With
    // no problem scope, assumption authority is not consulted, so the rejection is
    // the lemma itself, not the assume.
    let not_corrupted = exec.ctx.terms.mk_not_raw(corrupted_eq);
    let mut forged = Proof::new();
    let lemma_id =
        forged.add_theory_lemma_with_kind("bv", vec![corrupted_eq], TheoryLemmaKind::BvBitBlast);
    let assume_id = forged.add_assume(not_corrupted, None);
    forged.add_resolution(Vec::new(), corrupted_eq, lemma_id, assume_id);
    assert!(
        matches!(
            ay_proof::check_proof_strict(&forged, &exec.ctx.terms),
            Err(ay_proof::ProofCheckError::InvalidTheoryLemma { .. })
        ),
        "the strict checker must reject a forged BvBitBlast lemma over a false conflict; \
         got {:?}",
        ay_proof::check_proof_strict(&forged, &exec.ctx.terms)
    );
}

#[test]
fn test_qf_bv_zero_test_duality_is_strict_checkable() {
    // The DivZero/NullIfZero guard-carrier shape after the guards were
    // re-phrased over `bvult`: the intended trap set is `(bvult lhs 1)` while
    // the emitted x86 `E` condition tests `(= (bvand lhs lhs) 0)`. The
    // zero-test duality leaf + the `format_bv_ult_one_zero_equiv` printer
    // lowering must produce a hole-free pseudo-Boolean derivation.
    let cases = [
        // pure form
        "(not (= (bvult x (_ bv1 4)) (= x (_ bv0 4))))",
        // idempotent-gate form (the real guard-carrier obligation)
        "(not (= (ite (bvult x (_ bv1 4)) (_ bv1 1) (_ bv0 1)) (ite (= (bvand x x) (_ bv0 4)) (_ bv1 1) (_ bv0 1))))",
    ];
    let wide_cases = [
        // the SAME obligation at the production width, where no small-width
        // tautology fold applies and the proof enters reconstruction
        // structurally
        "(not (= (ite (bvult y (_ bv1 32)) (_ bv1 1) (_ bv0 1)) (ite (= (bvand y y) (_ bv0 32)) (_ bv1 1) (_ bv0 1))))",
    ];
    for (body, decl) in cases
        .iter()
        .map(|b| (*b, "(declare-const x (_ BitVec 4))"))
        .chain(wide_cases.iter().map(|b| (*b, "(declare-const y (_ BitVec 32))")))
    {
        let input = format!(
            r#"
            (set-option :produce-proofs true)
            (set-logic QF_BV)
            {decl}
            (assert {body})
            (check-sat)
        "#
        );
        let commands = parse(&input).unwrap();
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).unwrap();
        assert_eq!(outputs, vec!["unsat"], "{body} must be UNSAT");
        let text = exec.get_proof();
        assert!(
            !text.contains(":rule hole") && !text.contains(":rule trust"),
            "{body} must lower hole-free; got:\n{text}"
        );
        assert!(
            text.contains("pbblast_bvult") && text.contains("la_disequality"),
            "{body} must use the pseudo-Boolean zero-test template; got:\n{text}"
        );
    }
}
