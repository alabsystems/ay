// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[test]
fn test_scoped_reincarnated_dt_selector_projection_collapse_is_strict_checkable() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_DT)
        (push 1)
        (declare-datatypes ((ScopedPair 0)) (((scoped-mk (scoped-fst Int) (scoped-snd Int)))))
        (pop 1)
        (declare-datatypes ((ScopedPair 0)) (((scoped-mk (scoped-fst Int) (scoped-snd Int)))))
        (declare-const scoped-a Int)
        (declare-const scoped-b Int)
        (assert (not (= (scoped-fst (scoped-mk scoped-a scoped-b)) scoped-a)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
    let text = exec.get_proof();
    assert!(
        !text.contains(":rule trust"),
        "private member identities must retain trust-free reconstruction:\n{text}"
    );
    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    match exec.check_proof_strict_with_datatypes(proof) {
        Ok(quality) => assert_eq!(quality.trust_count, 0, "strict: zero trust steps"),
        Err(error) => panic!(
            "scoped datatype selector-projection proof must pass strict check, got {error:?}"
        ),
    }
}

#[test]
fn test_qf_dt_exhaustiveness_emits_firewall_lean() {
    // bench `qf_dt/v2l60078.cvc.smt2` core conflict: over `list` (cons|null),
    // `(not ((_ is cons) (cdr x4)))` AND `(cdr x4) != null` — a value that is
    // neither constructor of a 2-constructor datatype. End-to-end through QF_DT.
    let input = r#"(set-option :produce-proofs true)(set-logic QF_DT)
        (declare-datatypes ((nat 0)(list 0)(tree 0)) (((succ (pred nat)) (zero))
        ((cons (car tree) (cdr list)) (null))
        ((node (children list)) (leaf (data nat)))))
        (declare-fun x2 () nat)(declare-fun x3 () list)(declare-fun x4 () list)
        (declare-fun x5 () tree)(declare-fun x6 () tree)
        (assert (and (and (and (and (and (= (node x3) x5) (not ((_ is cons) (cdr x4)))) ((_ is node) x6)) ((_ is cons) (cons (leaf (pred x2)) x4))) (not (= null (cdr x4)))) (not ((_ is succ) zero))))
        (check-sat)"#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert_eq!(exec.execute_all(&commands).unwrap(), vec!["unsat"]);
    let fw = emit_firewall_lean(&exec, exec.last_proof.as_ref().unwrap());
    let f = fw
        .iter()
        .find(|f| f.contains("DtExhaust_"))
        .expect("expected a DtExhaust firewall file");
    assert!(f.contains("firewall_combined_unsat"));
    assert!(f.contains("| k0 | k1"));
}

#[test]
fn test_qf_dt_selector_over_matching_ctor_emits_firewall_lean() {
    // bench `datatype_simple.smt2`: `x = Some(0x2a)` with `value(x) ≠ 0x2a` is the
    // selector-over-matching-constructor collapse. The proof-step `DtSel`
    // projection emitter does NOT fire here (the residual routes through a
    // BV-constant compare), so the from-parsed `DtSelCtor` emitter reconstructs it.
    let input = r#"(set-option :produce-proofs true)(set-logic QF_DT)
        (declare-datatype Option_bv64 ((None_Option_bv64) (Some_Option_bv64 (value (_ BitVec 64)))))
        (declare-fun x () Option_bv64)
        (assert (= x (Some_Option_bv64 #x000000000000002a)))
        (assert (not (= (value x) #x000000000000002a)))(check-sat)"#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert_eq!(exec.execute_all(&commands).unwrap(), vec!["unsat"]);
    let fw = emit_firewall_lean(&exec, exec.last_proof.as_ref().unwrap());
    let f = fw
        .iter()
        .find(|f| f.contains("DtSelCtor_"))
        .expect("expected a DtSelCtor selector-over-constructor firewall file");
    assert!(f.contains("firewall_combined_unsat"));
    assert!(f.contains("def sel : D -> Int"));
}

/// Schema reconstruction is attempted for every completed refutation.
///
/// The individual promoters independently recognize the exact authored
/// theorem and strict-check their replacement before committing it. Their
/// common gate therefore only needs to establish that the existing proof
/// derives the empty clause; limiting it to historical collapse shapes would
/// miss valid reconstruction opportunities as proof production evolves.
#[test]
fn schema_collapse_reconstruction_gate_tracks_completed_refutations() {
    let mut exec = Executor::new();
    let false_t = exec.ctx.terms.false_term();
    let not_false = exec.ctx.terms.mk_not_raw(false_t);

    // The measured shape: assume the folded `false`, the `(not false)` wiring
    // lemma, and the resolution that closes them.
    let mut collapsed = Proof::new();
    let assume_id = collapsed.add_assume(false_t, None);
    let lemma_id = collapsed.add_theory_lemma_with_kind(
        "Bool",
        vec![not_false],
        TheoryLemmaKind::BoolTautology,
    );
    collapsed.add_resolution(vec![], false_t, assume_id, lemma_id);
    assert!(
        Executor::proof_needs_schema_collapse_reconstruction(&collapsed),
        "the false-constant collapse is a completed refutation"
    );

    // A content-bearing proof is also eligible: a mismatched promoter leaves it
    // untouched, while a matching promoter may replace it with a stricter
    // authored proof.
    let p = exec.ctx.terms.mk_var("shape3-p", Sort::Bool);
    let not_p = exec.ctx.terms.mk_not_raw(p);
    let mut real = Proof::new();
    let a = real.add_assume(p, None);
    let l = real.add_theory_lemma_with_kind("Bool", vec![not_p], TheoryLemmaKind::BoolTautology);
    real.add_resolution(vec![], p, a, l);
    assert!(
        Executor::proof_needs_schema_collapse_reconstruction(&real),
        "every completed refutation is eligible for an independently checked reconstruction"
    );

    // Extra proof content does not change eligibility when the empty clause is
    // still derived.
    let mut extra = Proof::new();
    let assume_id = extra.add_assume(false_t, None);
    let lemma_id =
        extra.add_theory_lemma_with_kind("Bool", vec![not_false], TheoryLemmaKind::BoolTautology);
    extra.add_theory_lemma_with_kind("Bool", vec![p], TheoryLemmaKind::BoolTautology);
    extra.add_resolution(vec![], false_t, assume_id, lemma_id);
    assert!(
        Executor::proof_needs_schema_collapse_reconstruction(&extra),
        "a completed proof with additional content remains eligible"
    );

    let mut incomplete = Proof::new();
    incomplete.add_assume(p, None);
    assert!(
        !Executor::proof_needs_schema_collapse_reconstruction(&incomplete),
        "an incomplete proof must not trigger reconstruction"
    );
}

#[test]
fn test_qf_ite_same_collapse_is_strict_checkable() {
    // `(not (= (ite p a a) a))` — an if-then-else with identical branches folds to
    // `false` during elaboration (the builder reduces `(ite p a a) → a`),
    // degenerating the proof to a single empty-clause `trust` step.
    // `promote_ite_same_collapse` reconstructs assume + an `IteSame` lemma (built
    // with the raw `mk_ite_raw` so the `ite` survives) + resolution — trust-free.
    // Exercised over an Int branch and a Bool branch (the axiom is sort-agnostic).
    for (sort, decl) in [
        ("Int", "(declare-const a Int)"),
        ("Bool", "(declare-const a Bool)"),
    ] {
        let input = format!(
            r#"
            (set-option :produce-proofs true)
            (set-logic QF_UF)
            (declare-const p Bool)
            {decl}
            (assert (not (= (ite p a a) a)))
            (check-sat)
        "#
        );
        let commands = parse(&input).unwrap();
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).unwrap();
        assert_eq!(outputs, vec!["unsat"], "ite-same over {sort} must be UNSAT");
        let text = exec.get_proof();
        assert!(
            !text.contains(":rule trust"),
            "ite-same collapse ({sort}) must not fall back to trust; got:\n{text}"
        );
        assert!(
            text.contains("ite"),
            "reconstructed proof should carry the raw `ite` term ({sort}); got:\n{text}"
        );
        let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
        match ay_proof::check_proof_strict(proof, &exec.ctx.terms) {
            Ok(quality) => assert_eq!(quality.trust_count, 0, "strict: zero trust steps ({sort})"),
            Err(e) => panic!("ite-same proof ({sort}) must pass strict check, got {e:?}"),
        }
    }
}

#[test]
fn test_qf_bool_tautology_collapse_is_strict_checkable() {
    // Propositional contradictions — the negation of a Boolean tautology, or a
    // directly-false Boolean equality — fold to `false` during elaboration,
    // degenerating the proof to a single empty-clause `trust` step.
    // `promote_bool_tautology_collapse` reconstructs assume(A) + a `BoolTautology`
    // lemma `(not A)` (re-validated by exhaustive bounded evaluation over the
    // Bool variables) + resolution — trust-free.
    for body in [
        "(not (= (not (not p)) p))",               // double-negation elimination
        "(not (= (and p p) p))",                   // idempotence of and
        "(not (= (or p (not p)) (or q (not q))))", // excluded middle, both sides
        "(= p (not p))",                           // directly-false equality
    ] {
        let input = format!(
            r#"
            (set-option :produce-proofs true)
            (set-logic QF_UF)
            (declare-const p Bool)
            (declare-const q Bool)
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

#[test]
fn test_qf_nia_linear_identity_collapse_is_strict_checkable() {
    // `(not (= (* x 0) 0))` and `(not (= (* x 1) x))` are negations of linear-
    // arithmetic tautologies, so the term builder folds them and the whole
    // assertion collapses to `false`, degenerating the proof to a single
    // empty-clause `trust` step. `promote_nia_linear_identity_collapse`
    // reconstructs assume + a `LiaGeneric`/`LinearIdentity` lemma (re-validated
    // by `L - R ≡ 0`) + resolution — trust-free.
    for body in ["(not (= (* x 0) 0))", "(not (= (* x 1) x))"] {
        let input = format!(
            r#"
            (set-option :produce-proofs true)
            (set-logic QF_NIA)
            (declare-const x Int)
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

#[test]
fn test_match_eq_negation_shapes() {
    use super::match_eq_negation;
    use ay_frontend::command::Term as PT;
    let sym = |s: &str| PT::Symbol(s.to_string());
    let bvand_xx = || PT::App("bvand".into(), vec![sym("x"), sym("x")]);
    // (not (= (bvand x x) x)) → the two equality sides.
    let neg = PT::App(
        "not".into(),
        vec![PT::App("=".into(), vec![bvand_xx(), sym("x")])],
    );
    let got = match_eq_negation(&neg).expect("negated equality must match");
    assert_eq!(got.0, &bvand_xx());
    assert_eq!(got.1, &sym("x"));
    // Reject the positive (non-negated) equality.
    assert!(match_eq_negation(&PT::App("=".into(), vec![bvand_xx(), sym("x")])).is_none());
    // Reject a non-equality negation.
    assert!(match_eq_negation(&PT::App("not".into(), vec![sym("p")])).is_none());
}

#[test]
fn test_match_row1_negation_accepts_canonical_and_rejects_near_misses() {
    use super::match_row1_negation;
    use ay_frontend::command::Term as PT;
    let sym = |s: &str| PT::Symbol(s.to_string());
    let row1 = |store_idx: &str, sel_idx: &str, store_val: &str, cmp_val: &str| {
        PT::App(
            "not".into(),
            vec![PT::App(
                "=".into(),
                vec![
                    PT::App(
                        "select".into(),
                        vec![
                            PT::App(
                                "store".into(),
                                vec![sym("a"), sym(store_idx), sym(store_val)],
                            ),
                            sym(sel_idx),
                        ],
                    ),
                    sym(cmp_val),
                ],
            )],
        )
    };
    // Canonical: store index == select index, stored value == compared value.
    assert_eq!(
        match_row1_negation(&row1("i", "i", "e", "e")),
        Some(("a", "i", "e"))
    );
    // Near-miss: store index != select index (this is SAT, must NOT be promoted).
    assert_eq!(match_row1_negation(&row1("i", "j", "e", "e")), None);
    // Near-miss: stored value != compared value (also SAT).
    assert_eq!(match_row1_negation(&row1("i", "i", "e", "d")), None);
    // Reject the positive (non-negated) equality — that is `true`, not refutable.
    let positive = PT::App(
        "=".into(),
        vec![
            PT::App(
                "select".into(),
                vec![
                    PT::App("store".into(), vec![sym("a"), sym("i"), sym("e")]),
                    sym("i"),
                ],
            ),
            sym("e"),
        ],
    );
    assert_eq!(match_row1_negation(&positive), None);
    // Select on the RIGHT side of the equality is still accepted.
    let flipped = PT::App(
        "not".into(),
        vec![PT::App(
            "=".into(),
            vec![
                sym("e"),
                PT::App(
                    "select".into(),
                    vec![
                        PT::App("store".into(), vec![sym("a"), sym("i"), sym("e")]),
                        sym("i"),
                    ],
                ),
            ],
        )],
    );
    assert_eq!(match_row1_negation(&flipped), Some(("a", "i", "e")));
}

#[test]
fn test_nia_integer_divisibility_conflict_is_trust_free_and_strict_checkable() {
    // `2y = 7` is rationally satisfiable (y = 3.5) but integer-infeasible
    // (gcd 2 ∤ 7). In a nonlinear context the live classifier emits it as
    // `Generic`/trust; `promote_lia_divisibility_lemmas` promotes it to a
    // strict-checkable `LiaGeneric` + `Divisibility` lemma. The dummy nonlinear
    // `(* z z) >= 0` keeps the problem on the QF_NIA path. This must (1) be UNSAT,
    // (2) carry NO trust step, and (3) PASS STRICT CHECK (genuinely checkable —
    // not merely relabelled), i.e. `trust_count == 0` with a real certificate.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_NIA)
        (declare-const y Int)
        (declare-const z Int)
        (assert (= (* 2 y) 7))
        (assert (>= (* z z) 0))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    let kinds: Vec<_> = proof
        .steps
        .iter()
        .filter_map(|s| match s {
            ProofStep::TheoryLemma { kind, .. } => Some(*kind),
            _ => None,
        })
        .collect();
    assert!(
        kinds.contains(&TheoryLemmaKind::LiaGeneric),
        "integer conflict should be promoted to LiaGeneric; got {kinds:?}"
    );
    assert!(
        !kinds.contains(&TheoryLemmaKind::Generic),
        "no Generic/trust theory lemma should remain; got {kinds:?}"
    );
    assert!(
        !exec.get_proof().contains(":rule trust"),
        "proof must not fall back to trust"
    );
    // STRICT: the promoted Divisibility certificate is re-validated by the checker
    // (not just relabelled) — a genuine, non-gaming reduction.
    match ay_proof::check_proof_strict(proof, &exec.ctx.terms) {
        Ok(quality) => assert_eq!(quality.trust_count, 0, "strict: zero trust steps"),
        Err(e) => panic!("promoted Divisibility proof must pass strict check, got {e:?}"),
    }
}
