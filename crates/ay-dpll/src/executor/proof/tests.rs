// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{AletheRule, ProofId, Sort};
use ay_frontend::parse;
use ay_proof::check_proof_partial;
use num_bigint::BigInt;

fn emit_firewall_lean(exec: &Executor, proof: &Proof) -> Vec<String> {
    exec.emit_datatype_firewall_lean_bounded(proof, usize::MAX, usize::MAX)
        .expect("test fixture must fit in the address-space bounds")
}

#[test]
fn contextual_row2_unit_is_rebuilt_as_guarded_strict_proof() {
    let mut exec = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = exec.ctx.terms.mk_var("a", array_sort);
    let i = exec.ctx.terms.mk_var("i", Sort::Int);
    let j = exec.ctx.terms.mk_var("j", Sort::Int);
    let v = exec.ctx.terms.mk_var("v", Sort::Int);
    let store = exec.ctx.terms.mk_store(a, i, v);
    let store_read = exec.ctx.terms.mk_select(store, j);
    let base_read = exec.ctx.terms.mk_select(a, j);
    let row_eq = exec.ctx.terms.mk_eq(store_read, base_read);
    let not_row_eq = exec.ctx.terms.mk_not(row_eq);
    let index_eq = exec.ctx.terms.mk_eq(i, j);
    let not_index_eq = exec.ctx.terms.mk_not(index_eq);
    exec.ctx.assertions = vec![not_index_eq, not_row_eq];

    // Exact pruned shape formerly published by the eager array lane: the unit
    // equality is only contextually valid and therefore remains Generic/trust.
    let mut proof = Proof::new();
    let trust = proof.add_theory_lemma("array", vec![row_eq]);
    let row_assume = proof.add_assume(not_row_eq, None);
    proof.add_resolution(Vec::new(), row_eq, row_assume, trust);

    exec.promote_contextual_array_row2_lemmas(&mut proof);

    assert_eq!(proof.steps.len(), 5);
    assert_eq!(
        proof
            .steps
            .iter()
            .filter(|step| matches!(step, ProofStep::Assume(_)))
            .count(),
        2
    );
    assert!(proof.steps.iter().any(|step| {
        matches!(
            step,
            ProofStep::TheoryLemma {
                clause,
                kind: TheoryLemmaKind::ArraySelectStore { index_eq: false },
                ..
            } if clause.as_slice() == [index_eq, row_eq]
        )
    }));
    assert!(proof
        .steps
        .iter()
        .all(|step| !matches!(step, ProofStep::TheoryLemma { kind, .. } if kind.is_trust())));
    ay_proof::check_proof_strict(&proof, &exec.ctx.terms)
        .expect("rebuilt contextual ROW2 proof must pass strict checking");
}

#[test]
fn contextual_row2_repair_skips_unowned_candidate_and_uses_later_owned_unit() {
    let mut exec = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);

    let a0 = exec.ctx.terms.mk_var("a0", array_sort.clone());
    let i0 = exec.ctx.terms.mk_var("i0", Sort::Int);
    let j0 = exec.ctx.terms.mk_var("j0", Sort::Int);
    let v0 = exec.ctx.terms.mk_var("v0", Sort::Int);
    let store0 = exec.ctx.terms.mk_store(a0, i0, v0);
    let store_read0 = exec.ctx.terms.mk_select(store0, j0);
    let base_read0 = exec.ctx.terms.mk_select(a0, j0);
    let unowned_row_eq = exec.ctx.terms.mk_eq(store_read0, base_read0);

    let a1 = exec.ctx.terms.mk_var("a1", array_sort);
    let i1 = exec.ctx.terms.mk_var("i1", Sort::Int);
    let j1 = exec.ctx.terms.mk_var("j1", Sort::Int);
    let v1 = exec.ctx.terms.mk_var("v1", Sort::Int);
    let store1 = exec.ctx.terms.mk_store(a1, i1, v1);
    let store_read1 = exec.ctx.terms.mk_select(store1, j1);
    let base_read1 = exec.ctx.terms.mk_select(a1, j1);
    let owned_row_eq = exec.ctx.terms.mk_eq(store_read1, base_read1);
    let not_owned_row_eq = exec.ctx.terms.mk_not(owned_row_eq);
    let owned_index_eq = exec.ctx.terms.mk_eq(i1, j1);
    let not_owned_index_eq = exec.ctx.terms.mk_not(owned_index_eq);
    exec.ctx.assertions = vec![not_owned_index_eq, not_owned_row_eq];

    let mut proof = Proof::new();
    proof.add_theory_lemma("array", vec![unowned_row_eq]);
    proof.add_theory_lemma("array", vec![owned_row_eq]);

    exec.promote_contextual_array_row2_lemmas(&mut proof);

    assert!(proof.steps.iter().any(|step| {
        matches!(
            step,
            ProofStep::TheoryLemma {
                clause,
                kind: TheoryLemmaKind::ArraySelectStore { index_eq: false },
                ..
            } if clause.as_slice() == [owned_index_eq, owned_row_eq]
        )
    }));
    ay_proof::check_proof_strict(&proof, &exec.ctx.terms)
        .expect("a later contextual unit with owned roots must be repaired");
}

#[test]
fn contextual_row2_repair_accepts_owned_check_sat_assuming_roots() {
    let mut exec = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = exec.ctx.terms.mk_var("a", array_sort);
    let i = exec.ctx.terms.mk_var("i", Sort::Int);
    let j = exec.ctx.terms.mk_var("j", Sort::Int);
    let v = exec.ctx.terms.mk_var("v", Sort::Int);
    let store = exec.ctx.terms.mk_store(a, i, v);
    let store_read = exec.ctx.terms.mk_select(store, j);
    let base_read = exec.ctx.terms.mk_select(a, j);
    let row_eq = exec.ctx.terms.mk_eq(store_read, base_read);
    let not_row_eq = exec.ctx.terms.mk_not(row_eq);
    let index_eq = exec.ctx.terms.mk_eq(i, j);
    let not_index_eq = exec.ctx.terms.mk_not(index_eq);
    exec.last_assumptions = Some(vec![not_index_eq, not_row_eq]);

    let mut proof = Proof::new();
    proof.add_theory_lemma("array", vec![row_eq]);

    exec.promote_contextual_array_row2_lemmas(&mut proof);

    assert_eq!(
        proof
            .steps
            .iter()
            .filter(|step| matches!(step, ProofStep::Assume(_)))
            .count(),
        2
    );
    ay_proof::check_proof_strict(&proof, &exec.ctx.terms)
        .expect("active check-sat-assuming roots are legitimate ROW2 proof inputs");
}

#[test]
fn shadowed_store_generic_lemma_expands_to_strict_primitives() {
    let mut exec = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = exec.ctx.terms.mk_var("a", array_sort);
    let i = exec.ctx.terms.mk_var("i", Sort::Int);
    let j = exec.ctx.terms.mk_var("j", Sort::Int);
    let v = exec.ctx.terms.mk_var("v", Sort::Int);
    let w = exec.ctx.terms.mk_var("w", Sort::Int);
    let x = exec.ctx.terms.mk_var("x", Sort::Int);

    let lhs_inner = exec.ctx.terms.mk_store(a, i, v);
    let rhs_inner = exec.ctx.terms.mk_store(a, i, w);
    let lhs = exec.ctx.terms.mk_store(lhs_inner, j, x);
    let rhs = exec.ctx.terms.mk_store(rhs_inner, j, x);
    let array_eq = exec.ctx.terms.mk_eq(lhs, rhs);
    let not_array_eq = exec.ctx.terms.mk_not(array_eq);
    let index_eq = exec.ctx.terms.mk_eq(i, j);
    let value_eq = exec.ctx.terms.mk_eq(v, w);
    let compact = exec.ctx.terms.mk_or(vec![not_array_eq, index_eq, value_eq]);
    let not_compact = exec.ctx.terms.mk_not_raw(compact);

    let mut proof = Proof::new();
    let lemma = proof.add_theory_lemma("array", vec![compact]);
    // Keep the named assumption after the expanded lemma so proof surgery must
    // remap the public name→ProofId index, not merely the inference premises.
    let assumption = proof.add_assume(not_compact, Some("shadowed_input".to_string()));
    proof.add_rule_step(
        AletheRule::ThResolution,
        Vec::new(),
        vec![lemma, assumption],
        Vec::new(),
    );
    exec.split_shadowed_store_equality_lemmas(&mut proof);

    let named = proof
        .named_steps
        .get("shadowed_input")
        .expect("named assumption must survive proof-id remapping");
    assert!(matches!(
        proof.steps.get(named.0 as usize),
        Some(ProofStep::Assume(term)) if *term == not_compact
    ));

    assert!(proof
        .steps
        .iter()
        .all(|step| { !matches!(step, ProofStep::TheoryLemma { kind, .. } if kind.is_trust()) }));
    assert!(proof.steps.iter().any(|step| {
        matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::ArraySelectStore { index_eq: true },
                ..
            }
        )
    }));
    assert!(proof.steps.iter().any(|step| {
        matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::ArraySelectStore { index_eq: false },
                ..
            }
        )
    }));
    assert!(proof.steps.iter().any(|step| {
        matches!(step, ProofStep::Step { clause, .. } if clause.as_slice() == [compact])
    }));
    assert!(matches!(
        proof.steps.last(),
        Some(ProofStep::Step { clause, .. }) if clause.is_empty()
    ));
    ay_proof::check_proof_strict(&proof, &exec.ctx.terms)
        .expect("expanded shadowed-store lemma must be strictly checkable");
}

#[test]
fn shadowed_store_expansion_handles_deduplicated_index_and_value_equality() {
    let mut exec = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = exec.ctx.terms.mk_var("a", array_sort);
    let i = exec.ctx.terms.mk_var("i", Sort::Int);
    let j = exec.ctx.terms.mk_var("j", Sort::Int);
    let x = exec.ctx.terms.mk_var("x", Sort::Int);

    // The inner values are i and j, so the index and value side conditions
    // are both the exact term `(= i j)`.  `mk_or` canonicalizes the compact
    // theorem to two disjuncts; proof surgery must not mistake that for a
    // malformed three-literal theorem and leave a trust step behind.
    let lhs_inner = exec.ctx.terms.mk_store(a, i, i);
    let rhs_inner = exec.ctx.terms.mk_store(a, i, j);
    let lhs = exec.ctx.terms.mk_store(lhs_inner, j, x);
    let rhs = exec.ctx.terms.mk_store(rhs_inner, j, x);
    let array_eq = exec.ctx.terms.mk_eq(lhs, rhs);
    let not_array_eq = exec.ctx.terms.mk_not(array_eq);
    let shared_eq = exec.ctx.terms.mk_eq(i, j);
    let compact = exec
        .ctx
        .terms
        .mk_or(vec![not_array_eq, shared_eq, shared_eq]);
    let TermData::App(_, compact_args) = exec.ctx.terms.get(compact) else {
        panic!("expected compact disjunction");
    };
    assert_eq!(compact_args.len(), 2, "duplicate side condition must fold");
    let not_compact = exec.ctx.terms.mk_not_raw(compact);

    let mut proof = Proof::new();
    let assumption = proof.add_assume(not_compact, None);
    let lemma = proof.add_theory_lemma("array", vec![compact]);
    proof.add_rule_step(
        AletheRule::ThResolution,
        Vec::new(),
        vec![lemma, assumption],
        Vec::new(),
    );
    exec.split_shadowed_store_equality_lemmas(&mut proof);

    assert!(proof
        .steps
        .iter()
        .all(|step| !matches!(step, ProofStep::TheoryLemma { kind, .. } if kind.is_trust())));
    assert!(matches!(
        proof.steps.last(),
        Some(ProofStep::Step { clause, .. }) if clause.is_empty()
    ));
    ay_proof::check_proof_strict(&proof, &exec.ctx.terms)
        .expect("deduplicated shadowed-store proof must be strictly checkable");
}

#[test]
fn test_get_proof_not_enabled() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 0))
        (assert (> x 0))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "unsat");
    assert!(outputs[1].contains("proof generation is not enabled"));
}

#[test]
fn test_get_proof_after_sat() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (> x 0))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    assert!(outputs[1].contains("proof is not available"));
}

#[test]
fn test_get_proof_after_unsat() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 0))
        (assert (> x 0))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "unsat");
    // Should get an actual proof (not an error)
    assert!(
        outputs[1].starts_with('('),
        "Expected proof output, got: {}",
        outputs[1]
    );
}

#[test]
fn test_clause_trace_to_lrat_bytes_rejects_noncontiguous_original_ids_8886() {
    let mut trace = ay_sat::ClauseTrace::new();
    trace.add_clause(
        2,
        vec![ay_sat::Literal::positive(ay_sat::Variable::new(0))],
        true,
    );
    trace.add_clause_with_hints(3, Vec::new(), false, vec![2]);

    assert!(
        clause_trace_to_lrat_bytes(&trace).is_none(),
        "standalone LRAT export must fail closed when original clause IDs do not match DIMACS order"
    );
}

#[test]
fn test_clause_trace_to_lrat_bytes_rejects_learned_id_collision_8886() {
    let mut trace = ay_sat::ClauseTrace::new();
    trace.add_clause(
        1,
        vec![ay_sat::Literal::positive(ay_sat::Variable::new(0))],
        true,
    );
    trace.add_clause_with_hints(1, Vec::new(), false, vec![1]);

    assert!(
        clause_trace_to_lrat_bytes(&trace).is_none(),
        "standalone LRAT export must fail closed when a learned clause reuses the original ID space"
    );
}

#[test]
fn test_qf_lia_check_sat_assuming_records_structured_split_loop_proof_6725() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (check-sat-assuming ((> x 1) (< x 0)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);

    let theory_proofs = exec
        .last_original_clause_theory_proofs
        .as_ref()
        .expect("split-loop UNSAT should retain original-clause theory proofs");
    let theory_kinds: Vec<_> = theory_proofs
        .iter()
        .map(|proof| proof.as_ref().map(|proof| proof.kind))
        .collect();
    let proof_step_kinds: Vec<_> = exec
        .last_proof
        .as_ref()
        .map(|proof| {
            proof
                .steps
                .iter()
                .filter_map(|step| match step {
                    ProofStep::TheoryLemma { kind, .. } => Some(*kind),
                    _ => None,
                })
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    assert!(
        theory_proofs.iter().flatten().any(|proof| {
            matches!(
                proof.kind,
                TheoryLemmaKind::LiaGeneric | TheoryLemmaKind::LraFarkas
            )
        }),
        "expected a structured arithmetic theory annotation in split-loop proof ledger, got ledger={theory_kinds:?}, proof={proof_step_kinds:?}"
    );

    let proof = exec.get_proof();
    assert!(
        !proof.contains(":rule trust"),
        "LIA check-sat-assuming proof must not fall back to trust; proof_kinds={proof_step_kinds:?}\n{proof}"
    );
}

#[test]
fn test_qf_lia_divisibility_lemma_is_strict_checkable() {
    // The DIRECT QF_LIA divisibility conflict `3x = 2` (gcd 3 ∤ 2) is emitted by the
    // LIA solver as `LiaGeneric` carrying only a rational Farkas `[1]` — so it has
    // `trust_count == 0` yet FAILS strict check (rational Farkas cannot eliminate the
    // variable). The Divisibility promotion attaches the integer annotation so it is
    // now GENUINELY strict-checkable.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= (* 3 x) 2))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    assert!(
        !exec.get_proof().contains(":rule trust"),
        "must not fall back to trust"
    );
    match ay_proof::check_proof_strict(proof, &exec.ctx.terms) {
        Ok(quality) => assert_eq!(quality.trust_count, 0, "strict: zero trust steps"),
        Err(e) => panic!("QF_LIA divisibility proof must pass strict check, got {e:?}"),
    }
}

#[test]
fn test_qf_lia_gomory_cut_is_strict_checkable() {
    // `3x ≤ 2 ∧ 3x ≥ 1` is UNSAT (no integer multiple of 3 in [1,2]) but RATIONALLY
    // feasible (x ∈ [1/3, 2/3]), so the LIA solver emits an `LraFarkas` lemma whose
    // rational certificate cannot eliminate the variable — `trust_count == 0` yet
    // strict-failing. The bounded-gcd (integer-cut) promotion attaches `Divisibility`
    // so it passes strict check.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (<= (* 3 x) 2))
        (assert (>= (* 3 x) 1))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    assert!(
        !exec.get_proof().contains(":rule trust"),
        "must not fall back to trust"
    );
    match ay_proof::check_proof_strict(proof, &exec.ctx.terms) {
        Ok(quality) => assert_eq!(quality.trust_count, 0, "strict: zero trust steps"),
        Err(e) => panic!("Gomory-cut proof must pass strict check, got {e:?}"),
    }
}

#[test]
fn test_qf_array_row1_collapse_is_strict_checkable() {
    // `(not (= (select (store a i e) i) e))` is the negation of the read-over-write
    // (ROW1) axiom instance, so the term builder folds `select(store(a,i,e),i) → e`
    // at elaboration time and the whole assertion collapses to `false`. The UNSAT
    // proof then degenerates to a SINGLE empty-clause `trust` step (the theory work
    // happened inside simplification, leaving no lemma). `promote_array_row_collapse`
    // reconstructs the refutation from the parsed assertion: an `assume` of the
    // original disequality, a strict-checkable `ArraySelectStore { index_eq: true }`
    // lemma, and a resolution to the empty clause — so it is now trust-free.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const e Int)
        (assert (not (= (select (store a i e) i) e)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    let text = exec.get_proof();
    assert!(
        !text.contains(":rule trust"),
        "array ROW1 collapse must not fall back to trust; got:\n{text}"
    );
    assert!(
        text.contains("read_over_write_pos"),
        "reconstructed proof should carry the ROW1 read-over-write lemma; got:\n{text}"
    );
    match ay_proof::check_proof_strict(proof, &exec.ctx.terms) {
        Ok(quality) => assert_eq!(quality.trust_count, 0, "strict: zero trust steps"),
        Err(e) => panic!("array ROW1 collapse proof must pass strict check, got {e:?}"),
    }
}

#[test]
fn test_qf_dt_selector_projection_collapse_is_strict_checkable() {
    // `(not (= (fst (mk a b)) a))` is the negation of the selector-projection
    // axiom instance, so the term builder folds `fst(mk a b) → a` at elaboration
    // and the whole assertion collapses to `false`. The UNSAT proof degenerates
    // to a SINGLE empty-clause `trust` step. `promote_dt_selector_collapse`
    // reconstructs the refutation from the parsed assertion: an `assume` of the
    // disequality, a strict-checkable `DatatypeSelectorProject` lemma, and a
    // resolution to the empty clause — trust-free, validated against the
    // constructor→selector registry.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_DT)
        (declare-datatypes ((Pair 0)) (((mk (fst Int) (snd Int)))))
        (declare-const a Int)
        (declare-const b Int)
        (assert (not (= (fst (mk a b)) a)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
    let text = exec.get_proof();
    assert!(
        !text.contains(":rule trust"),
        "DT selector-projection collapse must not fall back to trust; got:\n{text}"
    );
    assert!(
        text.contains("dt_project"),
        "reconstructed proof should carry the dt_project lemma; got:\n{text}"
    );
    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    // Validation requires the constructor→selector registry, so go through the
    // executor's datatype-aware strict checker rather than the bare one.
    match exec.check_proof_strict_with_datatypes(proof) {
        Ok(quality) => assert_eq!(quality.trust_count, 0, "strict: zero trust steps"),
        Err(e) => panic!("DT selector-projection proof must pass strict check, got {e:?}"),
    }
}

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
        // (op-keyword, assertion body) — each is the negation of a 4-bit tautology.
        ("bvand", "(not (= (bvand x x) x))"),
        ("bvor", "(not (= (bvor x x) x))"),
        ("bvxor", "(not (= (bvxor x x) #x0))"),
        ("bv0", "(not (= (bvand x (_ bv0 4)) (_ bv0 4)))"),
        ("bvnot", "(not (= (bvnot (bvnot x)) x))"),
        ("extract", "(not (= ((_ extract 3 0) x) x))"),
        ("repeat", "(not (= ((_ repeat 1) x) x))"),
        (
            "concat",
            "(not (= (concat ((_ extract 3 2) x) ((_ extract 1 0) x)) x))",
        ),
        ("zero_extend", "(not (= ((_ zero_extend 0) x) x))"),
    ];
    for (op, body) in cases {
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
            text.contains(op),
            "reconstructed proof should carry the raw `{op}` term (faithful); got:\n{text}"
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
fn qfbv_proof_rebuilder_accepts_structured_decimal_literal() {
    let mut terms = TermStore::new();
    let parsed = FrontendTerm::IndexedApp(
        "bv3".to_string(),
        vec![FrontendIndex::Numeral("4".to_string())],
        Vec::new(),
    );
    let rebuilt = build_qfbv_pterm(&mut terms, &parsed)
        .expect("structured decimal bitvector literal must rebuild");
    let expected = terms.mk_bitvec(BigInt::from(3), 4);
    assert_eq!(rebuilt, expected);
    assert_eq!(terms.sort(rebuilt), &Sort::bitvec(4));
    assert!(build_qfbv_pterm(&mut terms, &FrontendTerm::Symbol("(_ bv3 4)".to_string())).is_none());
}

#[test]
fn test_qf_nia_pin_substitution_is_strict_checkable() {
    // `(= (* x y) 7) ∧ (= x 2)`: pinning x=2 turns the nonlinear `x·y = 7` into the
    // integer-infeasible `2y = 7`. The elaborator folds the substituted product to
    // the canonical `(* y 2)` and emits the residual `(= 7 (* y 2))` as a single
    // `trust` Step (the divisibility lemma `2y≠7` is already strict-checkable).
    // `promote_nia_pin_substitution` reconstructs that trust step from the parsed
    // assertions via eq_reflexive + eq_congruent + a LinearIdentity commutativity
    // bridge + eq_transitive + a resolution chain — all existing strict-validated
    // rules, gated by a whole-proof check_proof_strict revert gate — so it is
    // trust-free.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_NIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= (* x y) 7))
        (assert (= x 2))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
    let text = exec.get_proof();
    assert!(
        !text.contains(":rule trust"),
        "NIA pin-substitution must not fall back to trust; got:\n{text}"
    );
    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    match ay_proof::check_proof_strict(proof, &exec.ctx.terms) {
        Ok(quality) => assert_eq!(quality.trust_count, 0, "strict: zero trust steps"),
        Err(e) => panic!("NIA pin-substitution proof must pass strict check, got {e:?}"),
    }
}

#[test]
fn test_qf_fp_classification_is_strict_checkable() {
    // Small-width FP classification / sign / structural-identity tautology
    // negations are UNSAT; the FP solver emits the identity lemma as a Generic
    // trust theory lemma. `promote_fp_classification_lemmas` re-tags it to the
    // strict-checkable `FpClassification` kind (exhaustive bounded exact-IEEE
    // evaluation) — trust-free.
    for body in [
        "(not (= (fp.abs (fp.abs x)) (fp.abs x)))", // abs idempotence
        "(not (= (fp.neg (fp.neg x)) x))",          // neg involution
        "(and (fp.isNaN x) (fp.isNormal x))",       // mutually exclusive
    ] {
        let input = format!(
            r#"
            (set-option :produce-proofs true)
            (set-logic QF_FP)
            (declare-const x (_ FloatingPoint 3 5))
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
            "{body} must not fall back to trust; got:\n{text}"
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
fn test_qf_bool_tautology_emits_firewall_lean() {
    let input = r#"(set-option :produce-proofs true)(set-logic QF_UF)(declare-const p Bool)(assert (not (= (not (not p)) p)))(check-sat)"#;
    let cmds = parse(input).unwrap();
    let mut ex = Executor::new();
    assert_eq!(ex.execute_all(&cmds).unwrap(), vec!["unsat"]);
    let proof = ex.last_proof.as_ref().unwrap();
    let fw = emit_firewall_lean(&ex, proof);
    assert_eq!(fw.len(), 1, "expected 1 Boolean firewall file");
    assert!(fw[0].contains("firewall_combined_unsat") && fw[0].contains("abbrev Val := Bool"));
    assert!(
        ex.emit_datatype_firewall_lean_bounded(proof, 0, usize::MAX)
            .is_none(),
        "file-count bound must reject before retaining an artifact"
    );
    assert!(
        ex.emit_datatype_firewall_lean_bounded(proof, 1, fw[0].len() - 1)
            .is_none(),
        "aggregate byte bound must reject an oversized artifact"
    );
    assert_eq!(
        ex.emit_datatype_firewall_lean_bounded(proof, 1, fw[0].len())
            .expect("exact bounds must accept"),
        fw
    );
}

#[test]
fn test_qf_ite_same_emits_firewall_lean() {
    // A real `(not (= (ite p a a) a))` conflict emits one `IteSame` Lean firewall
    // file grounding `(ite c x x) = x` in `firewall_combined_unsat` over
    // `Val = Int × Bool` (verified out-of-band to lake-build, axioms ⊆ kernel-3).
    let input = r#"(set-option :produce-proofs true)(set-logic QF_UF)(declare-const p Bool)(declare-const a Int)(assert (not (= (ite p a a) a)))(check-sat)"#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert_eq!(exec.execute_all(&commands).unwrap(), vec!["unsat"]);
    let fw = emit_firewall_lean(&exec, exec.last_proof.as_ref().unwrap());
    let ite = fw
        .iter()
        .find(|f| f.contains("IteSame"))
        .expect("expected an IteSame firewall file");
    assert!(ite.contains("firewall_combined_unsat"));
    assert!(ite.contains("abbrev Val := Int × Bool"));
    assert!(ite.contains("simp [ite_self]"));
}

#[test]
fn test_qf_fp_identity_emits_firewall_lean() {
    // FP sign-bit identities emit an `FpIdent` Lean firewall grounding the
    // identity over the `BitVec 5` carrier (`fp.abs`→clear sign, `fp.neg`→flip),
    // refuted by `decide` (verified out-of-band to lake-build, axioms ⊆ kernel-3).
    for (op, body) in [
        ("absBits", "(not (= (fp.abs (fp.abs x)) (fp.abs x)))"),
        ("negBits", "(not (= (fp.neg (fp.neg x)) x))"),
    ] {
        let input = format!(
            r#"(set-option :produce-proofs true)(set-logic QF_FP)(declare-const x (_ FloatingPoint 3 5))(assert {body})(check-sat)"#
        );
        let commands = parse(&input).unwrap();
        let mut exec = Executor::new();
        assert_eq!(exec.execute_all(&commands).unwrap(), vec!["unsat"]);
        let fw = emit_firewall_lean(&exec, exec.last_proof.as_ref().unwrap());
        let f = fw
            .iter()
            .find(|f| f.contains("FpIdent"))
            .unwrap_or_else(|| panic!("expected an FpIdent firewall for {body}"));
        assert!(f.contains("firewall_combined_unsat"));
        assert!(
            f.contains(op),
            "expected {op} in the FP firewall for {body}"
        );
    }
}

#[test]
fn test_closed_identity_classes_emit_firewall_lean() {
    // Every trust class closed via an all-variable IDENTITY lemma now also emits
    // a half-1 Lean firewall (verified out-of-band to lake-build, axioms ⊆
    // kernel-3): BV identity, NIA linear identity, and DT selector projection —
    // the three that the from-parsed emitters could not reach (no constant to
    // infer the model from), now handled per-lemma-kind with TermStore access.
    let cases = [
        ("QF_BV", "(declare-const x (_ BitVec 4))", "(not (= (bvand x x) x))", "Bv_"),
        ("QF_NIA", "(declare-const x Int)", "(not (= (* x 0) 0))", "NiaIdent_"),
        (
            "QF_DT",
            "(declare-datatypes ((Pair 0)) (((mk (fst Int) (snd Int)))))(declare-const a Int)(declare-const b Int)",
            "(not (= (fst (mk a b)) a))",
            "DtSel_",
        ),
    ];
    for (logic, decls, body, tag) in cases {
        let input = format!(
            r#"(set-option :produce-proofs true)(set-logic {logic}){decls}(assert {body})(check-sat)"#
        );
        let commands = parse(&input).unwrap();
        let mut exec = Executor::new();
        assert_eq!(
            exec.execute_all(&commands).unwrap(),
            vec!["unsat"],
            "{body}"
        );
        let fw = emit_firewall_lean(&exec, exec.last_proof.as_ref().unwrap());
        let f = fw
            .iter()
            .find(|f| f.contains(tag))
            .unwrap_or_else(|| panic!("expected a {tag} firewall for {body}"));
        assert!(f.contains("firewall_combined_unsat"));
    }
}

#[test]
fn test_qf_dt_tester_exclusion_emits_firewall_lean() {
    // bench `soundness_qf_dt_derived_terms/bug1_tester_excl_uf_app.smt2`:
    // two DISTINCT constructor testers on the SAME opaque term `(f x)` — no value
    // is headed by two constructors. End-to-end through the QF_UFDT pipeline.
    let input = r#"(set-option :produce-proofs true)(set-logic QF_UFDT)
        (declare-datatype Enum ((c0) (c1) (c2)))
        (declare-fun f (Enum) Enum)(declare-const x Enum)
        (assert ((_ is c0) (f x)))(assert ((_ is c1) (f x)))(check-sat)"#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert_eq!(exec.execute_all(&commands).unwrap(), vec!["unsat"]);
    let fw = emit_firewall_lean(&exec, exec.last_proof.as_ref().unwrap());
    let f = fw
        .iter()
        .find(|f| f.contains("DtTesterExcl_"))
        .expect("expected a DtTesterExcl firewall file");
    assert!(f.contains("firewall_combined_unsat"));
    assert!(f.contains("| k0 | k1 | k2"));
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

#[test]
fn test_failed_equality_farkas_promotion_stays_trusted_8866() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let x_eq_one = terms.mk_eq(x, one);
    let y_eq_two = terms.mk_eq(y, two);
    let clause = vec![terms.mk_not_raw(x_eq_one), terms.mk_not_raw(y_eq_two)];

    assert!(
        super::super::proof_farkas::synthesize_equality_farkas(&terms, &clause).is_none(),
        "precondition: the equality-specific Farkas synthesizer must fail"
    );

    let mut proof = Proof::new();
    let lemma_id = proof.add_theory_lemma("LIA", clause);

    Executor::promote_generic_theory_lemma_kinds_after_rewrite(&terms, &mut proof);

    let Some(ProofStep::TheoryLemma { kind, farkas, .. }) = proof.get_step(lemma_id) else {
        panic!("expected theory lemma step");
    };
    assert_eq!(
        *kind,
        TheoryLemmaKind::Generic,
        "failed Farkas synthesis must not leave LiaGeneric without coefficients"
    );
    assert!(farkas.is_none());

    proof.add_rule_step(AletheRule::ThResolution, vec![], vec![lemma_id], vec![]);
    let report = ay_proof::terminal_trust_report(&proof);
    assert_eq!(report.trust_theory_lemma_on_path, 1);
    assert!(report.has_terminal_trust());

    let rendered = ay_proof::export_alethe(&proof, &terms);
    assert!(
        !rendered.contains("UNVERIFIABLE PROOF"),
        "failed synthesis must export as honest trust, not as an uncertified arithmetic rule:\n{rendered}"
    );
    assert!(
        rendered.contains(":rule trust"),
        "failed synthesis should remain visible to terminal-trust detection:\n{rendered}"
    );
}

#[test]
fn test_uncertified_arithmetic_lemma_kinds_demote_to_trust_8866() {
    let mut proof = Proof::new();
    let t = TermId::new(1);

    proof.add_step(ProofStep::TheoryLemma {
        theory: String::from("LRA"),
        clause: vec![t],
        farkas: None,
        kind: TheoryLemmaKind::LraFarkas,
        lia: None,
    });
    proof.add_step(ProofStep::TheoryLemma {
        theory: String::from("LIA"),
        clause: vec![t],
        farkas: None,
        kind: TheoryLemmaKind::LiaGeneric,
        lia: None,
    });

    Executor::demote_uncertified_arithmetic_lemmas_to_trust(&mut proof);

    for step in &proof.steps {
        let ProofStep::TheoryLemma { kind, farkas, .. } = step else {
            panic!("expected theory lemma step");
        };
        assert_eq!(*kind, TheoryLemmaKind::Generic);
        assert!(farkas.is_none());
    }
}

#[test]
fn test_get_proof_no_check_sat() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 0))
        (get-proof)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert!(outputs[0].contains("no check-sat has been performed"));
}

#[test]
fn test_get_proof_rewrites_mod_div_auxiliary_symbols() {
    let benchmark_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/smt/regression/parity_xor_unsat.smt2");
    let benchmark = std::fs::read_to_string(&benchmark_path)
        .unwrap_or_else(|e| panic!("read {}: {e}", benchmark_path.display()));

    let input = format!("(set-option :produce-proofs true)\n{benchmark}\n(get-proof)\n");
    let commands = parse(&input).expect("parse benchmark");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute benchmark");

    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{outputs:?}"
    );
    let proof = outputs
        .get(1)
        .expect("expected get-proof output after unsat");

    assert!(
        !proof.contains("_mod_q_"),
        "proof leaked internal _mod_q witness:\n{proof}"
    );
    assert!(
        !proof.contains("_mod_r_"),
        "proof leaked internal _mod_r witness:\n{proof}"
    );
    assert!(
        !proof.contains("(declare-fun "),
        "Alethe proof must not contain top-level declarations:\n{proof}"
    );
    assert!(
        proof.contains("(mod "),
        "expected surface mod term in rewritten proof:\n{proof}"
    );
}

#[test]
fn test_trust_lemma_negation_preserves_checker_pivots() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let not_a = terms.mk_not(a);
    let not_b = terms.mk_not(b);
    let and_ab = terms.mk_and(vec![a, b]);
    let or_dual = terms.mk_or(vec![not_a, not_b]);
    let not_or_dual = terms.mk_not_raw(or_dual);

    let mut proof = Proof::new();
    proof.add_assume(and_ab, Some("h0".to_string()));
    proof.add_assume(not_a, Some("h1".to_string()));
    proof.add_assume(not_or_dual, Some("h2".to_string()));

    crate::executor::proof_resolution::empty_clause::derive_empty_via_trust_lemma(
        &mut terms, &mut proof,
    );

    let (summary, error) = check_proof_partial(&proof, &terms);
    assert!(
        error.is_none(),
        "trust lemma fallback should remain checker-valid, got {error:?}"
    );
    assert_eq!(
        summary.total_steps,
        proof.len() as u32,
        "partial checker should account for the whole trust derivation"
    );
    assert!(matches!(
        proof.steps.last(),
        Some(ProofStep::Step { clause, .. }) if clause.is_empty()
    ));
}

/// Direct unit test for prune_to_empty_clause_derivation.
///
/// Constructs a proof with both reachable and unreachable steps, prunes it,
/// and verifies that only the reachable steps survive with correct remapped
/// premise indices.
#[test]
fn test_prune_to_empty_clause_derivation_removes_unreachable_steps() {
    use ay_core::{AletheRule, TermId};

    let t1 = TermId::new(1);
    let t2 = TermId::new(2);
    let t3 = TermId::new(3);

    let mut proof = Proof::new();

    // Step 0: Assume(t1) — reachable (used by final resolution)
    let h0 = proof.add_assume(t1, None);
    // Step 1: Assume(t2) — reachable (used by final resolution)
    let h1 = proof.add_assume(t2, None);
    // Step 2: TheoryLemma [t3] — UNREACHABLE (not referenced by anything)
    let _unreachable = proof.add_theory_lemma("EUF", vec![t3]);
    // Step 3: Step(Trust) clause=[not(t1), not(t2)] — reachable (premise of step 4)
    let trust_step = proof.add_rule_step(
        AletheRule::Trust,
        vec![t1, t2], // clause content doesn't matter for pruning
        vec![],
        vec![],
    );
    // Step 4: Step(ThResolution) clause=[] — reachable (empty clause target)
    let _final_step = proof.add_rule_step(
        AletheRule::ThResolution,
        vec![], // empty clause
        vec![h0, h1, trust_step],
        vec![],
    );

    assert_eq!(proof.len(), 5);

    crate::executor::proof_resolution::prune_to_empty_clause_derivation(&mut proof);

    // Step 2 (unreachable TheoryLemma) should be removed
    assert_eq!(
        proof.len(),
        4,
        "expected 4 steps after pruning, got {}",
        proof.len()
    );

    // Step 0, 1 should still be Assume
    assert!(matches!(proof.steps[0], ProofStep::Assume(t) if t == t1));
    assert!(matches!(proof.steps[1], ProofStep::Assume(t) if t == t2));

    // Step 2 (was step 3) should be Trust rule
    assert!(matches!(
        &proof.steps[2],
        ProofStep::Step {
            rule: AletheRule::Trust,
            ..
        }
    ));

    // Step 3 (was step 4) should be ThResolution with remapped premises
    match &proof.steps[3] {
        ProofStep::Step {
            rule,
            clause,
            premises,
            ..
        } => {
            assert_eq!(*rule, AletheRule::ThResolution);
            assert!(clause.is_empty(), "final step should derive empty clause");
            // Old premises [0, 1, 3] should be remapped to [0, 1, 2]
            assert_eq!(premises, &[ProofId(0), ProofId(1), ProofId(2)]);
        }
        other => panic!("expected Step, got {other:?}"),
    }
}

/// Pruning a proof with no empty clause should be a no-op.
#[test]
fn test_prune_no_empty_clause_is_noop() {
    use ay_core::TermId;

    let t1 = TermId::new(1);
    let mut proof = Proof::new();
    proof.add_assume(t1, None);
    proof.add_theory_lemma("LRA", vec![t1]);

    let original_len = proof.len();
    crate::executor::proof_resolution::prune_to_empty_clause_derivation(&mut proof);
    assert_eq!(
        proof.len(),
        original_len,
        "prune should be no-op without empty clause"
    );
}

/// Pruning a proof where all steps are reachable should not change it.
#[test]
fn test_prune_all_reachable_is_noop() {
    use ay_core::{AletheRule, TermId};

    let t1 = TermId::new(1);
    let t2 = TermId::new(2);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(t1, None);
    let h1 = proof.add_assume(t2, None);
    let _final = proof.add_rule_step(AletheRule::ThResolution, vec![], vec![h0, h1], vec![]);

    assert_eq!(proof.len(), 3);
    crate::executor::proof_resolution::prune_to_empty_clause_derivation(&mut proof);
    assert_eq!(proof.len(), 3, "all-reachable proof should not change");
}

#[test]
fn test_theory_packet_resolution_derives_empty_clause() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let p = terms.mk_var("p", Sort::Bool);
    let not_a = terms.mk_not(a);
    let not_b = terms.mk_not(b);
    let not_c = terms.mk_not(c);
    let not_p = terms.mk_not(p);

    let mut proof = Proof::new();
    proof.add_assume(a, Some("h0".to_string()));
    proof.add_assume(b, Some("h1".to_string()));
    proof.add_assume(c, Some("h2".to_string()));
    proof.add_theory_lemma("EUF", vec![not_a, not_b, p]);
    proof.add_theory_lemma("LRA", vec![not_c, not_p]);

    assert!(
        crate::executor::proof_resolution::empty_clause::try_derive_empty_via_theory_packet_resolution(&terms, &mut proof),
        "expected two-lemma packet resolution to derive the empty clause"
    );
    assert!(matches!(
        proof.steps.last(),
        Some(ProofStep::Step { clause, .. }) if clause.is_empty()
    ));

    let (summary, error) = check_proof_partial(&proof, &terms);
    assert!(
        error.is_none(),
        "packet-derived proof should remain checker-valid, got {error:?} ({summary})"
    );
}

#[test]
fn test_proof_quality_metrics_in_statistics() {
    // Verify that proof quality metrics appear in :all-statistics after UNSAT (#4420)
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 0))
        (assert (> x 0))
        (check-sat)
        (get-info :all-statistics)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "unsat");

    let stats = &outputs[1];
    assert!(
        stats.contains(":proof-steps"),
        "Expected :proof-steps in statistics: {stats}"
    );
    assert!(
        stats.contains(":proof-verified"),
        "Expected :proof-verified in statistics: {stats}"
    );
    assert!(
        stats.contains(":proof-trust"),
        "Expected :proof-trust in statistics: {stats}"
    );
    assert!(
        stats.contains(":proof-complete"),
        "Expected :proof-complete in statistics: {stats}"
    );
}

#[test]
fn test_proof_quality_cleared_on_sat() {
    // Quality metrics should not carry over from a previous UNSAT (#4420)
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 0))
        (assert (> x 0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs[0], "unsat");

    // Now do a SAT check — quality should be cleared
    let input2 = r#"
        (reset)
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const y Real)
        (assert (> y 0))
        (check-sat)
        (get-info :all-statistics)
    "#;

    let commands2 = parse(input2).unwrap();
    let outputs2 = exec.execute_all(&commands2).unwrap();
    assert_eq!(outputs2[0], "sat");

    let stats = &outputs2[1];
    // After SAT, proof-steps should not appear (no proof was generated)
    assert!(
        !stats.contains(":proof-steps"),
        "proof-steps should not appear after SAT: {stats}"
    );
}

#[test]
fn test_proof_quality_strict_check_via_api() {
    // Verify strict checking reports unsupported arithmetic lemmas instead of
    // panicking after #6686 downgraded bound axioms from LraFarkas to Generic.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 0))
        (assert (> x 0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs[0], "unsat");

    // Access the proof and run strict check
    let proof = exec
        .last_proof
        .as_ref()
        .expect("proof should exist after UNSAT");
    let strict_result = ay_proof::check_proof_strict(proof, &exec.ctx.terms);

    // Arithmetic proofs now commonly include Generic theory lemmas, which
    // strict mode intentionally rejects until semantic validation exists.
    match strict_result {
        Ok(quality) => {
            assert!(
                quality.is_complete(),
                "strict-passing proof should be complete"
            );
        }
        Err(ay_proof::ProofCheckError::TrustStep { .. }) => {
            // Expected for trust-fallback proofs
        }
        Err(ay_proof::ProofCheckError::UnsupportedTheoryLemmaKind {
            kind: TheoryLemmaKind::Generic,
            ..
        }) => {
            // Expected for current arithmetic bound-axiom proofs (#6686).
        }
        Err(other) => {
            panic!("Unexpected strict check error: {other:?}");
        }
    }
}

#[cfg(feature = "proof-checker")]
#[test]
fn test_internal_proof_checker_records_partial_hole_metrics() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_var("x", Sort::Bool);
    let not_x = exec.ctx.terms.mk_not(x);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    let hole = proof.add_step(ProofStep::Step {
        rule: AletheRule::Hole,
        clause: vec![not_x],
        premises: vec![],
        args: vec![],
    });
    proof.add_resolution(vec![], x, hole, h0);

    exec.run_internal_proof_check(&proof);
    let stats = exec.statistics();
    assert_eq!(stats.get_int("proof_checker_failures"), Some(0));
    assert_eq!(stats.get_int("proof_checker_skipped_hole_steps"), Some(1));
    assert_eq!(stats.get_int("proof_checker_checked_steps"), Some(2));
    assert_eq!(stats.get_int("proof_checker_total_steps"), Some(3));
}

#[cfg(feature = "proof-checker")]
#[test]
fn self_check_rejects_generic_theory_lemma_accepted_by_partial_checker() {
    let mut exec = Executor::new();
    let p = exec.ctx.terms.mk_var("p", Sort::Bool);
    let not_p = exec.ctx.terms.mk_not(p);

    let mut proof = Proof::new();
    let lemma = proof.add_theory_lemma("test", vec![p]);
    let assumption = proof.add_assume(not_p, None);
    proof.add_resolution(Vec::new(), p, lemma, assumption);

    let (_, partial_error) = check_proof_partial(&proof, &exec.ctx.terms);
    assert!(
        partial_error.is_none(),
        "regression fixture must reach the former partial-check acceptance gap"
    );
    exec.run_internal_proof_check(&proof);
    exec.last_proof = Some(proof);

    assert!(
        !exec.unsat_proof_self_certified(),
        "self-check must reject a Generic theory lemma that has no semantic validator"
    );
}

#[cfg(feature = "proof-checker")]
#[test]
fn self_check_rejects_forged_named_theory_lemma_accepted_by_partial_checker() {
    let mut exec = Executor::new();
    let p = exec.ctx.terms.mk_var("p", Sort::Bool);
    let not_p = exec.ctx.terms.mk_not(p);

    let mut proof = Proof::new();
    let lemma = proof.add_theory_lemma_with_kind("EUF", vec![p], TheoryLemmaKind::EufTransitive);
    let assumption = proof.add_assume(not_p, None);
    proof.add_resolution(Vec::new(), p, lemma, assumption);

    let (_, partial_error) = check_proof_partial(&proof, &exec.ctx.terms);
    assert!(
        partial_error.is_none(),
        "regression fixture must reach the former partial-check acceptance gap"
    );
    exec.run_internal_proof_check(&proof);
    exec.last_proof = Some(proof);

    assert!(
        !exec.unsat_proof_self_certified(),
        "self-check must semantically reject a forged named theory lemma"
    );
}

#[cfg(feature = "proof-checker")]
#[test]
fn self_check_rejects_strict_refutation_from_non_problem_assumptions() {
    let mut exec = Executor::new();
    let p = exec.ctx.terms.mk_var("p", Sort::Bool);
    let not_p = exec.ctx.terms.mk_not(p);

    let mut proof = Proof::new();
    let p_assumption = proof.add_assume(p, None);
    let not_p_assumption = proof.add_assume(not_p, None);
    proof.add_resolution(Vec::new(), p, p_assumption, not_p_assumption);

    assert!(
        exec.check_proof_strict_with_datatypes(&proof).is_ok(),
        "regression fixture must be a valid derivation independent of its authority"
    );
    exec.run_internal_proof_check(&proof);
    exec.last_proof = Some(proof);

    assert!(
        !exec.unsat_proof_self_certified(),
        "self-check must reject assumptions that are not authored by the active problem"
    );
}

#[cfg(feature = "proof-checker")]
#[test]
fn self_check_accepts_strict_boolean_refutation() {
    let commands = parse(
        "(set-logic QF_UF)\n\
         (declare-const p Bool)\n\
         (assert p)\n\
         (assert (not p))\n\
         (check-sat)",
    )
    .unwrap();
    let mut exec = Executor::new();
    exec.set_self_check(true);
    exec.set_produce_proofs(true);

    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

/// Verify that invalid proofs record a failure without panicking (#7959).
/// Previously, debug builds would panic via `debug_assert!(false, ...)`,
/// which triggered `catch_unwind` in downstream consumers (verification-consumer).
/// Now all builds log the error and record the failure in statistics.
#[cfg(feature = "proof-checker")]
#[test]
fn test_internal_proof_checker_records_failure_without_panic() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_var("x", Sort::Bool);
    let y = exec.ctx.terms.mk_var("y", Sort::Bool);
    let not_x = exec.ctx.terms.mk_not(x);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    let h1 = proof.add_assume(not_x, None);
    proof.add_step(ProofStep::Resolution {
        clause: vec![y],
        pivot: x,
        clause1: h0,
        clause2: h1,
    });

    exec.run_internal_proof_check(&proof);
    let stats = exec.statistics();
    assert_eq!(stats.get_int(PROOF_CHECKER_FAILURES_KEY), Some(1));
    assert_eq!(stats.get_int(PROOF_CHECKER_SKIPPED_HOLE_STEPS_KEY), Some(0));
    assert_eq!(stats.get_int(PROOF_CHECKER_CHECKED_STEPS_KEY), Some(3));
    assert_eq!(stats.get_int(PROOF_CHECKER_TOTAL_STEPS_KEY), Some(3));
}

/// Verify that `:check-proofs-strict` option is read correctly (#4420).
#[test]
fn test_strict_proofs_option_defaults_to_false() {
    let exec = Executor::new();
    assert!(
        !exec.strict_proofs_enabled(),
        "strict proofs should default to disabled"
    );
}

/// Verify that strict proof mode runs end-to-end on a proof shape the
/// current strict checker can validate completely (#4420).
#[test]
fn test_strict_proof_mode_end_to_end() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-option :check-proofs-strict true)
        (set-logic QF_UF)
        (declare-const p Bool)
        (assert p)
        (assert (not p))
        (check-sat)
        (get-info :all-statistics)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "unsat");

    // Proof quality should be populated after strict checker runs.
    let stats = &outputs[1];
    assert!(
        stats.contains(":proof-steps"),
        "Expected :proof-steps in statistics: {stats}"
    );
}

/// End-to-end (#8419 / trust_count→0): a datatype constructor-distinctness
/// UNSAT emits a checker-validated `DatatypeDistinct` lemma (Alethe rule
/// `dt_distinct`), NOT a bare `trust` step. Under strict-proof mode the verdict
/// stays `unsat` instead of downgrading to `unknown`, because the terminal
/// derivation contains no trust step. Regression guard for the finalize-time
/// `promote_datatype_distinct_lemmas` promotion + registry-backed strict
/// validation.
#[test]
fn test_datatype_distinct_lemma_validated_not_trust_end_to_end() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-option :check-proofs-strict true)
        (set-logic QF_DT)
        (declare-datatype Color ((red) (green) (blue)))
        (declare-const c Color)
        (assert (= c red))
        (assert (= c green))
        (check-sat)
    "#;

    let commands = parse(input).expect("datatype script parses");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("datatype script executes");

    // Strict mode keeps `unsat` — the distinctness lemma is validated, not trust.
    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof().expect("a proof was produced");

    // The constructor-distinctness conflict lemma must carry the
    // strict-checkable `DatatypeDistinct` kind (promoted from `Generic` at
    // finalization), not a trust fallback.
    let has_dt_distinct = proof.steps.iter().any(|s| {
        matches!(
            s,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::DatatypeDistinct,
                ..
            }
        )
    });
    assert!(
        has_dt_distinct,
        "expected a DatatypeDistinct theory lemma in the datatype proof"
    );

    // The strict-proof verdict gate must see no terminal trust.
    let report = ay_proof::terminal_trust_report(proof);
    assert!(
        !report.has_terminal_trust(),
        "datatype-distinctness proof must have no terminal trust, got {report:?}"
    );
}

/// End-to-end (formal-verification half (1), datatype theory): the runtime
/// automatically emits a verified-firewall Lean proof for the datatype
/// distinctness lemma — the import-the-verified-theorem shape, generated (not
/// hand-written). The generator's output is separately confirmed to `lake build`
/// and kernel-check (axioms ⊆ {propext, Quot.sound}); this guards the runtime
/// wiring + emitted structure.
#[test]
fn test_runtime_emits_datatype_firewall_lean() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_DT)
        (declare-datatype Color ((red) (green) (blue)))
        (declare-const c Color)
        (assert (= c red))
        (assert (= c green))
        (check-sat)
    "#;
    let commands = parse(input).expect("datatype script parses");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("datatype script executes");
    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof().expect("a proof was produced").clone();
    let emitted = emit_firewall_lean(&exec, &proof);

    assert!(
        !emitted.is_empty(),
        "runtime must emit a firewall Lean proof for the dt_distinct lemma"
    );
    let lean = &emitted[0];
    for needle in [
        "import AySoundness.Firewall",
        "firewall_combined_unsat",
        "inductive T where",
        "theorem no_model",
    ] {
        assert!(lean.contains(needle), "emitted Lean missing: {needle}");
    }
}

/// End-to-end (formal-verification half (1), LINEAR ARITHMETIC theory): the
/// runtime emits a verified-firewall Lean proof for an `la_generic` bound
/// conflict (`x ≤ 1 ∧ x ≥ 2 ⊢ ⊥`). The generator's output is separately
/// confirmed to `lake build` and kernel-check (`omega`-discharged validity,
/// axioms ⊆ {propext, Quot.sound}).
#[test]
fn test_runtime_emits_lia_firewall_lean() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (<= x 1))
        (assert (>= x 2))
        (check-sat)
    "#;
    let commands = parse(input).expect("LIA script parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("LIA script executes");
    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof().expect("a proof was produced").clone();
    let emitted = emit_firewall_lean(&exec, &proof);

    assert!(
        !emitted.is_empty(),
        "runtime must emit a firewall Lean proof for the la_generic lemma"
    );
    let lean = &emitted[0];
    for needle in [
        "abbrev Val := Nat → Int",
        "omega",
        "firewall_combined_unsat",
        "theorem no_model",
    ] {
        assert!(lean.contains(needle), "emitted LIA Lean missing: {needle}");
    }
}

/// End-to-end (formal-verification half (1), EUF theory): the runtime emits a
/// verified-firewall Lean proof for an `eq_transitive` conflict
/// (`a=b ∧ b=c ∧ a≠c ⊢ ⊥`). Generator output separately confirmed to `lake
/// build` + kernel-check (`omega` validity, axioms ⊆ {propext, Quot.sound}).
#[test]
fn test_runtime_emits_euf_firewall_lean() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (assert (= a b))
        (assert (= b c))
        (assert (not (= a c)))
        (check-sat)
    "#;
    let commands = parse(input).expect("EUF script parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("EUF script executes");
    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof().expect("a proof was produced").clone();
    let emitted = emit_firewall_lean(&exec, &proof);

    assert!(
        !emitted.is_empty(),
        "runtime must emit a firewall Lean proof for the eq_transitive lemma"
    );
    let lean = &emitted[0];
    for needle in [
        "abbrev Val := Nat → Nat",
        "omega",
        "firewall_combined_unsat",
        "theorem no_model",
    ] {
        assert!(lean.contains(needle), "emitted EUF Lean missing: {needle}");
    }
}

/// End-to-end (formal-verification half (1), EUF CONGRUENCE — first
/// function-model theory): the runtime emits a verified-firewall Lean proof for
/// an `eq_congruent` conflict (`a=b ∧ f a ≠ f b ⊢ ⊥`). Generator output
/// separately confirmed to `lake build` + kernel-check (`simp`-congruence
/// validity over a `(valuation × function)` model, axioms ⊆ {propext,
/// Quot.sound}).
#[test]
fn test_runtime_emits_euf_congruence_firewall_lean() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-const a U)
        (declare-const b U)
        (assert (= a b))
        (assert (not (= (f a) (f b))))
        (check-sat)
    "#;
    let commands = parse(input).expect("EUF congruence script parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("script executes");
    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof().expect("a proof was produced").clone();
    let emitted = emit_firewall_lean(&exec, &proof);

    assert!(
        !emitted.is_empty(),
        "runtime must emit a firewall Lean proof for the eq_congruent lemma"
    );
    let lean = &emitted[0];
    for needle in [
        "abbrev Val := (Nat → Nat) × (Nat → Nat)",
        "firewall_combined_unsat",
        "theorem no_model",
    ] {
        assert!(
            lean.contains(needle),
            "emitted congruence Lean missing: {needle}"
        );
    }
}

/// End-to-end (formal-verification half (1), EUF PREDICATE-CONGRUENCE — fifth
/// theory): the runtime emits a verified-firewall Lean proof for an
/// `eq_congruent_pred` conflict (`a=b ∧ P a ∧ ¬P b ⊢ ⊥`). Generator output
/// separately confirmed to `lake build` + kernel-check (axioms ⊆ {propext,
/// Quot.sound}).
#[test]
fn test_runtime_emits_euf_pred_congruence_firewall_lean() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun P (U) Bool)
        (declare-const a U)
        (declare-const b U)
        (assert (= a b))
        (assert (P a))
        (assert (not (P b)))
        (check-sat)
    "#;
    let commands = parse(input).expect("pred-congruence script parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("script executes");
    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof().expect("a proof was produced").clone();
    let emitted = emit_firewall_lean(&exec, &proof);

    assert!(
        !emitted.is_empty(),
        "runtime must emit a firewall Lean proof for the eq_congruent_pred lemma"
    );
    let lean = &emitted[0];
    for needle in [
        "abbrev Val := (Nat → Nat) × (Nat → Bool)",
        "firewall_combined_unsat",
        "theorem no_model",
    ] {
        assert!(
            lean.contains(needle),
            "emitted pred-cong Lean missing: {needle}"
        );
    }
}

/// End-to-end (formal-verification half (1), ARRAY read-over-write-neg — sixth
/// theory): the runtime emits a verified-firewall Lean proof for a
/// `read_over_write_neg` conflict (`i≠j ∧ select(store a i v) j ≠ select a j ⊢
/// ⊥`). The emitter reconstructs the tautological `(i=j) ∨ (…)` lemma from the
/// unit's select/store structure. Generator output separately confirmed to
/// `lake build` + kernel-check (axioms ⊆ {propext, Quot.sound}).
#[test]
fn test_runtime_emits_array_row2_firewall_lean() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_AX)
        (declare-sort Idx 0)
        (declare-sort Elem 0)
        (declare-const a (Array Idx Elem))
        (declare-const i Idx)
        (declare-const j Idx)
        (declare-const v Elem)
        (assert (not (= i j)))
        (assert (not (= (select (store a i v) j) (select a j))))
        (check-sat)
    "#;
    let commands = parse(input).expect("array script parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("script executes");
    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof().expect("a proof was produced").clone();
    let emitted = emit_firewall_lean(&exec, &proof);

    assert!(
        !emitted.is_empty(),
        "runtime must emit a firewall Lean proof for the read_over_write_neg lemma"
    );
    let lean = &emitted[0];
    for needle in [
        "abbrev Val := (Nat → Nat) × (Nat → Nat)",
        "firewall_combined_unsat",
        "theorem no_model",
    ] {
        assert!(
            lean.contains(needle),
            "emitted array Lean missing: {needle}"
        );
    }
}

/// End-to-end (formal-verification half (1), STRING length — seventh theory):
/// the runtime emits a verified-firewall Lean proof for a string length-vs-
/// literal conflict (`s = "" ∧ str.len s = 3 ⊢ ⊥`). The conflict lemma and the
/// `TermId` assertions are surface-rewrite-trivialized, so the emitter
/// reconstructs from the FRONTEND PARSED assertions. Generator output separately
/// confirmed to `lake build` + kernel-check.
#[test]
fn test_runtime_emits_string_length_firewall_lean() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_S)
        (declare-const s String)
        (assert (= s ""))
        (assert (= (str.len s) 3))
        (check-sat)
    "#;
    let commands = parse(input).expect("string script parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("script executes");
    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof().expect("a proof was produced").clone();
    let emitted = emit_firewall_lean(&exec, &proof);

    assert!(
        emitted
            .iter()
            .any(|l| l.contains("abbrev Val := String") && l.contains("firewall_combined_unsat")),
        "runtime must emit a string-length firewall Lean proof from the parsed assertions"
    );
}

/// End-to-end (formal-verification half (1), BIT-VECTOR small-width — eighth
/// theory): the runtime emits a verified-firewall Lean proof for a small-width
/// BV conflict (`bvand x y = 0xF ∧ x ≠ 0xF ⊢ ⊥` over BitVec 4). ay bit-blasts BV
/// eagerly (bare-trust), so the emitter reconstructs from the FRONTEND PARSED
/// assertions and refutes by curried `decide`. Generator output separately
/// confirmed to `lake build` + kernel-check.
#[test]
fn test_runtime_emits_bv_firewall_lean() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (declare-const y (_ BitVec 4))
        (assert (= (bvand x y) #xF))
        (assert (not (= x #xF)))
        (check-sat)
    "#;
    let commands = parse(input).expect("BV script parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("script executes");
    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof().expect("a proof was produced").clone();
    let emitted = emit_firewall_lean(&exec, &proof);

    assert!(
        emitted
            .iter()
            .any(|l| l.contains("abbrev Val := BitVec 4") && l.contains("firewall_combined_unsat")),
        "runtime must emit a BV firewall Lean proof from the parsed assertions"
    );
}

/// End-to-end (formal-verification half (1), array read-over-write-SAME — ninth
/// theory): the runtime emits a verified-firewall Lean proof for a direct ROW-same
/// conflict (`select (store a i v) i ≠ v ⊢ ⊥`). ay refutes arrays eagerly
/// (bare-trust), so the emitter reconstructs from the FRONTEND PARSED assertions
/// and grounds the generic McCarthy ROW-same theorem. Generator output separately
/// confirmed to `lake build` + kernel-check.
#[test]
fn test_runtime_emits_array_row1_firewall_lean() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_AX)
        (declare-sort Idx 0)
        (declare-sort Elem 0)
        (declare-const a (Array Idx Elem))
        (declare-const i Idx)
        (declare-const v Elem)
        (assert (not (= (select (store a i v) i) v)))
        (check-sat)
    "#;
    let commands = parse(input).expect("ROW1 script parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("script executes");
    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof().expect("a proof was produced").clone();
    let emitted = emit_firewall_lean(&exec, &proof);

    assert!(
        emitted
            .iter()
            .any(|l| l.contains("ArrRow1_") && l.contains("firewall_combined_unsat")),
        "runtime must emit a ROW-same firewall Lean proof from the parsed assertions"
    );
}

/// End-to-end: the runtime emits a verified-firewall Lean proof for a BINARY
/// EUF-congruence conflict (`a=c ∧ b=d ∧ f(a,b)≠f(c,d) ⊢ ⊥`), exercising the
/// n-ary generalization of the congruence emitter (model carries a binary
/// `Nat → Nat → Nat` function). Generator output separately lake-verified.
#[test]
fn test_runtime_emits_binary_euf_congruence_firewall_lean() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun f (U U) U)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (declare-const d U)
        (assert (= a c))
        (assert (= b d))
        (assert (not (= (f a b) (f c d))))
        (check-sat)
    "#;
    let commands = parse(input).expect("binary congruence script parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("script executes");
    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof().expect("a proof was produced").clone();
    let emitted = emit_firewall_lean(&exec, &proof);

    assert!(
        emitted
            .iter()
            .any(|l| l.contains("(Nat → Nat) × (Nat → Nat → Nat)")
                && l.contains("firewall_combined_unsat")),
        "runtime must emit a binary-congruence firewall Lean proof"
    );
}

/// Verify that the strict option is correctly enabled via `set-option` (#4420).
#[test]
fn test_strict_proofs_option_enabled_via_set_option() {
    let input = r#"
        (set-option :check-proofs-strict true)
        (set-logic QF_LRA)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();
    assert!(
        exec.strict_proofs_enabled(),
        "strict proofs should be enabled after set-option"
    );
}

/// #6719 + #6722: QF_AX UNSAT proof with indirect store (ROW2 axiom).
///
/// Verifies trust-free proof for the indirect store pattern
/// `b = store(a, i, v)` with `i != j, select(b, j) != select(a, j)`.
/// - #6719: dpll_snapshot var_to_term capture for dynamic theory atoms
/// - #6722: eager array axiom proof annotations via record_eager_array_axiom_proofs
#[test]
fn test_array_row2_indirect_store_proof_structure() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_AX)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (declare-const v Int)
        (assert (= b (store a i v)))
        (assert (not (= i j)))
        (assert (not (= (select b j) (select a j))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs[0], "unsat");

    let proof = exec
        .last_proof
        .as_ref()
        .expect("proof should exist after UNSAT with produce-proofs");
    let quality =
        ay_proof::check_proof_with_quality(proof, &exec.ctx.terms).expect("proof should validate");
    assert!(
        quality.resolution_count + quality.th_resolution_count >= 1,
        "proof should contain resolution or theory resolution steps: {quality}"
    );
    // Input assertions may be compressed into axioms, theory lemmas, or
    // th_resolution steps by the proof engine. Check the proof has at least
    // some input facts rather than asserting a specific assume count.
    assert!(
        quality.assume_count >= 1 || quality.theory_lemma_count >= 1,
        "proof should have at least one input fact (assume or theory lemma): {quality}"
    );
    assert!(
        Executor::proof_derives_empty_clause(proof),
        "proof must derive the empty clause"
    );
    assert!(
        quality.theory_lemma_count >= 1,
        "ROW2 eager axiom should be recorded as theory lemma (#6722): {quality}"
    );
    // Array axioms now export as `read_over_write_pos`/`read_over_write_neg`/
    // `extensionality` in Alethe format (#8073), no longer falling back to `trust`.
    // The improvement from #6722 is that the axiom is *categorized* as a
    // TheoryLemma(ArraySelectStore) instead of being an anonymous original clause.
}

/// A QF_AX model that satisfies every AUTHORED assertion must self-certify as
/// `sat`, even though `--self-check` forces proof production on and the eager
/// array lane then leaves its injected ROW/extensionality axioms — over fresh
/// `__ay_*` / `__ext_diff_*` symbols that carry no model value — inside the
/// validation window. Those axioms are solver-generated, not part of the user's
/// claim; before #selfcert-authored they counted as "unverified" and degraded
/// EVERY QF_AX sat to `unknown` (0/60 self-certified on the SMT-LIB sample).
#[cfg(feature = "proof-checker")]
#[test]
fn self_check_certifies_qf_ax_sat_against_authored_assertions() {
    let commands = parse(
        "(set-logic QF_AX)\n\
         (declare-sort Index 0)\n\
         (declare-sort Element 0)\n\
         (declare-fun a () (Array Index Element))\n\
         (declare-fun i () Index)\n\
         (declare-fun j () Index)\n\
         (declare-fun u () Element)\n\
         (declare-fun v () Element)\n\
         (assert (not (= i j)))\n\
         (assert (= (select (store a i u) j) (select a j)))\n\
         (assert (not (= u v)))\n\
         (check-sat)",
    )
    .unwrap();
    let mut exec = Executor::new();
    exec.set_self_check(true);
    exec.set_produce_proofs(true);

    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

/// Companion of the test above for the store-FLATTENED shape (`*_sf_*` in the
/// SMT-LIB QF_AX families): proof-mode preprocessing CONSUMES the defining
/// equalities `(= a_k (store a_{k-1} i e))`, so the eliminated array variables
/// have no model value and the authored definitions evaluate to `Unknown`. The
/// gate closes the authored window under those definitions (a model extension)
/// and certifies the substituted window.
#[cfg(feature = "proof-checker")]
#[test]
fn self_check_certifies_store_flattened_sat_via_definitional_closure() {
    let commands = parse(
        "(set-logic QF_AX)\n\
         (declare-sort Index 0)\n\
         (declare-sort Element 0)\n\
         (declare-fun a () (Array Index Element))\n\
         (declare-fun i1 () Index)\n\
         (declare-fun i2 () Index)\n\
         (declare-fun e1 () Element)\n\
         (declare-fun e2 () Element)\n\
         (declare-fun a_1 () (Array Index Element))\n\
         (declare-fun a_2 () (Array Index Element))\n\
         (declare-fun b_1 () (Array Index Element))\n\
         (declare-fun b_2 () (Array Index Element))\n\
         (assert (= a_1 (store a i1 e1)))\n\
         (assert (= a_2 (store a_1 i2 e2)))\n\
         (assert (= b_1 (store a i2 e2)))\n\
         (assert (= b_2 (store b_1 i1 e1)))\n\
         (assert (not (= a_2 b_2)))\n\
         (check-sat)",
    )
    .unwrap();
    let mut exec = Executor::new();
    exec.set_self_check(true);
    exec.set_produce_proofs(true);

    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

/// The authored-window rescue must stay FAIL-CLOSED: an UNSAT problem can never
/// be turned into a `sat` by it (there is no model at all), and the `unsat` it
/// does report still has to clear the refutation-proof gate. The store-permuted
/// chains below are provably equal under pairwise-distinct indices, and AY's
/// array lemmas for that shape are still emitted as `trust`, so `--self-check`
/// must degrade to `unknown` rather than emit an uncertified `unsat`.
#[cfg(feature = "proof-checker")]
#[test]
fn self_check_authored_rescue_never_manufactures_sat() {
    let commands = parse(
        "(set-logic QF_AX)\n\
         (declare-sort Index 0)\n\
         (declare-sort Element 0)\n\
         (declare-fun a () (Array Index Element))\n\
         (declare-fun i1 () Index)\n\
         (declare-fun i2 () Index)\n\
         (declare-fun e1 () Element)\n\
         (declare-fun e2 () Element)\n\
         (declare-fun a_1 () (Array Index Element))\n\
         (declare-fun a_2 () (Array Index Element))\n\
         (declare-fun b_1 () (Array Index Element))\n\
         (declare-fun b_2 () (Array Index Element))\n\
         (assert (not (= i1 i2)))\n\
         (assert (= a_1 (store a i1 e1)))\n\
         (assert (= a_2 (store a_1 i2 e2)))\n\
         (assert (= b_1 (store a i2 e2)))\n\
         (assert (= b_2 (store b_1 i1 e1)))\n\
         (assert (not (= a_2 b_2)))\n\
         (check-sat)",
    )
    .unwrap();
    let mut exec = Executor::new();
    exec.set_self_check(true);
    exec.set_produce_proofs(true);

    let outputs = exec.execute_all(&commands).unwrap();

    assert_ne!(
        outputs,
        vec!["sat"],
        "unsatisfiable input must never self-certify as sat"
    );
}

#[test]
fn qf_s_ground_regex_refutation_self_certifies_from_authored_assertions() {
    // The QF_S `slog_stranger` "sink" family, verbatim in shape: a string
    // constant is pinned by an authored equality and then asserted to be in a
    // ground regex language it does not belong to.
    //
    // Before the ground string/regex checker and the substitution bridge this
    // exported as `assume (str.in_re "/mod/forum/" R)` (a preprocessing
    // artifact, NOT a problem premise) plus a `:rule trust` lemma, so
    // `--self-check` degraded the UNSAT to `unknown`. Now the leaf is DERIVED
    // from the authored assertion by `eq_congruent_pred` and the refutation is
    // a `string_ground_eval` lemma the checker decides outright.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_S)
        (declare-fun literal_5 () String)
        (assert (= literal_5 "/mod/forum/"))
        (assert (str.in_re literal_5
                  (re.++ (re.* re.allchar)
                         (re.++ (str.to_re "\u{5c}\u{3c}SCRIPT") (re.* re.allchar)))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert_eq!(exec.execute_all(&commands).unwrap(), vec!["unsat"]);

    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    match ay_proof::check_proof_strict(proof, &exec.ctx.terms) {
        Ok(quality) => assert_eq!(quality.trust_count, 0, "strict: zero trust steps"),
        Err(e) => panic!("ground-regex refutation must pass strict check, got {e:?}"),
    }
    assert!(
        proof.steps.iter().any(|s| matches!(
            s,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::StringGroundEval,
                ..
            }
        )),
        "the refuting lemma must carry the strict-checkable ground-eval kind"
    );
    assert!(
        proof.steps.iter().any(|s| matches!(
            s,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::EufCongruentPred,
                ..
            }
        )),
        "the substituted leaf must be bridged, not assumed"
    );

    // Every `assume` must be an AUTHORED assertion.
    let authored = exec.proof_original_problem_assertions();
    for step in &proof.steps {
        if let ProofStep::Assume(term) = step {
            assert!(
                authored.contains(term),
                "proof assumes a non-authored term {term:?}; authored = {authored:?}"
            );
        }
    }

    let text = exec.get_proof();
    assert!(
        !text.contains(":rule trust"),
        "ground-regex refutation must not fall back to trust; got:\n{text}"
    );
    assert!(
        text.contains(":rule string_ground_eval") && text.contains(":rule eq_congruent_pred"),
        "expected the ground-eval lemma and the congruence bridge; got:\n{text}"
    );
    assert!(
        exec.unsat_proof_self_certified(),
        "the refutation must now self-certify"
    );
}

#[test]
fn qf_s_ground_regex_membership_that_holds_is_sat() {
    // The soundness twin of the test above: when the pinned constant IS in the
    // language, the ground evaluator must NOT manufacture a refutation.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_S)
        (declare-fun literal_5 () String)
        (assert (= literal_5 "xx\u{5c}\u{3c}SCRIPTyy"))
        (assert (str.in_re literal_5
                  (re.++ (re.* re.allchar)
                         (re.++ (str.to_re "\u{5c}\u{3c}SCRIPT") (re.* re.allchar)))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert_eq!(
        exec.execute_all(&commands).unwrap(),
        vec!["sat"],
        "a membership that genuinely holds must stay SAT"
    );
}

#[test]
fn qf_s_symbolic_regex_intersection_refutation_self_certifies() {
    // The QF_S `automatark` family, verbatim in shape: a SYMBOLIC string
    // variable is asserted to be in two ground regex languages whose
    // intersection is empty. The ground evaluator cannot touch this — the fact
    // is not ground — so before the regex-emptiness certificate the refuting
    // lemma exported as `:rule trust` and `--self-check` degraded the UNSAT to
    // `unknown`. Now the lemma carries `RegexIntersectEmpty` and the checker
    // re-derives the whole derivative-product reachability argument itself.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_S)
        (declare-const X String)
        (assert (str.in_re X (re.++ (str.to_re "/f") (re.* (re.range "0" "9"))
                                    (str.to_re "/end"))))
        (assert (str.in_re X (re.++ (str.to_re "/f") (re.* (re.range "a" "z"))
                                    (str.to_re "/x"))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert_eq!(exec.execute_all(&commands).unwrap(), vec!["unsat"]);

    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    assert!(
        proof.steps.iter().any(|s| matches!(
            s,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::RegexIntersectEmpty,
                ..
            }
        )),
        "the refuting lemma must carry the strict-checkable regex-emptiness kind"
    );
    match ay_proof::check_proof_strict(proof, &exec.ctx.terms) {
        Ok(quality) => assert_eq!(quality.trust_count, 0, "strict: zero trust steps"),
        Err(e) => panic!("symbolic regex refutation must pass strict check, got {e:?}"),
    }
    let text = exec.get_proof();
    assert!(
        !text.contains(":rule trust"),
        "symbolic regex refutation must not fall back to trust; got:\n{text}"
    );
    assert!(
        text.contains(":rule regex_intersect_empty"),
        "expected the regex-emptiness lemma; got:\n{text}"
    );
    assert!(
        exec.unsat_proof_self_certified(),
        "the refutation must now self-certify"
    );
}

#[test]
fn qf_s_symbolic_regex_intersection_that_is_non_empty_stays_sat() {
    // The soundness twin: overlapping languages must NOT manufacture a
    // refutation. `X` = "007" satisfies both memberships.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_S)
        (declare-const X String)
        (assert (str.in_re X (re.++ (re.range "0" "9") (re.range "0" "9") (re.range "0" "9"))))
        (assert (str.in_re X (re.* (re.range "0" "9"))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert_eq!(
        exec.execute_all(&commands).unwrap(),
        vec!["sat"],
        "an intersection with a member must stay SAT"
    );
}

#[test]
fn qf_ax_store_flat_refutation_self_certifies_from_authored_assertions() {
    // The QF_AX `storecomm_*_sf_*` family, verbatim in shape: two store chains
    // build the same array by permuted writes at pairwise-distinct indices, and
    // the problem asserts the two endpoints differ.
    //
    // `substitute_store_flat_equalities` expands every defined array name into
    // its store chain and then DROPS the defining equalities (they have become
    // `true`), so the exported refutation assumed the fully expanded
    // `(not (= (store (store a1 i1 e1) i2 e2) (store (store a1 i2 e2) i1 e1)))`
    // — a preprocessing artifact, not a problem premise. The #8821 authority
    // gate refused to publish that proof and `--self-check` degraded the UNSAT
    // to `unknown`. The substitution bridge now walks back down the chain with
    // `trans` through each authored defining equality plus congruence on the
    // store's array argument, so every leaf is an authored assertion again.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a1 () (Array Index Element))
        (declare-fun b1 () (Array Index Element))
        (declare-fun b2 () (Array Index Element))
        (declare-fun c1 () (Array Index Element))
        (declare-fun c2 () (Array Index Element))
        (declare-fun i1 () Index)
        (declare-fun i2 () Index)
        (declare-fun e1 () Element)
        (declare-fun e2 () Element)
        (assert (= b1 (store a1 i1 e1)))
        (assert (= b2 (store b1 i2 e2)))
        (assert (= c1 (store a1 i2 e2)))
        (assert (= c2 (store c1 i1 e1)))
        (assert (not (= i1 i2)))
        (assert (not (= b2 c2)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert_eq!(exec.execute_all(&commands).unwrap(), vec!["unsat"]);

    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");

    // Every `assume` must be an AUTHORED assertion — this is exactly what the
    // #8821 gate checks, asserted here directly so a regression fails loudly
    // rather than silently degrading to `unknown`.
    let authored = exec.proof_original_problem_assertions();
    for step in &proof.steps {
        if let ProofStep::Assume(term) = step {
            assert!(
                authored.contains(term),
                "proof assumes a non-authored term {term:?}"
            );
        }
    }
    assert!(
        ay_proof::validate_reachable_assumes_in_problem_scope(proof, &authored).is_ok(),
        "the rebuilt proof must clear the #8821 authority gate"
    );

    let text = exec.get_proof();
    assert!(
        !text.contains(":rule trust"),
        "the store-flat refutation must not fall back to trust; got:\n{text}"
    );
    assert!(
        text.contains(":rule trans"),
        "expected the chain-walking `trans` bridge; got:\n{text}"
    );
    assert!(
        exec.unsat_proof_self_certified(),
        "the store-flat refutation must now self-certify"
    );
}

// ===========================================================================
// Array extensionality diff-witness certification (#ext-diff-cert).
//
// The injected axiom `(= a b) ∨ ¬(= (select a k) (select b k))` is NOT a
// tautology, so promotion is only sound when the proof also records what `k`
// is. Each acceptance test below has a twin that breaks exactly one provenance
// condition and asserts the gate REJECTS.
// ===========================================================================

/// A stand-in parsed AST: only the assertion COUNT matters for the
/// parsed-prefix boundary these tests exercise.
fn parsed_placeholder() -> ay_frontend::command::Term {
    ay_frontend::command::Term::Symbol("problem".to_string())
}

/// `(not (= a b))` over two array constants, plus the extensionality axiom the
/// eager array lane injects for that pair, in the `Generic`/trust shape
/// `push_array_axiom_assertion_site` records.
fn ext_axiom_fixture() -> (Executor, Proof, TermId, TermId, TermId) {
    let mut exec = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = exec.ctx.terms.mk_var("ext_a", array_sort.clone());
    let b = exec.ctx.terms.mk_var("ext_b", array_sort);
    let k = exec.ctx.terms.mk_var("__ext_diff_1_2", Sort::Int);
    let eq_ab = exec.ctx.terms.mk_eq(a, b);
    let not_eq_ab = exec.ctx.terms.mk_not(eq_ab);
    let sel_a = exec.ctx.terms.mk_select(a, k);
    let sel_b = exec.ctx.terms.mk_select(b, k);
    let sel_eq = exec.ctx.terms.mk_eq(sel_a, sel_b);
    let not_sel_eq = exec.ctx.terms.mk_not(sel_eq);
    let ext_axiom = exec.ctx.terms.mk_or(vec![eq_ab, not_sel_eq]);

    // The problem asserted the disequality; the extensionality axiom is the
    // SOLVER's own injection, appended AFTER the problem's parsed prefix (the
    // boundary `proof_original_problem_assertions` reads).
    exec.ctx
        .add_assertion_with_parsed(not_eq_ab, parsed_placeholder());
    exec.ctx.assertions.push(ext_axiom);

    let mut proof = Proof::new();
    proof.add_assume(not_eq_ab, None);
    proof.add_theory_lemma("array", vec![ext_axiom]);
    (exec, proof, a, b, k)
}

#[test]
fn injected_extensionality_axiom_is_promoted_with_a_witness_introduction() {
    let (mut exec, mut proof, a, b, k) = ext_axiom_fixture();
    exec.promote_array_extensionality_axioms(&mut proof);

    assert!(
        proof
            .steps
            .iter()
            .all(|step| !matches!(step, ProofStep::TheoryLemma { kind, .. } if kind.is_trust())),
        "the injected extensionality axiom must stop being a trust lemma"
    );
    assert_eq!(
        proof
            .steps
            .iter()
            .filter(|step| matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::ArrayExtensionality,
                    ..
                }
            ))
            .count(),
        1
    );
    let intro = proof
        .steps
        .iter()
        .find_map(|step| match step {
            ProofStep::Step {
                rule: AletheRule::ArrayExtDiffIntro,
                clause,
                premises,
                args,
            } => Some((clause.clone(), premises.clone(), args.clone())),
            _ => None,
        })
        .expect("promotion must append a witness introduction");
    assert!(
        intro.0.is_empty() && intro.1.is_empty(),
        "the introduction is a definition: no clause, no premises"
    );
    assert_eq!(intro.2, vec![k, a, b]);

    exec.unsat_proof_extensionality_certified(&proof)
        .then_some(())
        .expect("a freshly introduced, once-bound witness must certify");
}

#[test]
fn promoted_extensionality_is_rejected_when_the_witness_is_not_fresh() {
    // SOUNDNESS CRUX. The problem itself constrains `__ext_diff_1_2`, so the
    // clause is no longer a conservative extension and the gate must refuse it
    // even though the promotion produced a perfectly-shaped introduction.
    let (mut exec, mut proof, _a, _b, k) = ext_axiom_fixture();
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let pinned = exec.ctx.terms.mk_eq(k, zero);
    // The pinning constraint is a PROBLEM assertion, so it extends the parsed
    // prefix; the injected axiom stays after it.
    let injected = exec.ctx.assertions.pop().expect("injected axiom");
    exec.ctx
        .add_assertion_with_parsed(pinned, parsed_placeholder());
    exec.ctx.assertions.push(injected);

    exec.promote_array_extensionality_axioms(&mut proof);
    assert!(
        !exec.unsat_proof_extensionality_certified(&proof),
        "a witness the problem also constrains must not certify"
    );
}

#[test]
fn promoted_extensionality_is_rejected_when_the_introduction_names_another_pair() {
    let (mut exec, mut proof, a, _b, k) = ext_axiom_fixture();
    let c = exec
        .ctx
        .terms
        .mk_var("ext_c", Sort::array(Sort::Int, Sort::Int));
    exec.promote_array_extensionality_axioms(&mut proof);

    // Tamper: rebind the witness to a different array pair.
    for step in &mut proof.steps {
        if let ProofStep::Step {
            rule: AletheRule::ArrayExtDiffIntro,
            args,
            ..
        } = step
        {
            *args = vec![k, a, c];
        }
    }
    assert!(
        !exec.unsat_proof_extensionality_certified(&proof),
        "an introduction for a different pair must not certify the clause"
    );
}

#[test]
fn qf_ax_store_flat_permutation_that_is_consistent_stays_sat() {
    // The soundness twin: the SAME store chains, but WITHOUT the
    // `(not (= i1 i2))` premise the permutation argument needs. The two
    // endpoints may legitimately differ (take `i1 = i2`, `e1 != e2`), so the
    // bridge must not help manufacture a refutation.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a1 () (Array Index Element))
        (declare-fun b1 () (Array Index Element))
        (declare-fun b2 () (Array Index Element))
        (declare-fun c1 () (Array Index Element))
        (declare-fun c2 () (Array Index Element))
        (declare-fun i1 () Index)
        (declare-fun i2 () Index)
        (declare-fun e1 () Element)
        (declare-fun e2 () Element)
        (assert (= b1 (store a1 i1 e1)))
        (assert (= b2 (store b1 i2 e2)))
        (assert (= c1 (store a1 i2 e2)))
        (assert (= c2 (store c1 i1 e1)))
        (assert (not (= b2 c2)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert_ne!(
        exec.execute_all(&commands).unwrap(),
        vec!["unsat"],
        "a satisfiable store-flat permutation must never be refuted"
    );
}

#[test]
fn promoted_extensionality_is_rejected_when_the_introduction_is_removed() {
    let (mut exec, mut proof, _a, _b, _k) = ext_axiom_fixture();
    exec.promote_array_extensionality_axioms(&mut proof);
    proof.steps.retain(|step| {
        !matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::ArrayExtDiffIntro,
                ..
            }
        )
    });
    assert!(
        !exec.unsat_proof_extensionality_certified(&proof),
        "an extensionality lemma with no introduction must not certify"
    );
}

#[test]
fn one_witness_shared_by_two_array_pairs_is_never_promoted() {
    // The solver should never mint one witness for two pairs; if it somehow
    // did, no single introduction could be true, so NEITHER axiom is promoted
    // and both stay trust.
    let (mut exec, mut proof, a, _b, k) = ext_axiom_fixture();
    let c = exec
        .ctx
        .terms
        .mk_var("ext_c", Sort::array(Sort::Int, Sort::Int));
    let eq_ac = exec.ctx.terms.mk_eq(a, c);
    let sel_a = exec.ctx.terms.mk_select(a, k);
    let sel_c = exec.ctx.terms.mk_select(c, k);
    let sel_eq = exec.ctx.terms.mk_eq(sel_a, sel_c);
    let not_sel_eq = exec.ctx.terms.mk_not(sel_eq);
    let second_axiom = exec.ctx.terms.mk_or(vec![eq_ac, not_sel_eq]);
    exec.ctx.assertions.push(second_axiom);
    proof.add_theory_lemma("array", vec![second_axiom]);

    exec.promote_array_extensionality_axioms(&mut proof);
    assert!(
        proof.steps.iter().all(|step| !matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::ArrayExtDiffIntro,
                ..
            }
        )),
        "a witness shared across pairs must produce no introduction at all"
    );
    assert_eq!(
        proof
            .steps
            .iter()
            .filter(|step| matches!(step, ProofStep::TheoryLemma { kind, .. } if kind.is_trust()))
            .count(),
        2,
        "both axioms must stay uncertified trust lemmas"
    );
}

#[test]
fn a_problem_asserted_extensionality_shaped_clause_is_never_promoted() {
    // Promotion is limited to assertions the SOLVER injected. A clause of the
    // same shape written by the USER is a problem premise, not a Skolem
    // definition, and must keep its `assume` provenance.
    let (mut exec, _proof, _a, _b, _k) = ext_axiom_fixture();
    let ext_axiom = exec.ctx.assertions[1];
    exec.ctx.assertions.clear();
    exec.ctx
        .add_assertion_with_parsed(ext_axiom, parsed_placeholder());
    let mut proof = Proof::new();
    proof.add_assume(ext_axiom, None);

    exec.promote_array_extensionality_axioms(&mut proof);
    assert!(
        matches!(proof.steps.as_slice(), [ProofStep::Assume(_)]),
        "a problem-asserted clause must stay an assume, got {:?}",
        proof.steps
    );
}
