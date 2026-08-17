// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

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
        text.contains(":rule arrays_idx"),
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
    // `dt_project` is AY's kind name, not an Alethe rule (carcara has no
    // datatype rules at all), so on the wire the lemma is an honest `hole`.
    // The datatype-aware strict checker below still validates the real step.
    assert!(
        text.contains(":rule hole"),
        "reconstructed proof should carry the projection lemma as an honest hole; got:\n{text}"
    );
    assert!(
        !text.contains("dt_project"),
        "must not emit a rule name no Alethe checker implements; got:\n{text}"
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
fn test_qf_dt_concrete_tester_evaluation_is_strict_checkable() {
    for (label, actual_ctor, authored_is_positive) in [
        ("matching-negative", "red", false),
        ("distinct-positive", "green", true),
    ] {
        // The SMT-LIB elaborator deliberately evaluates a concrete tester at
        // parse time, so an end-to-end script reaches the earlier literal-false
        // lane and cannot prove that this producer is wired. Retain the public
        // datatype declaration, but construct the exact native-API root without
        // simplification so this test exercises DatatypeTesterEval itself.
        let mut exec = Executor::new();
        let declarations = parse(
            r#"
            (set-option :produce-proofs true)
            (set-logic QF_DT)
            (declare-datatype Color ((red) (green)))
            "#,
        )
        .unwrap();
        assert!(exec.execute_all(&declarations).unwrap().is_empty());

        let color = Sort::Uninterpreted("Color".to_string());
        let actual = exec.ctx.terms.mk_var(actual_ctor, color);
        let theorem = exec
            .ctx
            .terms
            .mk_app(Symbol::named("is-red"), [actual], Sort::Bool);
        let root = if authored_is_positive {
            theorem
        } else {
            exec.ctx.terms.mk_not_raw(theorem)
        };
        exec.ctx
            .add_assertion_with_parsed(root, parsed_placeholder());

        let mut proof = Proof::new();
        terminal_empty_trust(&mut proof, None);
        exec.replace_with_exact_authored_datatype_refutation(&mut proof);
        assert!(
            proof.steps.iter().any(|step| matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::DatatypeTesterEval,
                    ..
                }
            )),
            "{label}: reconstructed proof must carry the declaration-backed tester theorem"
        );
        assert!(
            ay_proof::terminal_trust_report(&proof).is_trust_free(),
            "{label}: concrete tester proof must be trust-free"
        );
        exec.check_proof_strict_with_datatypes(&proof)
            .unwrap_or_else(|error| panic!("{label}: strict datatype replay failed: {error:?}"));
    }
}

#[test]
fn test_qf_dt_injected_exhaustive_axiom_is_typed_and_strict_checkable() {
    // A tester-coverage refutation: `x` is neither of List's two constructors.
    // (A recursive datatype keeps the problem out of the all-nullary enum
    // elimination lanes and in the real DT axiom-injection path; `solve_dt` is
    // driven directly so the proof under inspection is exactly the native DT
    // lane's.) The refutation NEEDS the injected family-(D) exhaustiveness
    // disjunction `(or (is-nil x) (is-cons x))`. Under C5 it must be recorded
    // with its validator-backed kind — not `Generic` — the surviving proof must
    // be entirely trust-free, and the datatype-aware strict checker must
    // independently re-validate it.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_DT)
        (declare-datatype List ((nil) (cons (hd Int) (tl List))))
        (declare-const x List)
        (assert (not ((_ is nil) x)))
        (assert (not ((_ is cons) x)))
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert!(exec.execute_all(&commands).unwrap().is_empty());
    exec.proof_tracker.enable();
    let result = exec.solve_dt().expect("solve_dt must not error");
    assert!(result.is_unsat(), "tester-coverage conflict must be UNSAT");
    let proof = exec.last_proof.clone().expect("proof after UNSAT");
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::DatatypeExhaustive,
                ..
            }
        )),
        "the injected constructor-coverage disjunction must carry the \
         DatatypeExhaustive kind"
    );
    assert!(
        !proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::Generic,
                ..
            }
        )),
        "this pure-DT exhaustiveness refutation must carry no Generic lemma"
    );
    assert!(ay_proof::terminal_trust_report(&proof).is_trust_free());
    exec.check_proof_strict_with_datatypes(&proof)
        .expect("exhaustiveness refutation must pass the datatype-aware strict check");
}

#[test]
fn test_dt_emitted_exhaustive_and_reconstruct_axioms_match_their_validators() {
    // Emitter<->validator agreement on the REAL emitted terms (the C5 risk:
    // the validators must accept the shape `dt_selector_axioms` actually
    // interns — canonicalized `or` literal order, `mk_eq` orientation,
    // nullary constructors as `Var` — not a textbook rendering). The eager
    // pass for `x : List` must inject
    //   family (D): `(or (is-nil x) (is-cons x))`
    //   family (C): `(or (not (is-nil x)) (= x nil))`  (registry-nullary)
    //               `(or (not (is-cons x)) (= x (cons (hd x) (tl x))))`
    // and each must be recognized by the recognizer that IS the strict
    // validator, fed the same registries the strict check receives.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_DT)
        (declare-datatype List ((nil) (cons (hd Int) (tl List))))
        (declare-const x List)
        (assert (not ((_ is nil) x)))
        (assert (not ((_ is cons) x)))
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert!(exec.execute_all(&commands).unwrap().is_empty());
    let base: ay_core::kani_compat::DetHashSet<TermId> =
        exec.ctx.assertions.iter().copied().collect();
    let axioms = exec.dt_selector_axioms(&base);
    let dt_decls = exec.datatype_decls_for_strict_proof();
    let ctor_selectors = exec.ctor_selector_decls_for_strict_proof();

    let exhaustive: Vec<_> = axioms
        .iter()
        .copied()
        .filter(|&axiom| {
            ay_proof::recognize_datatype_exhaustive(&exec.ctx.terms, &[axiom], &dt_decls)
        })
        .collect();
    assert!(
        !exhaustive.is_empty(),
        "the emitted family-(D) coverage disjunction must satisfy the \
         DatatypeExhaustive validator"
    );

    let reconstruct: Vec<_> = axioms
        .iter()
        .copied()
        .filter(|&axiom| {
            ay_proof::recognize_datatype_constructor_reconstruct(
                &exec.ctx.terms,
                &[axiom],
                &dt_decls,
                &ctor_selectors,
            )
        })
        .collect();
    assert!(
        reconstruct.len() >= 2,
        "both emitted family-(C) guarded reconstructions (nullary nil and \
         binary cons) must satisfy the DatatypeConstructorReconstruct \
         validator; recognized {} of {} injected axioms",
        reconstruct.len(),
        axioms.len()
    );

    // Fail-closed cross-check: neither family is recognized without its
    // registry (the classifier can never out-accept the checker).
    let empty: Vec<(String, Vec<String>)> = Vec::new();
    for &axiom in &exhaustive {
        assert!(!ay_proof::recognize_datatype_exhaustive(
            &exec.ctx.terms,
            &[axiom],
            &empty
        ));
    }
    for &axiom in &reconstruct {
        assert!(!ay_proof::recognize_datatype_constructor_reconstruct(
            &exec.ctx.terms,
            &[axiom],
            &dt_decls,
            &empty
        ));
    }
}

#[test]
fn test_qf_dt_mined_acyclicity_units_stay_generic_and_fail_strict_check() {
    // Case-split structural cycles: every disjunct equates `(cons k x)` with
    // `(cons k (cons k x))`, which the frontend's constructor-injectivity
    // decomposition folds to the direct cycle `(= x (cons k x))`. Nine two-way
    // case splits push the occurs-check fast path past its documented
    // 256-combination cross-product bound, so the refutation runs through the
    // mined `#dt-acyclic-case-split` units at the SAT layer. With that
    // promotion lane disabled, a surviving mined unit must remain explicit
    // `Generic` trust and the datatype-aware strict checker must reject the
    // proof rather than publishing an unsupported typed lemma.
    let mut input = String::from(
        r#"
        (set-option :produce-proofs true)
        (set-logic QF_DT)
        (declare-datatype List ((nil) (cons (hd Int) (tl List))))
        (declare-const x List)
    "#,
    );
    for i in 0..9u32 {
        let (a, b) = (2 * i, 2 * i + 1);
        input.push_str(&format!(
            "(assert (or (= (cons {a} x) (cons {a} (cons {a} x))) \
                         (= (cons {b} x) (cons {b} (cons {b} x)))))\n"
        ));
    }
    let commands = parse(&input).unwrap();
    let mut exec = Executor::new();
    assert!(exec.execute_all(&commands).unwrap().is_empty());
    exec.proof_tracker.enable();
    let result = exec.solve_dt().expect("solve_dt must not error");
    assert!(result.is_unsat(), "the case-split cycles must be UNSAT");
    let proof = exec.last_proof.clone().expect("proof after UNSAT");
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::Generic,
                ..
            }
        )),
        "the mined cycle-breaking units must remain explicit Generic trust"
    );
    assert!(
        !proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::DatatypeAcyclicDirect,
                ..
            }
        )),
        "the disabled acyclicity promotion must not mint DatatypeAcyclicDirect"
    );
    assert!(!ay_proof::terminal_trust_report(&proof).is_trust_free());
    assert!(exec.check_proof_strict_with_datatypes(&proof).is_err());
}
