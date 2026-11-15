// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[test]
fn test_qf_dt_selector_projection_collapse_is_strict_checkable() {
    // `(not (= (fst (mk a b)) a))` is the negation of the selector-projection
    // axiom instance, so the term builder folds `fst(mk a b) → a` at elaboration
    // and the whole assertion collapses to `false`. The UNSAT proof degenerates
    // to a SINGLE empty-clause `trust` step. `promote_dt_selector_collapse`
    // reconstructs the refutation from the parsed assertion: an `assume` of the
    // disequality, a strict-checkable `DatatypeSelectorProject` lemma, and a
    // resolution to the empty clause — trust-free, validated against the
    // constructor→selector registry. The equality keeps its authored
    // orientation, so the `assume` is the problem's own assertion.
    //
    // On the wire the lemma is Clean's `dt_project` in the default (Clean)
    // dialect, through `symm` when the value is written first; pinned Carcara
    // has no datatype rule, so the pinned dialect prints the honest `hole`.
    // The datatype-aware strict checker below validates the real step either way.
    for (equality, wire) in [
        (
            "(= (fst (mk a b)) a)",
            "(step t1 (cl (= (fst (mk a b)) a)) :rule dt_project)",
        ),
        (
            "(= a (fst (mk a b)))",
            "(step t1.dt (cl (= (fst (mk a b)) a)) :rule dt_project)\n\
             (step t1 (cl (= a (fst (mk a b)))) :rule symm :premises (t1.dt))",
        ),
    ] {
        for dialect in [
            ay_proof::AletheDialect::Clean,
            ay_proof::AletheDialect::PinnedCarcara,
        ] {
            let input = format!(
                "(set-option :produce-proofs true)\n\
                 (set-logic QF_DT)\n\
                 (declare-datatypes ((Pair 0)) (((mk (fst Int) (snd Int)))))\n\
                 (declare-const a Int)\n\
                 (declare-const b Int)\n\
                 (assert (not {equality}))\n\
                 (check-sat)\n"
            );
            let commands = parse(&input).unwrap();
            let mut exec = Executor::new();
            exec.set_alethe_dialect(dialect);
            let outputs = exec.execute_all(&commands).unwrap();
            assert_eq!(outputs, vec!["unsat"], "{equality} {dialect:?}");
            let text = exec.get_proof();
            assert!(
                !text.contains(":rule trust"),
                "DT selector-projection collapse must not fall back to trust; got:\n{text}"
            );
            assert!(
                text.contains(&format!("(assume t0 (not {equality}))")),
                "the assume is the authored assertion; got:\n{text}"
            );
            match dialect {
                ay_proof::AletheDialect::PinnedCarcara => {
                    assert!(
                        text.contains(&format!("(step t1 (cl {equality}) :rule hole)")),
                        "the pinned dialect keeps the honest hole; got:\n{text}"
                    );
                    assert!(!text.contains("dt_project"), "{text}");
                }
                _ => {
                    assert!(text.contains(wire), "expected {wire}; got:\n{text}");
                    assert!(!text.contains(":rule hole"), "{text}");
                }
            }
            let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
            // Validation requires the constructor→selector registry, so go through the
            // executor's datatype-aware strict checker rather than the bare one.
            match exec.check_proof_strict_with_datatypes(proof) {
                Ok(quality) => assert_eq!(quality.trust_count, 0, "strict: zero trust steps"),
                Err(e) => panic!("DT selector-projection proof must pass strict check, got {e:?}"),
            }
        }
    }
}

/// The executor's two document judgements read its own dialect.
///
/// REGRESSION (measured 2026-10-02 on the dt_project commit): under
/// `(set-option :check-proofs-strict true)` the Clean dialect withheld this
/// UNSAT as `unknown (incomplete proof-trusted)`, "its Alethe rendering has a
/// known wire gap no external checker accepts", though the document it
/// renders is hole-free and Clean passes it, because the known-wire-gap
/// screen read the kind's wire rule (`hole`) whatever the dialect. And the
/// preflight render that chooses between proofs
/// (`proof_renders_without_unproved_step`) rendered in the thread's default
/// (Clean) dialect, so a pinned-dialect executor judged a `dt_project` proof
/// hole-free while its published document prints the hole.
#[test]
fn test_qf_dt_selector_projection_strict_option_reads_the_dialect() {
    for equality in ["(= (fst (mk a b)) a)", "(= a (fst (mk a b)))"] {
        for dialect in [
            ay_proof::AletheDialect::Clean,
            ay_proof::AletheDialect::PinnedCarcara,
        ] {
            let clean = dialect == ay_proof::AletheDialect::Clean;
            let input = format!(
                "(set-option :produce-proofs true)\n\
                 (set-option :check-proofs-strict true)\n\
                 (set-logic QF_DT)\n\
                 (declare-datatypes ((Pair 0)) (((mk (fst Int) (snd Int)))))\n\
                 (declare-const a Int)\n\
                 (declare-const b Int)\n\
                 (assert (not {equality}))\n\
                 (check-sat)\n"
            );
            let commands = parse(&input).unwrap();
            let mut exec = Executor::new();
            exec.set_alethe_dialect(dialect);
            let outputs = exec.execute_all(&commands).unwrap();
            let expected = if clean { "unsat" } else { "unknown" };
            assert_eq!(outputs, vec![expected], "{equality} {dialect:?}");
            if !clean {
                continue;
            }
            assert!(!exec.unsat_proof_has_known_wire_gap(), "{equality}");
            let proof = exec.last_proof.clone().expect("proof after UNSAT");
            assert!(
                exec.proof_renders_without_unproved_step(&proof),
                "{equality}: the Clean render is hole-free"
            );
            exec.set_alethe_dialect(ay_proof::AletheDialect::PinnedCarcara);
            assert!(exec.unsat_proof_has_known_wire_gap(), "{equality}");
            assert!(
                !exec.proof_renders_without_unproved_step(&proof),
                "{equality}: the pinned render prints the hole"
            );
        }
    }
}

#[test]
fn test_qf_dt_nested_selector_transport_is_strict_checkable() {
    // `x = (mk (g 0))` with `(case (f x)) != 0`: the contradiction needs TWO
    // selector transports (project `f` over `mk`, then `case` over `g`), so
    // a single-step transport planner cannot rebuild it. Roots are built
    // through the native API without simplification, like the tester test
    // above, so the planner itself is what is exercised.
    let mut exec = Executor::new();
    let declarations = parse(
        r#"
        (set-option :produce-proofs true)
        (set-logic QF_DT)
        (declare-datatypes ((D 0) (F 0)) (((mk (f F))) ((g (case Int)))))
        "#,
    )
    .unwrap();
    assert!(exec.execute_all(&declarations).unwrap().is_empty());

    let d_sort = Sort::Uninterpreted("D".to_string());
    let f_sort = Sort::Uninterpreted("F".to_string());
    let x = exec.ctx.terms.mk_var("x", d_sort.clone());
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let g0 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("g"), [zero], f_sort.clone());
    let mk_g0 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("mk"), [g0], d_sort.clone());
    let source = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [x, mk_g0], Sort::Bool);
    let f_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("f"), [x], f_sort.clone());
    let case_f_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("case"), [f_x], Sort::Int);
    let goal_eq = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [case_f_x, zero], Sort::Bool);
    let goal = exec.ctx.terms.mk_not_raw(goal_eq);
    exec.ctx
        .add_assertion_with_parsed(source, parsed_placeholder());
    exec.ctx
        .add_assertion_with_parsed(goal, parsed_placeholder());

    let mut proof = Proof::new();
    terminal_empty_trust(&mut proof, None);
    exec.replace_with_exact_authored_datatype_refutation(&mut proof);
    let projections = proof
        .steps
        .iter()
        .filter(|step| {
            matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::DatatypeSelectorProject,
                    ..
                }
            )
        })
        .count();
    assert!(
        projections >= 2,
        "nested transport must carry both selector projections, got {projections}"
    );
    assert!(
        ay_proof::terminal_trust_report(&proof).is_trust_free(),
        "nested selector proof must be trust-free"
    );
    exec.check_proof_strict_with_datatypes(&proof)
        .unwrap_or_else(|error| panic!("strict datatype replay failed: {error:?}"));
}

#[test]
fn test_qf_dt_negated_conjunction_transport_is_strict_checkable() {
    // The P22 shape in one authored root:
    // `(and (= x (mk (g 0))) (not (and (= 0 0) (= (case (f x)) 0))))`.
    // The selector equality sits inside a negated conjunction, so closing
    // it needs `NotAnd` plus a discharge of the sibling conjunct in
    // addition to the two selector transports.
    let mut exec = Executor::new();
    let declarations = parse(
        r#"
        (set-option :produce-proofs true)
        (set-logic QF_DT)
        (declare-datatypes ((D 0) (F 0)) (((mk (f F))) ((g (case Int)))))
        "#,
    )
    .unwrap();
    assert!(exec.execute_all(&declarations).unwrap().is_empty());

    let d_sort = Sort::Uninterpreted("D".to_string());
    let f_sort = Sort::Uninterpreted("F".to_string());
    let x = exec.ctx.terms.mk_var("x", d_sort.clone());
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let g0 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("g"), [zero], f_sort.clone());
    let mk_g0 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("mk"), [g0], d_sort.clone());
    let source = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [x, mk_g0], Sort::Bool);
    let f_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("f"), [x], f_sort.clone());
    let case_f_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("case"), [f_x], Sort::Int);
    let selector_eq = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [case_f_x, zero], Sort::Bool);
    let reflexive_sibling = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [zero, zero], Sort::Bool);
    let inner_and = exec.ctx.terms.mk_app(
        Symbol::named("and"),
        [reflexive_sibling, selector_eq],
        Sort::Bool,
    );
    let negated = exec.ctx.terms.mk_not_raw(inner_and);
    let root = exec
        .ctx
        .terms
        .mk_app(Symbol::named("and"), [source, negated], Sort::Bool);
    exec.ctx
        .add_assertion_with_parsed(root, parsed_placeholder());

    let mut proof = Proof::new();
    terminal_empty_trust(&mut proof, None);
    exec.replace_with_exact_authored_datatype_refutation(&mut proof);
    assert!(
        ay_proof::terminal_trust_report(&proof).is_trust_free(),
        "negated-conjunction transport must be trust-free"
    );
    exec.check_proof_strict_with_datatypes(&proof)
        .unwrap_or_else(|error| panic!("strict negated-conjunction transport failed: {error:?}"));
}

#[test]
fn test_qf_dt_negated_conjunction_bv_sibling_transport_is_strict_checkable() {
    // The P22 sibling shape: the non-selector conjunct is a ground BV
    // concat equality, discharged by the BV/LIA double-negation lemma
    // rather than reflexivity.
    let mut exec = Executor::new();
    let declarations = parse(
        r#"
        (set-option :produce-proofs true)
        (set-logic QF_DT)
        (declare-datatypes ((D 0) (F 0)) (((mk (f F))) ((g (case (_ BitVec 8))))))
        "#,
    )
    .unwrap();
    assert!(exec.execute_all(&declarations).unwrap().is_empty());

    let d_sort = Sort::Uninterpreted("D".to_string());
    let f_sort = Sort::Uninterpreted("F".to_string());
    let x = exec.ctx.terms.mk_var("x", d_sort.clone());
    let zero8 = exec.ctx.terms.mk_bitvec(BigInt::from(0), 8);
    let g0 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("g"), [zero8], f_sort.clone());
    let mk_g0 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("mk"), [g0], d_sort.clone());
    let source = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [x, mk_g0], Sort::Bool);
    let f_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("f"), [x], f_sort.clone());
    let case_f_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("case"), [f_x], Sort::bitvec(8));
    let selector_eq = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [case_f_x, zero8], Sort::Bool);
    let four32 = exec.ctx.terms.mk_bitvec(BigInt::from(4), 32);
    let zero32 = exec.ctx.terms.mk_bitvec(BigInt::from(0), 32);
    let concat = exec
        .ctx
        .terms
        .mk_app(Symbol::named("concat"), [four32, zero32], Sort::bitvec(64));
    let concat_value = exec
        .ctx
        .terms
        .mk_bitvec(BigInt::from(17_179_869_184i64), 64);
    let bv_sibling = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [concat, concat_value], Sort::Bool);
    let inner_and =
        exec.ctx
            .terms
            .mk_app(Symbol::named("and"), [bv_sibling, selector_eq], Sort::Bool);
    let negated = exec.ctx.terms.mk_not_raw(inner_and);
    let root = exec
        .ctx
        .terms
        .mk_app(Symbol::named("and"), [source, negated], Sort::Bool);
    exec.ctx
        .add_assertion_with_parsed(root, parsed_placeholder());

    let mut proof = Proof::new();
    terminal_empty_trust(&mut proof, None);
    exec.replace_with_exact_authored_datatype_refutation(&mut proof);
    assert!(
        ay_proof::terminal_trust_report(&proof).is_trust_free(),
        "BV-sibling negated-conjunction transport must be trust-free"
    );
    exec.check_proof_strict_with_datatypes(&proof)
        .unwrap_or_else(|error| {
            panic!("strict BV-sibling negated-conjunction transport failed: {error:?}")
        });
}

#[test]
fn test_qf_dt_negated_conjunction_leaf_sibling_transport_is_strict_checkable() {
    // The P22 transformed shape: a sibling conjunct is an equality over a
    // free 64-bit BV variable (`(= fld #x0000000400000000)`), which is no
    // BV/LIA tautology — the bounded checker refuses finite enumeration
    // over the free variable. It closes only because the same equality is
    // a positive authored leaf of the root.
    let mut exec = Executor::new();
    let declarations = parse(
        r#"
        (set-option :produce-proofs true)
        (set-logic QF_DT)
        (declare-datatypes ((D 0) (F 0)) (((mk (f F))) ((g (case (_ BitVec 8))))))
        "#,
    )
    .unwrap();
    assert!(exec.execute_all(&declarations).unwrap().is_empty());

    let d_sort = Sort::Uninterpreted("D".to_string());
    let f_sort = Sort::Uninterpreted("F".to_string());
    let x = exec.ctx.terms.mk_var("x", d_sort.clone());
    let zero8 = exec.ctx.terms.mk_bitvec(BigInt::from(0), 8);
    let g0 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("g"), [zero8], f_sort.clone());
    let mk_g0 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("mk"), [g0], d_sort.clone());
    let source = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [x, mk_g0], Sort::Bool);
    let f_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("f"), [x], f_sort.clone());
    let case_f_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("case"), [f_x], Sort::bitvec(8));
    let selector_eq = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [case_f_x, zero8], Sort::Bool);
    let fld = exec.ctx.terms.mk_var("fld", Sort::bitvec(64));
    let fld_value = exec
        .ctx
        .terms
        .mk_bitvec(BigInt::from(17_179_869_184i64), 64);
    let fld_eq = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [fld, fld_value], Sort::Bool);
    let inner_and = exec
        .ctx
        .terms
        .mk_app(Symbol::named("and"), [fld_eq, selector_eq], Sort::Bool);
    let negated = exec.ctx.terms.mk_not_raw(inner_and);
    let root = exec
        .ctx
        .terms
        .mk_app(Symbol::named("and"), [source, fld_eq, negated], Sort::Bool);
    exec.ctx
        .add_assertion_with_parsed(root, parsed_placeholder());

    let mut proof = Proof::new();
    terminal_empty_trust(&mut proof, None);
    exec.replace_with_exact_authored_datatype_refutation(&mut proof);
    assert!(
        ay_proof::terminal_trust_report(&proof).is_trust_free(),
        "leaf-sibling negated-conjunction transport must be trust-free"
    );
    exec.check_proof_strict_with_datatypes(&proof)
        .unwrap_or_else(|error| {
            panic!("strict leaf-sibling negated-conjunction transport failed: {error:?}")
        });
}
