// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `completion.rs` to preserve test FQNs.

#[cfg(test)]
mod quantified_output_completion_tests {
    use super::{EvalValue, Executor, Model};
    use ay_core::term::Symbol;
    use ay_core::Sort;
    use ay_frontend::parse;
    use num_bigint::BigInt;
    use num_rational::BigRational;

    fn executor_with_absent_g() -> Executor {
        let mut executor = Executor::new();
        executor
            .execute_all(
                &parse(
                    "(set-logic UFLIA)\n\
                     (set-option :produce-models true)\n\
                     (declare-fun g (Int) Int)\n\
                     (assert true)",
                )
                .expect("valid quantified-output completion fixture"),
            )
            .expect("fixture executes");
        executor
    }

    fn g_at_zero(executor: &mut Executor) -> ay_core::TermId {
        let zero = executor.ctx.terms.mk_int(BigInt::from(0));
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("g"), vec![zero], Sort::Int)
    }

    #[test]
    fn quantified_preseal_completion_isolates_the_candidate_from_ambient_eval_memo() {
        let mut executor = Executor::new();
        executor
            .execute_all(
                &parse(
                    "(set-logic LIA)\n\
                     (declare-const c Bool)\n\
                     (assert true)",
                )
                .expect("valid memo-isolation fixture"),
            )
            .expect("fixture executes");
        let roots = executor.ctx.assertions.clone();
        // This fixture covers the direct source-declaration lane; native API\n        // declarations are covered separately below.
        let info = executor.ctx.symbol_info("c").expect("declared constant");
        assert_eq!(
            info.declaration_kind(),
            ay_frontend::DeclarationKind::Uninterpreted
        );
        assert!(info.internal_name.is_none());
        assert!(info.is_direct_source_declaration());
        let c = info.term.expect("declared constant has a term");
        assert!(!executor.ctx.is_internal_symbol("c"));
        assert_eq!(
            executor.evaluate_term(&Model::empty(), c),
            EvalValue::Unknown
        );
        let stale = EvalValue::Bool(true);
        let canonical_default = EvalValue::Bool(false);

        // Completion must neither read nor overwrite an outer predecessor's
        // memo while evaluating the isolated candidate.
        let memo_session = crate::executor::model::EvalMemoSession::new();
        crate::executor::model::seed_eval_memo_for_test(c, stale.clone());
        assert_eq!(
            crate::executor::model::with_isolated_eval_memo(|| {
                executor.evaluate_term(&Model::empty(), c)
            }),
            EvalValue::Unknown,
            "an isolated candidate evaluation must not read the outer memo"
        );
        let mut candidate = Model::empty();
        assert!(executor.complete_quantified_output_model_before_seal(&mut candidate, &roots,));
        assert_eq!(candidate.bool_overrides.get(&c), Some(&false));
        assert_eq!(
            executor.evaluate_term(&Model::empty(), c),
            stale,
            "the ambient predecessor memo must be restored byte-for-byte"
        );

        drop(memo_session);
        assert_eq!(executor.evaluate_term(&candidate, c), canonical_default);
    }

    /// The native-API lane of the same contract the source-path fixtures pin
    /// above: `Solver::declare_const` registers through
    /// `register_native_global_constant`, which allocates the term and
    /// records its metadata atomically (`NativeApiDeclaration`), so an
    /// unconstrained API-declared constant receives the canonical default
    /// exactly like a parsed `declare-const`. Without this, quantified SAT
    /// models were partial for API consumers and `try_get_model` failed with
    /// "sat accepted without a total model" (the deductive-checks spec constants).
    #[test]
    fn quantified_preseal_completion_fills_native_api_declarations() {
        let mut executor = Executor::new();
        executor
            .execute_all(&parse("(set-logic LIA)\n(assert true)").expect("valid fixture"))
            .expect("fixture executes");
        let roots = executor.ctx.assertions.clone();
        let c = executor
            .ctx
            .register_native_global_constant("api-c".to_string(), Sort::Bool);
        let info = executor.ctx.symbol_info("api-c").expect("registered");
        assert!(!info.is_direct_source_declaration());
        assert!(info.is_completion_eligible_declaration());

        let mut candidate = Model::empty();
        assert!(executor.complete_quantified_output_model_before_seal(&mut candidate, &roots));
        assert_eq!(
            candidate.bool_overrides.get(&c),
            Some(&false),
            "an unconstrained native-API declaration receives the canonical default"
        );
    }

    /// Only positive-origin declarations receive completion defaults. A
    /// caller-supplied-term registration (`register_symbol`) is the entry
    /// point the forged-owner rejection tests use and the registrar internal
    /// lanes (optimization relax/aux symbols) go through — filling those
    /// would leak solver bookkeeping into user models or reward a forged
    /// registration, so completion must skip them even though they satisfy
    /// every other eligibility leg.
    #[test]
    fn quantified_preseal_completion_skips_caller_supplied_term_registrations() {
        let mut executor = Executor::new();
        executor
            .execute_all(&parse("(set-logic LIA)\n(assert true)").expect("valid fixture"))
            .expect("fixture executes");
        let roots = executor.ctx.assertions.clone();
        let c = executor.ctx.terms.mk_var("plain-c", Sort::Bool);
        executor
            .ctx
            .register_symbol("plain-c".to_string(), c, Sort::Bool);
        let info = executor.ctx.symbol_info("plain-c").expect("registered");
        assert_eq!(
            info.declaration_kind(),
            ay_frontend::DeclarationKind::Uninterpreted
        );
        assert!(!info.is_completion_eligible_declaration());

        let mut candidate = Model::empty();
        assert!(executor.complete_quantified_output_model_before_seal(&mut candidate, &roots));
        assert_eq!(
            candidate.bool_overrides.get(&c),
            None,
            "an Other-origin registration must not be default-filled"
        );
    }

    #[test]
    fn quantified_authority_publication_clears_the_predecessor_eval_memo() {
        #[derive(Clone, Copy)]
        enum AuthorityLane {
            Datatype,
            Mbqi,
        }

        for lane in [AuthorityLane::Datatype, AuthorityLane::Mbqi] {
            let mut executor = Executor::new();
            executor
                .execute_all(
                    &parse("(set-logic ALL)\n(declare-const memo-c Bool)\n(assert true)")
                        .expect("valid authority memo fixture"),
                )
                .expect("fixture executes");
            let roots = executor.ctx.assertions.clone();
            let c = executor
                .ctx
                .symbol_info("memo-c")
                .expect("declared constant")
                .term
                .expect("declared constant has a term");
            executor.last_model = Some(Model::empty());

            let memo_session = crate::executor::model::EvalMemoSession::new();
            crate::executor::model::seed_eval_memo_for_test(c, EvalValue::Bool(true));
            assert_eq!(
                executor
                    .evaluate_term(executor.last_model.as_ref().expect("predecessor model"), c,),
                EvalValue::Bool(true)
            );

            let admitted = match lane {
                AuthorityLane::Datatype => {
                    crate::executor::mbqi::CheckedDtSatAuthority::for_test(&mut executor, &roots)
                        .is_some()
                }
                AuthorityLane::Mbqi => {
                    crate::executor::mbqi::CheckedMbqiSatAuthority::for_test(&mut executor, &roots)
                        .is_some()
                }
            };
            assert!(admitted, "authority constructor must accept its fixture");
            assert_eq!(
                executor.evaluate_term(executor.last_model.as_ref().expect("completed model"), c,),
                EvalValue::Bool(false),
                "installing the completed model must invalidate predecessor memo entries"
            );
            drop(memo_session);
        }
    }

    #[test]
    fn quantified_preseal_function_default_is_not_euf_evidence_and_round_trips() {
        let mut executor = executor_with_absent_g();
        let roots = executor.ctx.assertions.clone();
        let application = g_at_zero(&mut executor);
        let mut model = Model::empty();

        assert!(executor.complete_quantified_output_model_before_seal(&mut model, &roots));
        assert!(
            model.euf_model.is_none(),
            "output completion must not create EUF gate evidence"
        );
        assert_eq!(
            executor.evaluate_term(&model, application),
            EvalValue::Rational(BigRational::from_integer(BigInt::from(0)))
        );
        assert_eq!(model.formula_neutral_function_default_entries().len(), 1);

        executor.last_model = Some(model);
        let evidence =
            crate::executor::mbqi::CheckedMbqiSatAuthority::for_test(&mut executor, &roots)
                .expect("preseal completion retains a model-bound theorem");
        assert!(executor.install_mbqi_sat_authority(evidence));
        assert!(executor
            .mbqi_sat_cert_query_grant
            .as_ref()
            .is_some_and(|grant| grant.is_current_for(&executor, &roots)));
        executor.last_result = Some(crate::executor_types::SolveResult::Sat);
        let printed = executor.model();
        assert!(
            printed.contains("(define-fun g ((x!0 Int)) Int\n    0)"),
            "get-model must print the same canonical value returned by evaluation: {printed}"
        );
    }

    #[test]
    fn quantified_function_default_fails_closed_after_source_epoch_change() {
        let mut executor = executor_with_absent_g();
        let roots = executor.ctx.assertions.clone();
        let application = g_at_zero(&mut executor);
        let mut model = Model::empty();
        assert!(executor.complete_quantified_output_model_before_seal(&mut model, &roots));

        executor
            .execute(&ay_frontend::Command::Push(1))
            .expect("scope mutation succeeds");
        assert!(!model.formula_neutral_function_defaults_are_current(&executor.ctx));
        assert_eq!(
            executor.evaluate_term(&model, application),
            EvalValue::Unknown
        );
    }

    #[test]
    fn replanning_with_function_in_exact_roots_clears_prior_default_package() {
        let mut executor = executor_with_absent_g();
        let initial_roots = executor.ctx.assertions.clone();
        let application = g_at_zero(&mut executor);
        let mut model = Model::empty();
        assert!(executor.complete_quantified_output_model_before_seal(&mut model, &initial_roots));
        assert_eq!(model.formula_neutral_function_default_entries().len(), 1);

        let zero = executor.ctx.terms.mk_int(BigInt::from(0));
        let constrained_root = executor.ctx.terms.mk_eq(application, zero);
        assert!(
            executor.complete_quantified_output_model_before_seal(&mut model, &[constrained_root],)
        );
        assert!(model.formula_neutral_function_default_entries().is_empty());
        assert!(model.euf_model.is_none());
        assert_eq!(
            executor.evaluate_term(&model, application),
            EvalValue::Unknown
        );
    }
}
