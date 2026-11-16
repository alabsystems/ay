// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! No parser: exercise the native root authority and real strict commit seam.

use super::*;
use crate::api::proofs::EnvelopeStop;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

fn fixture() -> (Executor, Vec<TermId>) {
    let mut executor = Executor::new();
    let x = executor
        .ctx
        .register_native_global_constant("native_proof_x".into(), Sort::bitvec(4));
    let zero = executor.ctx.terms.mk_bitvec(0.into(), 4);
    let one = executor.ctx.terms.mk_bitvec(1.into(), 4);
    let a = executor.ctx.terms.mk_eq(x, zero);
    let b = executor.ctx.terms.mk_eq(x, one);
    executor.ctx.assertions = vec![a, b];
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    assert_eq!(executor.ctx.assertions_parsed(), []);
    (executor, vec![a, b])
}

fn native_offer_recorded(executor: &Executor) -> bool {
    NativeBvRefutationScope::capture(executor).is_some_and(|scope| {
        executor
            .evaluation_attempt()
            .native_bv_refutation_attempted(&scope)
    })
}

#[test]
fn unsuppressed_incomplete_native_proof_gets_an_exact_checked_replacement() {
    let (mut executor, roots) = restored_named_native_fixture();
    executor.last_unsat_proof_reconstruction_suppressed = false;
    assert!(!executor.last_unsat_proof_reconstruction_suppressed);
    assert!(executor
        .check_proof_strict_with_datatypes(executor.last_proof.as_ref().unwrap())
        .is_err());
    assert!(!native_offer_recorded(&executor));
    executor.refresh_authenticated_native_bv_refutation_after_named_core_redirect();
    let proof = executor
        .last_proof
        .as_ref()
        .expect("a retained replacement");
    assert!(Executor::proof_derives_empty_clause(proof));
    assert!(executor
        .check_proof_strict_with_datatypes(proof)
        .is_ok_and(|quality| quality.is_complete()));
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(proof, &roots).is_ok());
    assert!(native_offer_recorded(&executor));
}

#[test]
fn strict_complete_presentable_native_proof_does_not_start_a_repair() {
    let (mut executor, roots) = restored_named_native_fixture();
    let mut proof = provisional();
    assert!(executor.try_authenticated_native_bv_refutation(&mut proof));
    let core_names = executor.last_core_term_to_name.clone();
    // A new query over the same immutable roots has no consumed native offer.
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    executor.last_assumptions = Some(roots.clone());
    executor.last_assumption_core = Some(roots);
    executor.last_core_term_to_name = core_names;
    executor.last_unsat_proof_reconstruction_suppressed = false;
    assert!(executor
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
    assert!(executor.candidate_authored_surface_is_available(&proof));
    assert!(!native_offer_recorded(&executor));
    let original = format!("{:?}", proof.steps);
    executor.last_proof = Some(proof);
    executor.refresh_authenticated_native_bv_refutation_after_named_core_redirect();
    assert_eq!(
        format!("{:?}", executor.last_proof.as_ref().unwrap().steps),
        original
    );
    assert!(!native_offer_recorded(&executor));
}

fn provisional() -> Proof {
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![], vec![], vec![]);
    proof
}

fn unchanged_refusal(executor: &mut Executor) {
    let mut proof = provisional();
    let before = format!("{:?}", proof.steps);
    let raw = executor.last_proof_raw_original_assertions.clone();
    let rebuilt = executor.last_proof_rebuild_originals.clone();
    assert!(!executor.try_authenticated_native_bv_refutation(&mut proof));
    assert_eq!(format!("{:?}", proof.steps), before);
    assert_eq!(executor.last_proof_raw_original_assertions, raw);
    assert_eq!(executor.last_proof_rebuild_originals, rebuilt);
}

#[test]
fn native_roots_commit_a_complete_exact_scope_proof_once() {
    let (mut executor, roots) = fixture();
    // The preprocessing stack is not the source authority.
    executor.ctx.assertions.clear();
    let mut proof = provisional();
    assert!(executor.try_authenticated_native_bv_refutation(&mut proof));
    assert!(Executor::proof_derives_empty_clause(&proof));
    assert!(executor
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &roots).is_ok());
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &roots[..1]).is_err());
    assert_eq!(
        executor.last_proof_raw_original_assertions,
        [] as [TermId; 0]
    );
    assert_eq!(executor.last_proof_rebuild_originals, [] as [TermId; 0]);
    assert!(native_offer_recorded(&executor));
    // The late shared producer cannot replenish this attempt's expensive lane.
    assert!(executor
        .exact_authored_bv_refutation(|_, _| panic!("no second offer"))
        .is_none());
}

#[test]
fn native_bound_assumptions_are_exact_and_load_bearing() {
    let (mut executor, roots) = fixture();
    executor.ctx.assertions = vec![roots[0]];
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[roots[1]]);
    executor.last_assumptions = Some(vec![roots[1]]);
    let mut proof = provisional();
    assert!(executor.try_authenticated_native_bv_refutation(&mut proof));
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &roots).is_ok());
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &roots[..1]).is_err());

    let (mut mismatch, roots) = fixture();
    mismatch.last_assumptions = Some(vec![roots[0]]);
    unchanged_refusal(&mut mismatch);
    let (mut unbound, _) = fixture();
    unbound.begin_public_solve(false);
    unchanged_refusal(&mut unbound);
}

#[test]
fn native_epoch_source_provenance_and_entry_changes_refuse() {
    let (mut stale, _) = fixture();
    stale.advance_query_authority_epoch();
    unchanged_refusal(&mut stale);
    let (mut stale, _) = fixture();
    stale
        .ctx
        .process_command(&Command::Push(1))
        .expect("push changes source");
    unchanged_refusal(&mut stale);
    let (mut forged, roots) = fixture();
    forged
        .proof_problem_assertion_provenance
        .as_mut()
        .expect("source provenance")
        .original_problem_assertions = vec![roots[0]];
    unchanged_refusal(&mut forged);

    let mut reused = Executor::new();
    let checkpoint = reused.ctx.terms.rollback_checkpoint();
    let root = reused
        .ctx
        .terms
        .mk_fresh_named_var("reused_native", Sort::Bool);
    reused.ctx.assertions = vec![root];
    reused.begin_public_solve(false);
    reused.bind_unsat_query_assumptions(&[]);
    reused.ctx.terms.rollback_to(checkpoint);
    let replacement = reused
        .ctx
        .terms
        .mk_fresh_named_var("replacement_native", Sort::Bool);
    assert_eq!(root, replacement);
    unchanged_refusal(&mut reused);
}

#[test]
fn native_grammar_uses_core_vars_and_checks_full_operator_typing() {
    let (mut executor, roots) = fixture();
    assert!(grammar::accepts(&executor, &roots, &|| false));
    // A free core Var needs no source-name credential: semantic replay must
    // establish a theorem for EVERY valuation of its exact canonical identity.
    let free = executor
        .ctx
        .terms
        .mk_fresh_named_var("unregistered_leaf", Sort::bitvec(4));
    let truth = executor.ctx.terms.true_term();
    let eq =
        executor
            .ctx
            .terms
            .mk_app_structural(Symbol::Named("=".into()), [free, truth], Sort::Bool);
    assert!(!grammar::accepts(&executor, &[eq], &|| false));
    let bad_arity = executor.ctx.terms.mk_app_structural(
        Symbol::Named("bvudiv".into()),
        [free],
        Sort::bitvec(4),
    );
    let bad_root = executor.ctx.terms.mk_eq(free, bad_arity);
    assert!(!grammar::accepts(&executor, &[bad_root], &|| false));
    let bad_width = executor.ctx.terms.mk_app_structural(
        Symbol::Indexed("extract".into(), vec![5, 0]),
        [free],
        Sort::bitvec(4),
    );
    let bad_root = executor.ctx.terms.mk_eq(free, bad_width);
    assert!(!grammar::accepts(&executor, &[bad_root], &|| false));
    let uf = executor.ctx.terms.mk_app_structural(
        Symbol::Named("native_uf".into()),
        [free],
        Sort::bitvec(4),
    );
    let uf_root = executor.ctx.terms.mk_eq(free, uf);
    assert!(!grammar::accepts(&executor, &[uf_root], &|| false));
    let int = executor
        .ctx
        .terms
        .mk_fresh_named_var("outside_int", Sort::Int);
    let mixed =
        executor
            .ctx
            .terms
            .mk_app_structural(Symbol::Named("=".into()), [free, int], Sort::Bool);
    assert!(!grammar::accepts(&executor, &[mixed], &|| false));
    let zero = executor.ctx.terms.mk_bitvec(0.into(), 4);
    let free_root = executor.ctx.terms.mk_eq(free, zero);
    assert!(grammar::accepts(&executor, &[free_root], &|| false));
    let quantified = executor
        .ctx
        .terms
        .mk_forall(vec![("bound".into(), Sort::bitvec(4))], free_root);
    assert!(!grammar::accepts(&executor, &[quantified], &|| false));
    let let_root = executor
        .ctx
        .terms
        .mk_let(vec![("bound".into(), free)], free_root);
    assert!(!grammar::accepts(&executor, &[let_root], &|| false));
    let array = executor.ctx.terms.mk_fresh_named_var(
        "outside_array",
        Sort::array(Sort::bitvec(4), Sort::bitvec(4)),
    );
    let array_eq =
        executor
            .ctx
            .terms
            .mk_app_structural(Symbol::Named("=".into()), [array, array], Sort::Bool);
    assert!(!grammar::accepts(&executor, &[array_eq], &|| false));
    let future = TermId(u32::try_from(executor.ctx.terms.len() + 1).expect("small test DAG"));
    let forward =
        executor
            .ctx
            .terms
            .mk_app_structural(Symbol::Named("not".into()), [future], Sort::Bool);
    let child = executor
        .ctx
        .terms
        .mk_fresh_named_var("future_child", Sort::Bool);
    assert_eq!(child, future);
    assert!(!grammar::accepts(&executor, &[forward], &|| false));
    // Metadata ownership, not the spelling '=' alone, decides builtin use.
    let shadow = executor
        .ctx
        .terms
        .mk_fresh_named_var("shadow_eq", Sort::Bool);
    executor.ctx.register_symbol("=".into(), shadow, Sort::Bool);
    assert!(!grammar::accepts(&executor, &[free_root], &|| false));
}

#[test]
fn native_satisfiable_scope_cannot_adopt_a_foreign_contradiction() {
    let (mut executor, roots) = fixture();
    executor.ctx.assertions = vec![roots[0]];
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    // An unrelated working assertion is never added to authenticated roots.
    executor.ctx.assertions.push(roots[1]);
    unchanged_refusal(&mut executor);
    assert!(native_offer_recorded(&executor));
}

#[test]
fn native_original_stops_and_source_debits_do_not_renew() {
    for deadline in [false, true] {
        let (mut executor, _) = fixture();
        if deadline {
            executor.set_deadline(Some(ay_core::time::Instant::now()));
        } else {
            executor.set_solve_controls(Some(Arc::new(AtomicBool::new(true))), None);
        }
        unchanged_refusal(&mut executor);
        assert_eq!(
            executor.certification_stop(),
            Some(if deadline {
                EnvelopeStop::Backstop
            } else {
                EnvelopeStop::Interrupt
            })
        );
    }
    let (mut executor, _) = fixture();
    // The first metadata visit consumes the final unit, then the unchanged
    // authenticated-scope precharge declines. Neither return nor retry renews it.
    executor.proof_source_work.set_remaining_for_test(1);
    unchanged_refusal(&mut executor);
    assert_eq!(executor.proof_source_work.remaining_for_test(), 0);
    unchanged_refusal(&mut executor);
    assert_eq!(executor.proof_source_work.remaining_for_test(), 0);
}

#[test]
fn native_route_does_not_replace_a_complete_incumbent() {
    let (mut executor, _) = fixture();
    let mut proof = provisional();
    assert!(executor.try_authenticated_native_bv_refutation(&mut proof));
    executor.begin_evaluation_decision();
    let before = format!("{:?}", proof.steps);
    assert!(!executor.try_authenticated_native_bv_refutation(&mut proof));
    assert_eq!(format!("{:?}", proof.steps), before);
    assert!(!native_offer_recorded(&executor));
}

#[test]
fn native_one_shot_original_stop_stays_refused_across_return_and_retry() {
    use std::sync::atomic::Ordering;
    let (mut executor, _) = fixture();
    let armed = Arc::new(AtomicBool::new(true));
    let original = Arc::clone(&armed);
    let _scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        original.swap(false, Ordering::SeqCst)
    }));
    unchanged_refusal(&mut executor);
    assert!(
        !armed.load(Ordering::SeqCst),
        "the original one-shot was consumed"
    );
    assert_eq!(executor.certification_stop(), Some(EnvelopeStop::Caller));
    unchanged_refusal(&mut executor);
    assert!(executor.evaluation_stop_origin().is_some());
}

#[test]
fn native_retry_key_preserves_exact_epoch_scope_and_does_not_record_a_grammar_decline() {
    let (mut executor, roots) = fixture();
    let old_attempt = executor.evaluation_attempt();
    let old_scope = NativeBvRefutationScope::capture(&executor).expect("authenticated scope");
    assert!(old_attempt.begin_native_bv_refutation(old_scope.clone()));
    assert!(old_attempt.native_bv_refutation_attempted(&old_scope));
    assert!(!old_attempt.begin_native_bv_refutation(old_scope.clone()));

    // Same exact root IDs and entry stamps, but a different actual public
    // authority token: even a deliberately retained old attempt cannot match.
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    let current = NativeBvRefutationScope::capture(&executor).expect("fresh public scope");
    assert!(!old_scope.matches(&current));
    assert!(!old_attempt.native_bv_refutation_attempted(&current));

    let int = executor
        .ctx
        .terms
        .mk_fresh_named_var("grammar_int", Sort::Int);
    let bad = executor.ctx.terms.mk_app_structural(
        Symbol::Named("=".into()),
        [int, roots[0]],
        Sort::Bool,
    );
    executor.ctx.assertions = vec![bad];
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    let declined_attempt = executor.evaluation_attempt();
    let declined_scope =
        NativeBvRefutationScope::capture(&executor).expect("authenticated bad scope");
    let recorded_before = declined_attempt.native_bv_refutation_count();
    unchanged_refusal(&mut executor);
    assert_eq!(
        declined_attempt.native_bv_refutation_count(),
        recorded_before
    );
    assert!(!declined_attempt.native_bv_refutation_attempted(&declined_scope));
    executor.ctx.assertions = roots;
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    let valid = NativeBvRefutationScope::capture(&executor).expect("newly valid native scope");
    assert!(!declined_attempt.native_bv_refutation_attempted(&valid));
    let mut proof = provisional();
    assert!(executor.try_authenticated_native_bv_refutation(&mut proof));
}

#[test]
fn native_empty_and_over_cap_roots_do_not_record_a_producer_offer() {
    let (mut executor, roots) = fixture();
    executor.ctx.assertions.clear();
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    unchanged_refusal(&mut executor);
    assert_eq!(
        executor.evaluation_attempt().native_bv_refutation_count(),
        0
    );
    executor.ctx.assertions = vec![roots[0]; 65];
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    unchanged_refusal(&mut executor);
    assert_eq!(
        executor.evaluation_attempt().native_bv_refutation_count(),
        0
    );
}

#[test]
fn retained_native_sentinels_use_authenticated_roots_and_share_the_retry_key() {
    let mut executor = Executor::new();
    let x = executor
        .ctx
        .register_native_global_constant("retained_native_x".into(), Sort::bitvec(4));
    let zero = executor.ctx.terms.mk_bitvec(0.into(), 4);
    let one = executor.ctx.terms.mk_bitvec(1.into(), 4);
    let a = executor.ctx.terms.mk_eq(x, zero);
    let b = executor.ctx.terms.mk_eq(x, one);
    for root in [a, b] {
        executor.ctx.add_assertion_with_parsed(
            root,
            ay_frontend::command::Term::Symbol(
                crate::executor::NATIVE_API_ASSERTION_PLACEHOLDER.to_string(),
            ),
        );
    }
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    assert_ne!(executor.ctx.assertions_parsed(), []);
    assert_eq!(
        executor.native_bv_source_kind(&|| false),
        Some(NativeAssertionSurfaces::Native)
    );
    let mut proof = provisional();
    assert!(executor.try_authenticated_native_bv_refutation(&mut proof));
    assert!(Executor::proof_derives_empty_clause(&proof));
    assert!(executor
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|q| q.is_complete()));
    assert!(executor
        .exact_authored_bv_refutation(|_, _| panic!("no late native retry"))
        .is_none());
    assert_eq!(
        executor.last_proof_raw_original_assertions,
        [] as [TermId; 0]
    );
}

fn restored_named_native_fixture() -> (Executor, Vec<TermId>) {
    let (mut executor, roots) = fixture();
    executor.ctx.assertions.clear();
    for &root in &roots {
        executor.ctx.add_assertion_with_parsed(
            root,
            ay_frontend::command::Term::Symbol(
                crate::executor::NATIVE_API_ASSERTION_PLACEHOLDER.to_string(),
            ),
        );
    }
    executor
        .execute(&Command::SetOption(
            ":produce-unsat-cores".to_string(),
            ay_frontend::sexp::SExpr::True,
        ))
        .expect("enable core tracking before the public epoch");
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    executor.last_assumptions = Some(roots.clone());
    executor.last_assumption_core = Some(roots.clone());
    executor.last_core_term_to_name = Some(
        roots
            .iter()
            .enumerate()
            .map(|(index, &root)| (root, format!("native_core_{index}")))
            .collect(),
    );
    executor.last_proof = Some(provisional());
    executor.suppress_unsat_proof_reconstruction();
    (executor, roots)
}

#[test]
fn restored_named_native_scope_reproves_exact_originals_and_retains_core() {
    let (mut executor, roots) = restored_named_native_fixture();
    assert!(executor
        .authenticated_unsat_query_roots_for_internal_certificate()
        .is_none());
    let scope = NativeBvRefutationScope::capture(&executor).expect("restored named scope");
    assert_eq!(scope.roots(), roots);
    let core_names = executor.last_core_term_to_name.clone();
    let core = executor.last_assumption_core.clone();
    let tracking = executor.last_assumptions.clone();
    executor.refresh_authenticated_native_bv_refutation_after_named_core_redirect();
    assert!(!executor.last_unsat_proof_reconstruction_suppressed);
    let proof = executor.last_proof.as_ref().expect("new native refutation");
    assert!(executor
        .check_proof_strict_with_datatypes(proof)
        .is_ok_and(|quality| quality.is_complete()));
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(proof, &roots).is_ok());
    assert!(executor.candidate_authored_surface_is_available(proof));
    assert_eq!(executor.last_core_term_to_name, core_names);
    assert_eq!(executor.last_assumption_core, core);
    assert_eq!(executor.last_assumptions, tracking);
    assert!(native_offer_recorded(&executor));
}

#[test]
fn trust_accepting_reconfirmation_does_not_offer_the_native_refresh() {
    let (mut executor, _) = restored_named_native_fixture();
    executor.trust_accepting_reconfirmation = true;
    assert!(executor.skips_trust_elimination_repairs());
    let proof = format!("{:?}", executor.last_proof.as_ref().unwrap().steps);
    let core = executor.last_assumption_core.clone();
    executor.refresh_authenticated_native_bv_refutation_after_named_core_redirect();
    assert_eq!(
        format!("{:?}", executor.last_proof.as_ref().unwrap().steps),
        proof
    );
    assert_eq!(executor.last_assumption_core, core);
    assert!(executor.last_unsat_proof_reconstruction_suppressed);
    assert_eq!(
        executor.evaluation_attempt().native_bv_refutation_count(),
        0
    );
}

#[test]
fn restored_native_refresh_refuses_missing_names_foreign_tracking_and_changed_scope() {
    for mutation in 0..3 {
        let (mut executor, roots) = restored_named_native_fixture();
        match mutation {
            0 => executor.last_core_term_to_name = None,
            1 => {
                let foreign = executor.ctx.terms.mk_fresh_named_var("foreign", Sort::Bool);
                executor.last_assumptions = Some(vec![foreign]);
                executor
                    .last_core_term_to_name
                    .as_mut()
                    .unwrap()
                    .insert(foreign, "foreign_label".into());
            }
            _ => executor.ctx.assertions = roots[..1].to_vec(),
        }
        assert!(NativeBvRefutationScope::capture(&executor).is_none());
        let before = format!("{:?}", executor.last_proof.as_ref().unwrap().steps);
        executor.refresh_authenticated_native_bv_refutation_after_named_core_redirect();
        assert_eq!(
            format!("{:?}", executor.last_proof.as_ref().unwrap().steps),
            before
        );
        assert!(executor.last_unsat_proof_reconstruction_suppressed);
        assert_eq!(
            executor.evaluation_attempt().native_bv_refutation_count(),
            0
        );
    }
}

#[test]
fn native_only_misaligned_source_cannot_fall_back_to_legacy_roots() {
    let (mut executor, roots) = fixture();
    // Retained parsed rows are a prefix of the current assertion stack. Start
    // empty before adding native surfaces, rather than accidentally creating
    // a retention gap behind the fixture's pre-existing bare assertions.
    executor.ctx.assertions.clear();
    // Source inventory mismatch: native rows authenticate a different ordering
    // from this query's frozen original assertions. This is no parsed fallback.
    for &root in roots.iter().rev() {
        executor.ctx.add_assertion_with_parsed(
            root,
            ay_frontend::command::Term::Symbol(
                crate::executor::NATIVE_API_ASSERTION_PLACEHOLDER.to_string(),
            ),
        );
    }
    assert_eq!(executor.ctx.assertions_parsed().len(), roots.len());
    assert!(executor.ctx.assertions_parsed().iter().all(
        |surface| matches!(surface, ay_frontend::command::Term::Symbol(name)
            if name == crate::executor::NATIVE_API_ASSERTION_PLACEHOLDER)
    ));
    executor.ctx.assertions = roots.clone();
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    assert_eq!(
        executor.authenticated_unsat_query_roots_for_internal_certificate(),
        Some(roots)
    );
    assert_eq!(
        executor.native_bv_source_kind(&|| false),
        Some(NativeAssertionSurfaces::Unavailable)
    );
    unchanged_refusal(&mut executor);
    assert!(executor
        .exact_authored_bv_refutation(|_, _| panic!("no native fallback"))
        .is_none());
}
