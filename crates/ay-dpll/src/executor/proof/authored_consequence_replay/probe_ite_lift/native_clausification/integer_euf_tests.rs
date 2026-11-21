// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

struct MixedFixture {
    exec: Executor,
    proof: Proof,
    roots: Vec<TermId>,
}

fn app(terms: &mut ay_core::TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(name), args, sort)
}

/// The captured parity cut and affine transfer preserve their original input.
/// A stronger arithmetic producer may also establish the affine transfer;
/// a genuinely uninterpreted predicate variant is tested separately below.
fn mixed_fixture(upper: i64) -> MixedFixture {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let t = &mut exec.ctx.terms;
    let x = t.mk_var("mixed_x", Sort::Int);
    let alias = t.mk_var("mixed_alias", Sort::Int);
    let zero = t.mk_int(0.into());
    let two = t.mk_int(2.into());
    let minus_two = t.mk_int((-2).into());
    let upper = t.mk_int(upper.into());
    let x2 = app(t, "+", &[x, two], Sort::Int);
    let q0 = app(t, "mixed_q", &[x, two], Sort::Int);
    let q2 = app(t, "mixed_q", &[x2, two], Sort::Int);
    let nq0 = app(t, "*", &[q0, minus_two], Sort::Int);
    let nq2 = app(t, "*", &[q2, minus_two], Sort::Int);
    let r0 = app(t, "+", &[x, nq0], Sort::Int);
    let r2 = app(t, "+", &[x, nq2, two], Sort::Int);
    let alias_eq = t.mk_eq(alias, r2);
    let alias_nonpositive = app(t, "<=", &[alias, zero], Sort::Bool);
    let alias_positive = t.mk_not_raw(alias_nonpositive);
    let nonpositive = app(t, "<=", &[r2, zero], Sort::Bool);
    let positive = t.mk_not_raw(nonpositive);
    let even = t.mk_eq(zero, r0);
    let bounded = app(t, "<=", &[r2, upper], Sort::Bool);
    let not_alias_eq = t.mk_not_raw(alias_eq);
    let not_even = t.mk_not_raw(even);
    let not_bounded = t.mk_not_raw(bounded);
    let bound = t.mk_var("mixed_irrelevant", Sort::Int);
    let reflexive = app(t, "=", &[bound, bound], Sort::Bool);
    let universal = t.mk_forall(vec![("mixed_irrelevant".to_owned(), Sort::Int)], reflexive);

    let mut proof = Proof::new();
    let eq = proof.add_assume(alias_eq, None);
    let positive_alias = proof.add_assume(alias_positive, None);
    let even_assume = proof.add_assume(even, None);
    let bound_assume = proof.add_assume(bounded, None);
    let euf = proof.add_rule_step(
        AletheRule::Trust,
        vec![not_alias_eq, alias_nonpositive, positive],
        Vec::new(),
        Vec::new(),
    );
    let transferred = proof.add_resolution(vec![alias_nonpositive, positive], alias_eq, euf, eq);
    let transferred = proof.add_resolution(
        vec![positive],
        alias_nonpositive,
        transferred,
        positive_alias,
    );
    let cut = proof.add_rule_step(
        AletheRule::Trust,
        vec![nonpositive, not_bounded, not_even],
        Vec::new(),
        Vec::new(),
    );
    let tail = proof.add_resolution(vec![not_bounded, not_even], nonpositive, cut, transferred);
    let tail = proof.add_resolution(vec![not_even], bounded, tail, bound_assume);
    proof.add_resolution(Vec::new(), even, tail, even_assume);
    MixedFixture {
        exec,
        proof,
        // The immutable query includes an irrelevant universal and repeated
        // exact native roots. Optional proof selection cannot erase either.
        roots: vec![universal, alias_eq, alias_positive, even, bounded, even],
    }
}

fn strict_complete(exec: &mut Executor, proof: &Proof) -> bool {
    exec.check_proof_strict_with_datatypes(proof)
        .is_ok_and(|quality| quality.is_complete())
}

fn owned_euf_input() -> MixedFixture {
    let mut f = predicate_fixture(1);
    begin(&mut f.exec, &f.roots, true);
    assert!(f.exec.stage_small_integer_leaves(&mut f.proof) > 0);
    f
}

fn retained_or_pointers(proof: &Proof) -> (usize, usize) {
    proof
        .steps
        .iter()
        .find_map(|step| match step {
            ProofStep::Step {
                rule: AletheRule::Or,
                clause,
                premises,
                ..
            } if !clause.is_empty() && !premises.is_empty() => {
                Some((clause.as_ptr() as usize, premises.as_ptr() as usize))
            }
            _ => None,
        })
        .unwrap()
}

#[test]
fn native_ite_clausification_owned_euf_matches_borrowed_and_moves_named_payloads_whole_carcara() {
    let mut f = owned_euf_input();
    f.proof
        .named_steps
        .insert("source-equality".into(), ay_core::ProofId(0));
    let non_assume = f
        .proof
        .steps
        .iter()
        .position(|step| !matches!(step, ProofStep::Assume(_)))
        .unwrap();
    f.proof.named_steps.insert(
        "not-an-assumption".into(),
        ay_core::ProofId(non_assume as u32),
    );
    f.proof
        .named_steps
        .insert("foreign-name-id".into(), ay_core::ProofId(u32::MAX));
    let row_pointers = retained_or_pointers(&f.proof);
    let name_pointer = f
        .proof
        .named_steps
        .keys()
        .find(|name| name.as_str() == "source-equality")
        .unwrap()
        .as_ptr() as usize;
    let name_allocation = f.proof.named_steps.allocation_size();
    let borrowed = f
        .exec
        .build_generic_euf_leaf_candidate(&f.proof, MAX_NATIVE_PAYLOAD)
        .unwrap();
    let budget = RepairBudget::new(&f.exec);
    let owner = budget.clone();
    let owned = f
        .exec
        .build_generic_euf_leaf_candidate_owned_with_admission(
            f.proof,
            MAX_NATIVE_PAYLOAD,
            move |work, bytes| owner.pay(work, bytes),
        )
        .unwrap();
    assert_eq!(owned, borrowed, "same planner, emitted rules and remapping");
    assert_eq!(retained_or_pointers(&owned), row_pointers);
    assert_eq!(owned.named_steps.allocation_size(), name_allocation);
    assert_eq!(owned.named_steps.len(), 1);
    assert_eq!(
        owned.named_steps.keys().next().unwrap().as_ptr() as usize,
        name_pointer
    );
    assert!(strict_complete(&mut f.exec, &owned));
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&owned, &f.roots).is_ok());
    let wire = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &owned,
        &f.exec.ctx.terms,
        &f.roots,
        None,
    )
    .unwrap();
    let mut problem = "(set-logic AUFLIA)\n(declare-const mixed_x Int)\n(declare-const mixed_alias Int)\n(declare-fun mixed_q (Int Int) Int)\n(declare-fun mixed_p (Int) Bool)\n".to_owned();
    for &root in &f.roots {
        problem.push_str(&format!(
            "(assert {})\n",
            ay_proof::format_term_alethe(&f.exec.ctx.terms, root)
        ));
    }
    problem.push_str("(check-sat)\n");
    assert_eq!(
        external_check("owned-euf-original", &problem, &wire)
            .lines()
            .last(),
        Some("valid")
    );
    let premise = ay_proof::format_term_alethe(&f.exec.ctx.terms, f.roots[2]);
    let forged = problem.replacen(
        &format!("(assert {premise})\n"),
        &format!("(assert (not {premise}))\n"),
        1,
    );
    assert_ne!(forged, problem);
    let refusal = external_check("owned-euf-forged-original", &forged, &wire);
    assert_ne!(refusal.lines().last(), Some("valid"));
    assert!(refusal.to_lowercase().contains("assum"), "{refusal}");
}

#[test]
fn native_ite_clausification_owned_euf_moves_wide_retained_vectors_and_text_under_same_grant() {
    let mut f = owned_euf_input();
    let final_step = f.proof.steps.pop().unwrap();
    let text = "owned-retained-".repeat(5000);
    let args = vec![f.roots[1]; 40_000];
    let text_pointer = text.as_ptr() as usize;
    let args_pointer = args.as_ptr() as usize;
    let wide = f
        .proof
        .add_rule_step(AletheRule::Custom(text), vec![f.roots[1]], vec![], args);
    f.proof.add_step(final_step);
    // These are already-owned proof DATA. The deliberately unsupported unused
    // Custom row can never grant strict authority; this tests copy admission.
    let borrowed_budget = RepairBudget::new(&f.exec);
    let owner = borrowed_budget.clone();
    assert!(f
        .exec
        .build_generic_euf_leaf_candidate_with_admission(
            &f.proof,
            MAX_NATIVE_PAYLOAD,
            move |work, bytes| owner.pay(work, bytes)
        )
        .is_none());
    assert!(
        !borrowed_budget.pay(0, 0),
        "the unchanged borrowed deep-copy fee refuses"
    );
    let owned_budget = RepairBudget::new(&f.exec);
    let owner = owned_budget.clone();
    let candidate = f
        .exec
        .build_generic_euf_leaf_candidate_owned_with_admission(
            f.proof,
            MAX_NATIVE_PAYLOAD,
            move |work, bytes| owner.pay(work, bytes),
        )
        .unwrap();
    assert!(owned_budget.pay(0, 0));
    let retained = candidate
        .steps
        .iter()
        .find_map(|step| match step {
            ProofStep::Step {
                rule: AletheRule::Custom(name),
                args,
                ..
            } => Some((name, args)),
            _ => None,
        })
        .unwrap();
    assert_eq!(retained.0.as_ptr() as usize, text_pointer);
    assert_eq!(retained.1.as_ptr() as usize, args_pointer);
    assert_eq!(retained.1.len(), 40_000);
    let _ = wide;
    assert!(
        !strict_complete(&mut f.exec, &candidate),
        "moving unsupported data never promotes it"
    );
}

#[test]
fn native_ite_clausification_owned_euf_no_plan_preserves_owned_container() {
    let mut exec = Executor::new();
    let atom = exec.ctx.terms.mk_var("owned_no_plan", Sort::Bool);
    let mut proof = Proof::new();
    proof.add_assume(atom, Some("kept".to_owned()));
    let rows = proof.steps.as_ptr();
    let name = proof.named_steps.keys().next().unwrap().as_ptr();
    let unchanged = exec
        .build_generic_euf_leaf_candidate_owned_with_admission(proof, MAX_NATIVE_PAYLOAD, |_, _| {
            true
        })
        .unwrap();
    assert_eq!(unchanged.steps.as_ptr(), rows);
    assert_eq!(unchanged.named_steps.keys().next().unwrap().as_ptr(), name);
    assert_eq!(unchanged.named_steps["kept"], ay_core::ProofId(0));
}

#[test]
fn native_ite_clausification_owned_euf_refusal_is_sticky_and_retained_outer_proof_is_untouched() {
    use std::sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    };
    for cancelled in [false, true] {
        let mut f = owned_euf_input();
        let original = f.proof.clone();
        let disposable = f.proof.clone();
        let interrupt = Arc::new(AtomicBool::new(false));
        f.exec.set_interrupt(Arc::clone(&interrupt));
        let budget = RepairBudget::new(&f.exec);
        if !cancelled {
            budget.set_remaining(1_048_576, 1);
        } else {
            interrupt.store(true, Ordering::Relaxed);
        }
        let owner = budget.clone();
        let candidate = f
            .exec
            .build_generic_euf_leaf_candidate_owned_with_admission(
                disposable,
                MAX_NATIVE_PAYLOAD,
                move |work, bytes| owner.pay(work, bytes),
            );
        assert!(candidate.is_none());
        assert_eq!(f.proof, original);
        interrupt.store(false, Ordering::Relaxed);
        assert!(!budget.clone().pay(0, 0));
        assert_eq!(f.exec.proof_original_problem_assertions_slice(), f.roots);
    }
}

#[test]
fn native_ite_clausification_owned_euf_rejects_foreign_premises_and_forged_surface() {
    for bad_surface in [false, true] {
        let mut f = owned_euf_input();
        if bad_surface {
            let mut overrides = ay_core::kani_compat::DetHashMap::default();
            overrides.insert(f.roots[1], "true".to_owned());
            f.exec.last_proof_term_overrides = Some(overrides);
        } else {
            let Some(ProofStep::Resolution { clause1, .. }) = f.proof.steps.last_mut() else {
                panic!("closing resolution")
            };
            *clause1 = ay_core::ProofId(u32::MAX);
        }
        let original = f.proof.clone();
        assert!(f
            .exec
            .build_generic_euf_leaf_candidate(&f.proof, MAX_NATIVE_PAYLOAD)
            .is_none());
        assert!(f
            .exec
            .build_generic_euf_leaf_candidate_owned_with_admission(
                f.proof.clone(),
                MAX_NATIVE_PAYLOAD,
                |_, _| true
            )
            .is_none());
        assert_eq!(f.proof, original);
    }
}

#[test]
fn native_ite_clausification_owned_euf_preflight_charges_repeated_physical_premise_edges() {
    use std::cell::Cell;
    use std::rc::Rc;
    let mut f = owned_euf_input();
    let premise = ay_core::ProofId(0);
    f.proof
        .add_rule_step(AletheRule::Trust, vec![], vec![premise; 4096], vec![]);
    assert!(f.proof.steps.len() < 100);
    let work = Rc::new(Cell::new(0usize));
    let owner = Rc::clone(&work);
    assert!(f
        .exec
        .build_generic_euf_leaf_candidate_owned_with_admission(
            f.proof,
            MAX_NATIVE_PAYLOAD,
            move |amount, _| {
                let next = owner.get().saturating_add(amount);
                owner.set(next);
                next < 1000
            }
        )
        .is_none());
    assert!(
        work.get() >= 1000,
        "physical edges use the caller's original owner"
    );
}

#[test]
fn native_ite_clausification_owned_euf_late_output_cancel_precedes_moves_and_is_sticky() {
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    };
    let mut f = owned_euf_input();
    let original = f.proof.clone();
    let offers = Rc::new(RefCell::new(Vec::new()));
    let seen = Rc::clone(&offers);
    let baseline = RepairBudget::new(&f.exec);
    let owner = baseline.clone();
    f.exec
        .build_generic_euf_leaf_candidate_owned_with_admission(
            f.proof.clone(),
            MAX_NATIVE_PAYLOAD,
            move |work, bytes| {
                if bytes != 0 {
                    seen.borrow_mut().push((work, bytes));
                }
                owner.pay(work, bytes)
            },
        )
        .unwrap();
    let offers = offers.borrow();
    assert_eq!(
        offers.last().unwrap().1,
        f.proof.steps.len() * 2,
        "last backing is the prepaid original-Assume mask"
    );
    let output = offers[offers.len() - 2];
    assert!(output.1 > offers.last().unwrap().1);
    drop(offers);
    let interrupt = Arc::new(AtomicBool::new(false));
    f.exec.set_interrupt(Arc::clone(&interrupt));
    let budget = RepairBudget::new(&f.exec);
    let owner = budget.clone();
    let signal = Arc::clone(&interrupt);
    assert!(f
        .exec
        .build_generic_euf_leaf_candidate_owned_with_admission(
            f.proof.clone(),
            MAX_NATIVE_PAYLOAD,
            move |work, bytes| {
                if (work, bytes) == output {
                    signal.store(true, Ordering::Relaxed);
                }
                owner.pay(work, bytes)
            }
        )
        .is_none());
    assert!(
        interrupt.load(Ordering::Relaxed),
        "reached the actual output preallocation fence"
    );
    interrupt.store(false, Ordering::Relaxed);
    assert!(!budget.pay(0, 0));
    assert_eq!(f.proof, original);
}

#[test]
fn native_ite_clausification_integer_euf_composes_before_one_complete_gate() {
    let _diagnostics = diagnostic_flags();
    let mut f = mixed_fixture(1);
    begin(&mut f.exec, &f.roots, true);
    let mut integer_only = f.proof.clone();
    assert!(f.exec.stage_small_integer_leaves(&mut integer_only) > 0);
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&integer_only, &f.roots).is_ok());
    let euf_only = f
        .exec
        .build_generic_euf_leaf_candidate(&f.proof, MAX_NATIVE_PAYLOAD)
        .expect("the exact predicate transfer is independently derivable");
    assert!(!strict_complete(&mut f.exec, &euf_only));
    assert!(f
        .exec
        .replace_with_checked_small_integer_leaves(&mut f.proof));
    assert!(strict_complete(&mut f.exec, &f.proof));
    assert_eq!(f.exec.proof_original_problem_assertions_slice(), f.roots);
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&f.proof, &f.roots).is_ok());
    assert!(f.proof.steps.iter().all(|step| !matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::Trust | AletheRule::Hole,
            ..
        }
    )));
    let document = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &f.proof,
        &f.exec.ctx.terms,
        &f.roots,
        None,
    )
    .expect("the whole mixed derivation exports");
    let prefix = "(set-logic AUFLIA)\n(declare-const mixed_x Int)\n(declare-const mixed_alias Int)\n(declare-fun mixed_q (Int Int) Int)\n";
    let assertions: String = f
        .roots
        .iter()
        .map(|&root| {
            format!(
                "(assert {})\n",
                ay_proof::format_term_alethe(&f.exec.ctx.terms, root)
            )
        })
        .collect();
    let problem = format!("{prefix}{assertions}(check-sat)\n");
    assert_eq!(
        external_check("mixed-integer-euf", &problem, &document)
            .lines()
            .last(),
        Some("valid")
    );
}

/// Replace only the affine guard transfer with a real UF predicate transfer.
/// The arithmetic cut, exact original equality and original bounds stay the
/// same. Its predicate is intentionally opaque to the integer recognizer.
fn predicate_fixture(upper: i64) -> MixedFixture {
    let mut f = mixed_fixture(upper);
    let alias_eq = f.roots[1];
    let even = f.roots[3];
    let bounded = f.roots[4];
    let TermData::App(_, args) = f.exec.ctx.terms.get(alias_eq) else {
        unreachable!()
    };
    let (alias, value) = (args[0], args[1]);
    let cut = f
        .proof
        .steps
        .iter()
        .find_map(|step| match step {
            ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                ..
            } if clause.len() == 3
                && clause.iter().any(
                    |&lit| matches!(f.exec.ctx.terms.get(lit),TermData::Not(inner) if *inner==even),
                ) =>
            {
                Some(clause.clone())
            }
            _ => None,
        })
        .unwrap();
    let nonpositive = cut[0];
    let positive = f.exec.ctx.terms.mk_not_raw(nonpositive);
    let p_alias = app(&mut f.exec.ctx.terms, "mixed_p", &[alias], Sort::Bool);
    let p_value = app(&mut f.exec.ctx.terms, "mixed_p", &[value], Sort::Bool);
    let not_p_alias = f.exec.ctx.terms.mk_not_raw(p_alias);
    let not_p_value = f.exec.ctx.terms.mk_not_raw(p_value);
    let not_eq = f.exec.ctx.terms.mk_not_raw(alias_eq);
    let implication = app(
        &mut f.exec.ctx.terms,
        "or",
        &[not_p_value, positive],
        Sort::Bool,
    );
    let mut proof = Proof::new();
    let eq_unit = proof.add_assume(alias_eq, None);
    let alias_unit = proof.add_assume(p_alias, None);
    let implication_unit = proof.add_assume(implication, None);
    let even_unit = proof.add_assume(even, None);
    let bound_unit = proof.add_assume(bounded, None);
    let euf = proof.add_rule_step(
        AletheRule::Trust,
        vec![not_eq, not_p_alias, p_value],
        vec![],
        vec![],
    );
    let euf = proof.add_resolution(vec![not_p_alias, p_value], alias_eq, euf, eq_unit);
    let value_unit = proof.add_resolution(vec![p_value], p_alias, euf, alias_unit);
    let expansion = proof.add_rule_step(
        AletheRule::Or,
        vec![not_p_value, positive],
        vec![implication_unit],
        vec![],
    );
    let positive_unit = proof.add_resolution(vec![positive], p_value, value_unit, expansion);
    let cut_unit = proof.add_rule_step(AletheRule::Trust, cut.clone(), vec![], vec![]);
    let tail = proof.add_resolution(vec![cut[1], cut[2]], nonpositive, cut_unit, positive_unit);
    let tail = proof.add_resolution(vec![cut[2]], bounded, tail, bound_unit);
    proof.add_resolution(vec![], even, tail, even_unit);
    f.roots = vec![
        f.roots[0],
        alias_eq,
        p_alias,
        implication,
        even,
        bounded,
        even,
    ];
    f.proof = proof;
    f
}

#[test]
fn native_ite_clausification_integer_euf_opaque_predicate_requires_atomic_composition() {
    for upper in [1, 2] {
        let mut f = predicate_fixture(upper);
        begin(&mut f.exec, &f.roots, true);
        if upper == 2 {
            let original = f.proof.clone();
            assert!(!f
                .exec
                .replace_with_checked_small_integer_leaves(&mut f.proof));
            assert_eq!(f.proof, original);
            continue;
        }
        let mut integer = f.proof.clone();
        assert!(f.exec.stage_small_integer_leaves(&mut integer) > 0);
        assert!(!strict_complete(&mut f.exec, &integer));
        let euf = f
            .exec
            .build_generic_euf_leaf_candidate(&f.proof, MAX_NATIVE_PAYLOAD)
            .unwrap();
        assert!(!strict_complete(&mut f.exec, &euf));
        assert!(f
            .exec
            .replace_with_checked_small_integer_leaves(&mut f.proof));
        assert!(strict_complete(&mut f.exec, &f.proof));
        assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&f.proof, &f.roots).is_ok());
        let wire = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
            &f.proof,
            &f.exec.ctx.terms,
            &f.roots,
            None,
        )
        .unwrap();
        let mut problem="(set-logic AUFLIA)\n(declare-const mixed_x Int)\n(declare-const mixed_alias Int)\n(declare-fun mixed_q (Int Int) Int)\n(declare-fun mixed_p (Int) Bool)\n".to_owned();
        for &root in &f.roots {
            problem.push_str(&format!(
                "(assert {})\n",
                ay_proof::format_term_alethe(&f.exec.ctx.terms, root)
            ));
        }
        problem.push_str("(check-sat)\n");
        assert_eq!(
            external_check("mixed-int-opaque-predicate", &problem, &wire)
                .lines()
                .last(),
            Some("valid")
        );
    }
}

#[test]
fn native_ite_clausification_integer_euf_preserves_scope_epoch_and_sat_refusal() {
    for mutation in 0..4 {
        let mut f = mixed_fixture(if mutation == 3 { 2 } else { 1 });
        let mut roots = f.roots.clone();
        if mutation == 0 {
            roots.remove(1);
        }
        begin(&mut f.exec, &roots, true);
        if mutation == 1 {
            f.exec.begin_public_solve(false);
        }
        if mutation == 2 {
            f.exec
                .set_interrupt(std::sync::Arc::new(std::sync::atomic::AtomicBool::new(
                    true,
                )));
        }
        let original = f.proof.clone();
        assert!(
            !f.exec
                .replace_with_checked_small_integer_leaves(&mut f.proof),
            "mutation {mutation}"
        );
        assert_eq!(f.proof, original);
    }
}

#[test]
fn native_ite_clausification_integer_euf_planning_stop_is_sticky_within_a_dag() {
    use crate::executor::proof_trust_surgery_provenance::SurgeryPlanningBudget;
    use std::sync::{
        atomic::{AtomicBool, AtomicUsize, Ordering},
        Arc,
    };
    let stop = Arc::new(AtomicBool::new(false));
    let callback = Arc::clone(&stop);
    let mut planning = SurgeryPlanningBudget::with_stop(move || callback.load(Ordering::Acquire));
    assert!(planning.spend_work(1));
    stop.store(true, Ordering::Release);
    assert!(!planning.spend_work(1));
    stop.store(false, Ordering::Release);
    assert!(!planning.spend_work(1));

    let mut terms = ay_core::TermStore::new();
    let leaf = terms.mk_var("stop_inside", Sort::Int);
    let shared = terms.mk_app(Symbol::named("stop_pair"), vec![leaf; 32], Sort::Int);
    let polls = Arc::new(AtomicUsize::new(0));
    let callback = Arc::clone(&polls);
    let mut planning =
        SurgeryPlanningBudget::with_stop(move || callback.fetch_add(1, Ordering::AcqRel) >= 3);
    assert!(!planning.spend_terms(&terms, &[shared]));
    assert!(polls.load(Ordering::Acquire) >= 4);
}
