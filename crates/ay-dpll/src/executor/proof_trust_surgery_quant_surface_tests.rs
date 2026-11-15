// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{AletheRule, Proof, ProofId, Sort, Symbol, TermData, TermId};
use ay_frontend::command::{Command, Constant, Sort as FrontendSort, Term as FrontendTerm};

use super::{QuantSurfaceAuthority, QuantSurfacePlans, MAX_QUANT_SURFACE_CHAINS};
use crate::executor::proof_trust_surgery::AssumePlan;
use crate::executor::proof_trust_surgery_provenance::OriginalSourceIndex;
use crate::executor::{EmatchingProofRecord, Executor};

fn declare_fixture_const(executor: &mut Executor, name: &str, sort: FrontendSort) -> TermId {
    executor
        .ctx
        .process_command(&Command::DeclareConst(name.to_string(), sort))
        .expect("fixture declaration succeeds");
    executor
        .ctx
        .elaborate_surface_subterm(&FrontendTerm::Symbol(name.to_string()))
        .expect("declared fixture symbol elaborates")
}

fn direct_forall_fixture() -> (Executor, FrontendTerm, TermId, TermId) {
    let mut executor = Executor::new();
    let _y = declare_fixture_const(
        &mut executor,
        "quant_surface_y",
        FrontendSort::Simple("Int".to_string()),
    );
    let parsed = FrontendTerm::Forall(
        vec![(
            "quant_surface_x".to_string(),
            FrontendSort::Simple("Int".to_string()),
        )],
        Box::new(FrontendTerm::App(
            "<".to_string(),
            vec![
                FrontendTerm::Symbol("quant_surface_x".to_string()),
                FrontendTerm::Symbol("quant_surface_y".to_string()),
            ],
        )),
    );
    let forall = executor
        .ctx
        .elaborate_surface_subterm(&parsed)
        .expect("forall fixture elaborates");
    let ground = FrontendTerm::App(
        "<".to_string(),
        vec![
            FrontendTerm::Const(Constant::Numeral("0".to_string())),
            FrontendTerm::Symbol("quant_surface_y".to_string()),
        ],
    );
    let target = executor
        .ctx
        .elaborate_surface_subterm(&ground)
        .expect("ground fixture elaborates");
    (executor, parsed, forall, target)
}

struct DirectNegativeQuantFixture {
    executor: Executor,
    proof: Proof,
    originals: Vec<(TermId, FrontendTerm)>,
    forall: TermId,
    forall_assume: ProofId,
    negative: ProofId,
}

fn direct_negative_quant_fixture() -> DirectNegativeQuantFixture {
    let (mut executor, parsed_forall, forall, instance) = direct_forall_fixture();
    let zero = executor.ctx.terms.mk_int(0.into());
    let parsed_support = FrontendTerm::App(
        "<=".to_string(),
        vec![
            FrontendTerm::Symbol("quant_surface_y".to_string()),
            FrontendTerm::Const(Constant::Numeral("0".to_string())),
        ],
    );
    let support = executor
        .ctx
        .elaborate_surface_subterm(&parsed_support)
        .expect("conflicting support elaborates");
    executor.ematching_proof_records.push(EmatchingProofRecord {
        assertion_index: 0,
        quantifier: forall,
        binding: vec![zero],
        instance,
    });

    let not_forall = executor.ctx.terms.mk_not_raw(forall);
    let mut proof = Proof::new();
    let forall_assume = proof.add_assume(forall, None);
    let negative = proof.add_rule_step(AletheRule::Trust, vec![not_forall], Vec::new(), Vec::new());
    DirectNegativeQuantFixture {
        executor,
        proof,
        originals: vec![(forall, parsed_forall), (support, parsed_support)],
        forall,
        forall_assume,
        negative,
    }
}

#[test]
fn standalone_quant_surface_audit_accepts_exact_forall_instance() {
    let (mut executor, parsed, forall, target) = direct_forall_fixture();
    let value = executor.ctx.terms.mk_int(0.into());
    let chain = executor
        .build_quant_instance_chain(&parsed, &[value], target)
        .expect("exact instance chain");
    let mut instances = HashMap::default();
    instances.insert(target, vec![value]);
    let mut assumes = HashMap::default();
    assumes.insert(
        0,
        AssumePlan::QuantExpansion {
            forall_term: forall,
            assertion_index: 0,
            conjs: vec![target],
            instances,
        },
    );
    let mut chains = HashMap::default();
    chains.insert((0, 0), chain);
    let originals = vec![(forall, parsed)];
    let index = OriginalSourceIndex::new(&originals);
    let mut authority = QuantSurfaceAuthority::new(&index);

    assert!(executor
        .prepare_quant_surface_overrides(
            &mut authority,
            &Proof::new(),
            &[],
            &originals,
            QuantSurfacePlans {
                assumes: &assumes,
                chains: &chains,
                consequences: &HashMap::default(),
                negations: &HashMap::default(),
            },
        )
        .is_some());
    let TermData::Forall(_, body, _) = executor.ctx.terms.get(forall) else {
        panic!("fixture is a forall");
    };
    assert!(authority.authenticated_assume_roots().contains(&forall));
    assert!(!authority.authenticated_assume_roots().contains(body));
}

#[test]
fn standalone_quant_surface_audit_rejects_override_in_copied_rule() {
    let (mut executor, parsed, forall, target) = direct_forall_fixture();
    let value = executor.ctx.terms.mk_int(0.into());
    let chain = executor
        .build_quant_instance_chain(&parsed, &[value], target)
        .expect("exact instance chain");
    let mut instances = HashMap::default();
    instances.insert(target, vec![value]);
    let mut assumes = HashMap::default();
    assumes.insert(
        0,
        AssumePlan::QuantExpansion {
            forall_term: forall,
            assertion_index: 0,
            conjs: vec![target],
            instances,
        },
    );
    let mut chains = HashMap::default();
    chains.insert((0, 0), chain);
    let originals = vec![(forall, parsed)];
    let mut proof = Proof::new();
    proof.add_assume(forall, None);
    proof.add_rule_step(AletheRule::EqReflexive, vec![forall], vec![], vec![]);
    let index = OriginalSourceIndex::new(&originals);
    let mut authority = QuantSurfaceAuthority::new(&index);

    assert!(executor
        .prepare_quant_surface_overrides(
            &mut authority,
            &proof,
            &[true, true],
            &originals,
            QuantSurfacePlans {
                assumes: &assumes,
                chains: &chains,
                consequences: &HashMap::default(),
                negations: &HashMap::default(),
            },
        )
        .is_none());
}

#[test]
fn standalone_quant_surface_audit_caps_all_instance_chains_together() {
    let (mut executor, parsed, forall, target) = direct_forall_fixture();
    let value = executor.ctx.terms.mk_int(0.into());
    let mut instances = HashMap::default();
    instances.insert(target, vec![value]);
    let mut assumes = HashMap::default();
    assumes.insert(
        0,
        AssumePlan::QuantExpansion {
            forall_term: forall,
            assertion_index: 0,
            conjs: vec![target],
            instances,
        },
    );
    let mut chains = HashMap::default();
    for position in 0..=MAX_QUANT_SURFACE_CHAINS {
        let chain = executor
            .build_quant_instance_chain(&parsed, &[value], target)
            .expect("exact instance chain");
        chains.insert((0, position), chain);
    }
    let originals = vec![(forall, parsed)];
    let index = OriginalSourceIndex::new(&originals);
    let mut authority = QuantSurfaceAuthority::new(&index);
    assert!(executor
        .prepare_quant_surface_overrides(
            &mut authority,
            &Proof::new(),
            &[],
            &originals,
            QuantSurfacePlans {
                assumes: &assumes,
                chains: &chains,
                consequences: &HashMap::default(),
                negations: &HashMap::default(),
            },
        )
        .is_none());
}

#[test]
fn copied_quant_surface_roles_reject_descendant_assume_and_annotated_resolution() {
    let mut executor = Executor::new();
    let p = executor.ctx.terms.mk_var("quant_copied_p", Sort::Bool);
    let not_p = executor.ctx.terms.mk_not_raw(p);
    let mut overrides = HashMap::default();
    overrides.insert(p, "(= quant_copied_p true)".to_string());
    let empty_assumes = HashMap::default();
    let empty_chains = HashMap::default();
    let empty_consequences = HashMap::default();
    let empty_negations = HashMap::default();
    let plans = QuantSurfacePlans {
        assumes: &empty_assumes,
        chains: &empty_chains,
        consequences: &empty_consequences,
        negations: &empty_negations,
    };

    let mut descendant_assume = Proof::new();
    descendant_assume.add_assume(not_p, None);
    assert!(!super::copied::copied_quant_rendering_roles_are_static(
        &descendant_assume,
        &[true],
        &plans,
        &executor.ctx.terms,
        &overrides,
        &HashSet::default(),
    ));

    let mut annotated_resolution = Proof::new();
    annotated_resolution.add_rule_step(AletheRule::Resolution, vec![p], Vec::new(), vec![p]);
    assert!(!super::copied::copied_quant_rendering_roles_are_static(
        &annotated_resolution,
        &[true],
        &plans,
        &executor.ctx.terms,
        &overrides,
        &HashSet::default(),
    ));

    let mut top_level_assume = Proof::new();
    top_level_assume.add_assume(p, None);
    assert!(!super::copied::copied_quant_rendering_roles_are_static(
        &top_level_assume,
        &[true],
        &plans,
        &executor.ctx.terms,
        &overrides,
        &HashSet::default(),
    ));
    let mut authenticated = HashSet::default();
    authenticated.insert(p);
    assert!(super::copied::copied_quant_rendering_roles_are_static(
        &top_level_assume,
        &[true],
        &plans,
        &executor.ctx.terms,
        &overrides,
        &authenticated,
    ));

    let high_arity = executor.ctx.terms.mk_app(
        Symbol::named("quant_copied_high_arity"),
        vec![p; 100_001],
        Sort::Bool,
    );
    let mut high_arity_assume = Proof::new();
    high_arity_assume.add_assume(high_arity, None);
    assert!(!super::copied::copied_quant_rendering_roles_are_static(
        &high_arity_assume,
        &[true],
        &plans,
        &executor.ctx.terms,
        &HashMap::default(),
        &HashSet::default(),
    ));
}

#[test]
fn standalone_quant_chain_rejects_deep_authored_body_before_substitution() {
    let mut executor = Executor::new();
    let mut body = FrontendTerm::App(
        "<".to_string(),
        vec![
            FrontendTerm::Symbol("deep_quant_x".to_string()),
            FrontendTerm::Const(Constant::Numeral("1".to_string())),
        ],
    );
    for _ in 0..300 {
        body = FrontendTerm::App("not".to_string(), vec![body]);
    }
    let parsed = FrontendTerm::Forall(
        vec![(
            "deep_quant_x".to_string(),
            FrontendSort::Simple("Int".to_string()),
        )],
        Box::new(body),
    );
    let value = executor.ctx.terms.mk_int(0.into());
    let target = executor.ctx.terms.mk_bool(false);
    assert!(executor
        .build_quant_instance_chain(&parsed, &[value], target)
        .is_none());
}

#[test]
fn live_forall_assume_and_negative_trust_rebuild_end_to_end() {
    let mut fixture = direct_negative_quant_fixture();
    fixture.proof.add_resolution(
        Vec::new(),
        fixture.forall,
        fixture.forall_assume,
        fixture.negative,
    );

    assert!(fixture
        .executor
        .try_rebuild_with_trust_surgery(&mut fixture.proof, &fixture.originals));
    let quality = ay_proof::check_proof_strict(&fixture.proof, &fixture.executor.ctx.terms)
        .expect("rebuilt direct E-matching negation must be strict");
    assert_eq!(quality.trust_count, 0);
}

#[test]
fn quant_source_pivot_remap_does_not_forgive_invalid_conclusion() {
    let mut fixture = direct_negative_quant_fixture();
    fixture.proof.add_resolution(
        vec![fixture.forall],
        fixture.forall,
        fixture.forall_assume,
        fixture.negative,
    );
    let proof_before = format!("{:?}", fixture.proof);
    let overrides_before = fixture.executor.last_proof_term_overrides.clone();

    assert!(!fixture
        .executor
        .try_rebuild_with_trust_surgery(&mut fixture.proof, &fixture.originals));
    assert_eq!(format!("{:?}", fixture.proof), proof_before);
    assert_eq!(fixture.executor.last_proof_term_overrides, overrides_before);
}

/// An IDENTITY quantifier-expansion consequence: the trust leaf `(cl L)` is
/// the folded expansion instance `L` itself (F03 in `ay`'s
/// `provenance_assume_gate_leak2`: 23 of its 25 leaves). The planner used to
/// pair the instance chain with the degenerate lemma `(cl (not L) L)`, which
/// the surface audit's `unique_atoms` guard (c25240fc9) refuses, and that one
/// refusal discarded the WHOLE surgery. The chain alone must now replace the
/// leaf, and the rebuilt proof must be strict and trust-free.
#[test]
fn identity_quant_expansion_consequence_rebuilds_without_a_lemma() {
    use ay_core::{FarkasAnnotation, ProofStep, TheoryLemmaKind};

    let (mut executor, parsed_forall, forall, instance) = direct_forall_fixture();
    let zero = executor.ctx.terms.mk_int(0.into());
    let parsed_support = FrontendTerm::App(
        "<=".to_string(),
        vec![
            FrontendTerm::Symbol("quant_surface_y".to_string()),
            FrontendTerm::Const(Constant::Numeral("0".to_string())),
        ],
    );
    let support = executor
        .ctx
        .elaborate_surface_subterm(&parsed_support)
        .expect("conflicting support elaborates");
    executor
        .quant_expansion_records
        .push(crate::executor::QuantExpansionRecord {
            original: forall,
            assertion_index: 0,
            expanded: instance,
            instances: vec![(vec![zero], instance)],
        });

    let not_instance = executor.ctx.terms.mk_not_raw(instance);
    let not_support = executor.ctx.terms.mk_not_raw(support);
    let mut proof = Proof::new();
    let _forall_assume = proof.add_assume(forall, None);
    let leaf = proof.add_rule_step(AletheRule::Trust, vec![instance], Vec::new(), Vec::new());
    let support_assume = proof.add_assume(support, None);
    let lemma = proof.add_step(ProofStep::TheoryLemma {
        theory: "LRA".to_string(),
        clause: vec![not_instance, not_support],
        farkas: Some(FarkasAnnotation::from_ints(&[1, 1])),
        kind: TheoryLemmaKind::LraFarkas,
        lia: None,
    });
    let unit = proof.add_resolution(vec![not_support], instance, lemma, leaf);
    proof.add_resolution(Vec::new(), support, unit, support_assume);
    let originals = vec![(forall, parsed_forall), (support, parsed_support)];

    assert!(
        executor.try_rebuild_with_trust_surgery(&mut proof, &originals),
        "an identity consequence must not discard the surgery"
    );
    let quality = ay_proof::check_proof_strict(&proof, &executor.ctx.terms)
        .expect("the rebuilt identity-consequence proof must be strict");
    assert_eq!(quality.trust_count, 0);
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::ForallInst,
            ..
        }
    )));
    // No degenerate `(cl (not L) L)` lemma may be emitted for the leaf.
    assert!(!proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma { clause, .. }
            if clause.contains(&instance) && clause.contains(&not_instance)
    )));
}
