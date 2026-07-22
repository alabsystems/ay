// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{
    BoundRefinementRequest, NativeTheoryPropagationProfile, Sort, TermId, TermStore, TheoryLit,
    TheoryPropagation, TheoryResult,
};
use ay_sat::{ExtCheckResult, Extension, SolverContext};
use ay_sat::{Literal, Variable};
use num_bigint::BigInt;
use num_rational::BigRational;

use crate::executor::BoundRefinementReplayKey;

/// Mock theory solver for testing TheoryExtension
struct MockTheory {
    assertions: Vec<(TermId, bool)>,
    push_count: u32,
    pop_count: u32,
    reset_count: u32,
    check_calls: usize,
    check_result: TheoryResult,
    propagations: Vec<TheoryPropagation>,
    pending_bound_refinements: Vec<BoundRefinementRequest>,
    axiom_terms: Vec<(TermId, bool, TermId, bool)>,
    rejected_propagations: Vec<(TermId, u64)>,
    native_theory_propagation_profile: NativeTheoryPropagationProfile,
}

impl MockTheory {
    fn new() -> Self {
        Self {
            assertions: vec![],
            push_count: 0,
            pop_count: 0,
            reset_count: 0,
            check_calls: 0,
            check_result: TheoryResult::Sat,
            propagations: vec![],
            pending_bound_refinements: Vec::new(),
            axiom_terms: Vec::new(),
            rejected_propagations: Vec::new(),
            native_theory_propagation_profile: NativeTheoryPropagationProfile::unsupported(),
        }
    }

    fn with_check_result(mut self, result: TheoryResult) -> Self {
        self.check_result = result;
        self
    }

    fn with_propagations(mut self, props: Vec<TheoryPropagation>) -> Self {
        self.propagations = props;
        self
    }

    fn with_bound_refinements(mut self, refinements: Vec<BoundRefinementRequest>) -> Self {
        self.pending_bound_refinements = refinements;
        self
    }

    fn with_axiom_terms(mut self, axiom_terms: Vec<(TermId, bool, TermId, bool)>) -> Self {
        self.axiom_terms = axiom_terms;
        self
    }

    fn with_native_theory_propagation_profile(
        mut self,
        profile: NativeTheoryPropagationProfile,
    ) -> Self {
        self.native_theory_propagation_profile = profile;
        self
    }
}

impl TheorySolver for MockTheory {
    fn assert_literal(&mut self, literal: TermId, value: bool) {
        self.assertions.push((literal, value));
    }

    fn check(&mut self) -> TheoryResult {
        self.check_calls += 1;
        self.check_result.clone()
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        std::mem::take(&mut self.propagations)
    }

    fn push(&mut self) {
        self.push_count += 1;
    }

    fn pop(&mut self) {
        self.pop_count += 1;
    }

    fn reset(&mut self) {
        self.reset_count += 1;
        self.assertions.clear();
        self.pending_bound_refinements.clear();
        self.rejected_propagations.clear();
    }

    fn take_bound_refinements(&mut self) -> Vec<BoundRefinementRequest> {
        std::mem::take(&mut self.pending_bound_refinements)
    }

    fn generate_bound_axiom_terms(&self) -> Vec<(TermId, bool, TermId, bool)> {
        self.axiom_terms.clone()
    }

    fn native_theory_propagation_profile(&self) -> NativeTheoryPropagationProfile {
        self.native_theory_propagation_profile
    }

    fn mark_propagation_rejected(&mut self, lit: TermId, reason_data: u64) {
        self.rejected_propagations.push((lit, reason_data));
    }
}

/// Simulates theories like LRA that only expose bound refinements during
/// an earlier eager `check()` call and clear the queue on the later final
/// `check()` if the extension did not already preserve them.
struct PropagateOnlyRefinementTheory {
    pending_bound_refinements: Vec<BoundRefinementRequest>,
    check_calls: usize,
}

impl PropagateOnlyRefinementTheory {
    fn new(refinement: BoundRefinementRequest) -> Self {
        Self {
            pending_bound_refinements: vec![refinement],
            check_calls: 0,
        }
    }
}

impl TheorySolver for PropagateOnlyRefinementTheory {
    fn assert_literal(&mut self, _literal: TermId, _value: bool) {}

    fn check(&mut self) -> TheoryResult {
        self.check_calls += 1;
        if self.check_calls > 1 {
            self.pending_bound_refinements.clear();
        }
        TheoryResult::Sat
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        Vec::new()
    }

    fn push(&mut self) {}

    fn pop(&mut self) {
        self.pending_bound_refinements.clear();
    }

    fn reset(&mut self) {
        self.pending_bound_refinements.clear();
    }

    fn take_bound_refinements(&mut self) -> Vec<BoundRefinementRequest> {
        std::mem::take(&mut self.pending_bound_refinements)
    }
}

/// Mock solver context for testing
struct MockContext {
    trail: Vec<Literal>,
    values: HashMap<u32, bool>,
    decision_level: u32,
}

impl MockContext {
    fn new() -> Self {
        Self {
            trail: vec![],
            values: HashMap::default(),
            decision_level: 0,
        }
    }

    fn with_trail(mut self, trail: Vec<Literal>) -> Self {
        for lit in &trail {
            self.values.insert(lit.variable().id(), lit.is_positive());
        }
        self.trail = trail;
        self
    }

    fn with_level(mut self, level: u32) -> Self {
        self.decision_level = level;
        self
    }
}

impl SolverContext for MockContext {
    fn value(&self, var: Variable) -> Option<bool> {
        self.values.get(&var.id()).copied()
    }

    fn decision_level(&self) -> u32 {
        self.decision_level
    }

    fn var_level(&self, _var: Variable) -> Option<u32> {
        Some(0)
    }

    fn trail(&self) -> &[Literal] {
        &self.trail
    }

    fn new_assignments(&self, _last_pos: usize) -> &[Literal] {
        &self.trail
    }
}

type TestSetup = (
    TermStore,
    HashMap<u32, TermId>,
    HashMap<TermId, u32>,
    Vec<TermId>,
    HashSet<TermId>,
    [TermId; 3],
);

fn create_test_setup() -> TestSetup {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);
    let z = terms.mk_var("z", Sort::Bool);

    let var_to_term: HashMap<u32, TermId> = [(1, x), (2, y), (3, z)].into_iter().collect();
    let term_to_var: HashMap<TermId, u32> = [(x, 1), (y, 2), (z, 3)].into_iter().collect();
    let mut theory_atoms = vec![x, y, z];
    theory_atoms.sort_unstable_by_key(|term| term.0);
    let theory_atom_set: HashSet<TermId> = theory_atoms.iter().copied().collect();

    (
        terms,
        var_to_term,
        term_to_var,
        theory_atoms,
        theory_atom_set,
        [x, y, z],
    )
}

#[cfg(test)]
type LraBoundAxiomSetup = (
    TermStore,
    HashMap<u32, TermId>,
    HashMap<TermId, u32>,
    Vec<TermId>,
    HashSet<TermId>,
    [TermId; 2],
);

/// Create a real-arithmetic setup whose validated bound axiom is tautological:
/// `(x >= 0) OR (x <= 0)`.
#[cfg(test)]
fn create_lra_bound_axiom_setup() -> LraBoundAxiomSetup {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::from(BigInt::from(0)));
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_0 = terms.mk_le(x, zero);

    let var_to_term: HashMap<u32, TermId> = [(1, x_ge_0), (2, x_le_0)].into_iter().collect();
    let term_to_var: HashMap<TermId, u32> = [(x_ge_0, 1), (x_le_0, 2)].into_iter().collect();
    let mut theory_atoms = vec![x_ge_0, x_le_0];
    theory_atoms.sort_unstable_by_key(|term| term.0);
    let theory_atom_set: HashSet<TermId> = theory_atoms.iter().copied().collect();

    (
        terms,
        var_to_term,
        term_to_var,
        theory_atoms,
        theory_atom_set,
        [x_ge_0, x_le_0],
    )
}

#[cfg(test)]
type EufTransitivitySetup = (
    TermStore,
    HashMap<u32, TermId>,
    HashMap<TermId, u32>,
    Vec<TermId>,
    HashSet<TermId>,
    [TermId; 3],
);

/// Create an EUF setup over three uninterpreted-sort constants with the three
/// pairwise equality atoms `(= a b)`, `(= b c)`, `(= a c)` mapped to SAT vars
/// 1, 2, 3. Exercises a SEMANTICALLY VALID theory propagation:
/// `a=b ∧ b=c ⊢ a=c` (transitivity), which the propagate path's mandatory
/// semantic-verification gate accepts (`reason ∧ ¬propagated` is EUF-UNSAT).
#[cfg(test)]
fn create_euf_transitivity_setup() -> EufTransitivitySetup {
    let mut terms = TermStore::new();
    let sort = Sort::Uninterpreted("U".to_string());
    let a = terms.mk_var("a", sort.clone());
    let b = terms.mk_var("b", sort.clone());
    let c = terms.mk_var("c", sort);
    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);
    let eq_ac = terms.mk_eq(a, c);

    let var_to_term: HashMap<u32, TermId> =
        [(1, eq_ab), (2, eq_bc), (3, eq_ac)].into_iter().collect();
    let term_to_var: HashMap<TermId, u32> =
        [(eq_ab, 1), (eq_bc, 2), (eq_ac, 3)].into_iter().collect();
    let mut theory_atoms = vec![eq_ab, eq_bc, eq_ac];
    theory_atoms.sort_unstable_by_key(|term| term.0);
    let theory_atom_set: HashSet<TermId> = theory_atoms.iter().copied().collect();

    (
        terms,
        var_to_term,
        term_to_var,
        theory_atoms,
        theory_atom_set,
        [eq_ab, eq_bc, eq_ac],
    )
}

#[test]
fn var_for_term_returns_variable_when_mapped() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let x = _xyz[0];
    let mut theory = MockTheory::new();
    let ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    assert_eq!(ext.var_for_term(x), Some(Variable::new(1)));
}

#[test]
fn var_for_term_returns_none_for_unmapped_term() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let unmapped = TermId(999);
    assert_eq!(ext.var_for_term(unmapped), None);
}

#[test]
fn term_to_literal_positive_value() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let x = _xyz[0];
    let mut theory = MockTheory::new();
    let ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let lit = ext.term_to_literal(x, true).unwrap();
    assert!(lit.is_positive());
    assert_eq!(lit.variable(), Variable::new(1));
}

#[test]
fn term_to_literal_negative_value() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let x = _xyz[0];
    let mut theory = MockTheory::new();
    let ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let lit = ext.term_to_literal(x, false).unwrap();
    assert!(!lit.is_positive());
    assert_eq!(lit.variable(), Variable::new(1));
}

#[test]
fn term_to_literal_returns_none_for_unmapped() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let unmapped = TermId(999);
    assert_eq!(ext.term_to_literal(unmapped, true), None);
}

#[test]
fn is_theory_atom_returns_true_for_atoms() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    assert!(ext.is_theory_atom(Variable::new(1)));
    assert!(ext.is_theory_atom(Variable::new(2)));
    assert!(ext.is_theory_atom(Variable::new(3)));
}

#[test]
fn is_theory_atom_works_with_unsorted_atom_order() {
    let (terms, var_to_term, term_to_var, mut theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    theory_atoms.swap(0, 2);

    let mut theory = MockTheory::new();
    let ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    assert!(ext.is_theory_atom(Variable::new(1)));
    assert!(ext.is_theory_atom(Variable::new(2)));
    assert!(ext.is_theory_atom(Variable::new(3)));
}

#[test]
fn is_theory_atom_returns_false_for_non_atoms() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    // Variable 4 is not mapped
    assert!(!ext.is_theory_atom(Variable::new(4)));
}

#[test]
fn retain_new_axioms_skips_duplicate_axioms_across_extension_instances_issue_6586() {
    let (_terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, xyz) =
        create_test_setup();
    let axiom = (xyz[0], true, xyz[1], false);
    let mut seen_axioms = HashSet::default();

    // Pass None for terms to skip LRA tautology validation (#6242, #6564).
    // This test exercises duplicate-detection in retain_new_axioms, not axiom
    // validation. Bool-typed axioms would be rejected by the LRA validator.
    let mut theory = MockTheory::new().with_axiom_terms(vec![axiom]);
    let mut first = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        None,
        None,
    );
    first.retain_new_axioms(&mut seen_axioms);
    assert_eq!(first.pending_axiom_terms, vec![axiom]);
    assert_eq!(first.pending_axiom_clauses.len(), 1);
    assert_eq!(seen_axioms.len(), 1);

    let mut theory = MockTheory::new().with_axiom_terms(vec![axiom]);
    let mut second = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        None,
        None,
    );
    second.retain_new_axioms(&mut seen_axioms);
    assert!(second.pending_axiom_terms.is_empty());
    assert!(second.pending_axiom_clauses.is_empty());
    assert_eq!(seen_axioms.len(), 1);
}

#[test]
fn propagate_records_farkas_for_validated_bound_axioms_issue_6686() {
    use crate::proof_tracker::ProofTracker;
    use ay_core::{ProofStep, TheoryLemmaKind};

    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, [x_ge_0, x_le_0]) =
        create_lra_bound_axiom_setup();
    let mut theory = MockTheory::new().with_axiom_terms(vec![(x_ge_0, true, x_le_0, true)]);
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LRA");
    let negations = HashMap::default();

    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    )
    .with_proof_tracking(&mut tracker, &negations);

    let result = ext.propagate(&MockContext::new());
    assert_eq!(
        result.clauses.len(),
        1,
        "expected one pending bound axiom clause"
    );
    assert_eq!(
        result.clauses[0],
        vec![
            Literal::positive(Variable::new(1)),
            Literal::positive(Variable::new(2))
        ],
        "bound axiom literals should match the registered theory atoms"
    );
    assert!(
        result.conflict.is_none() && result.propagations.is_empty() && !result.stop,
        "bound-axiom injection should only add clauses: {result:?}"
    );
    assert!(
        ext.pending_axiom_terms.is_empty() && ext.pending_axiom_farkas.is_empty(),
        "propagate() should consume aligned bound-axiom proof data"
    );

    drop(ext);
    let proof = tracker.take_proof();
    let theory_lemmas: Vec<_> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::TheoryLemma {
                clause,
                farkas,
                kind,
                ..
            } => Some((clause.clone(), farkas.clone(), *kind)),
            _ => None,
        })
        .collect();
    assert_eq!(
        theory_lemmas.len(),
        1,
        "bound axiom injection should record exactly one theory lemma: {theory_lemmas:?}"
    );

    let (clause, farkas, kind) = &theory_lemmas[0];
    assert_eq!(*kind, TheoryLemmaKind::LraFarkas);
    assert_eq!(clause, &vec![x_ge_0, x_le_0]);
    let farkas = farkas
        .as_ref()
        .expect("validated LRA bound axiom should retain extracted Farkas coefficients");
    assert_eq!(
        farkas.coefficients.len(),
        clause.len(),
        "Farkas coefficients must stay aligned with bound-axiom literals"
    );
}

#[test]
fn retain_new_axioms_keeps_farkas_alignment_before_propagate_issue_6686() {
    use crate::proof_tracker::ProofTracker;
    use ay_core::{ProofStep, TheoryLemmaKind};

    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, [x_ge_0, x_le_0]) =
        create_lra_bound_axiom_setup();
    let mut theory = MockTheory::new().with_axiom_terms(vec![(x_ge_0, true, x_le_0, true)]);
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LRA");
    let negations = HashMap::default();

    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    )
    .with_proof_tracking(&mut tracker, &negations);

    let mut seen_axioms = HashSet::default();
    ext.retain_new_axioms(&mut seen_axioms);
    assert_eq!(seen_axioms.len(), 1, "expected one retained bound axiom");
    assert_eq!(
        ext.pending_axiom_clauses.len(),
        1,
        "retain_new_axioms() must not silently drop clauses with aligned Farkas sidecars"
    );
    assert_eq!(
        ext.pending_axiom_terms,
        vec![(x_ge_0, true, x_le_0, true)],
        "bound-axiom terms should stay aligned with clauses after retain_new_axioms()"
    );
    assert_eq!(
        ext.pending_axiom_farkas.len(),
        1,
        "retained bound axioms should keep one aligned Farkas sidecar"
    );
    assert!(
        ext.pending_axiom_farkas[0].is_some(),
        "retain_new_axioms() must preserve validation Farkas certificates"
    );

    let result = ext.propagate(&MockContext::new());
    assert_eq!(
        result.clauses,
        vec![vec![
            Literal::positive(Variable::new(1)),
            Literal::positive(Variable::new(2))
        ]],
        "propagate() should inject the retained bound axiom"
    );
    assert!(
        ext.pending_axiom_terms.is_empty() && ext.pending_axiom_farkas.is_empty(),
        "propagate() should consume aligned bound-axiom proof data"
    );

    drop(ext);
    let proof = tracker.take_proof();
    let theory_lemmas: Vec<_> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::TheoryLemma {
                clause,
                farkas,
                kind,
                ..
            } => Some((clause.clone(), farkas.clone(), *kind)),
            _ => None,
        })
        .collect();
    assert_eq!(
        theory_lemmas.len(),
        1,
        "bound axiom injection should record exactly one theory lemma after retain_new_axioms()"
    );

    let (clause, farkas, kind) = &theory_lemmas[0];
    assert_eq!(*kind, TheoryLemmaKind::LraFarkas);
    assert_eq!(clause, &vec![x_ge_0, x_le_0]);
    assert!(
        farkas.is_some(),
        "proof export should keep the bound-axiom Farkas annotation after retain_new_axioms()"
    );
}

#[test]
fn propagate_pushes_theory_level_to_match_sat_level() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new().with_level(3);
    ext.propagate(&ctx);

    assert_eq!(ext.theory.push_count, 3);
}

#[test]
fn propagate_asserts_theory_atoms_from_trail() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let x = _xyz[0];
    let y = _xyz[1];
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let trail = vec![
        Literal::positive(Variable::new(1)),
        Literal::negative(Variable::new(2)),
    ];
    let ctx = MockContext::new().with_trail(trail);
    ext.propagate(&ctx);

    assert_eq!(ext.theory.assertions.len(), 2);
    assert!(ext.theory.assertions.contains(&(x, true)));
    assert!(ext.theory.assertions.contains(&(y, false)));
}

#[test]
fn propagate_returns_none_when_no_propagations() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.propagate(&ctx);

    // ExtPropagateResult is a struct, not an enum
    assert!(result.clauses.is_empty());
    assert!(result.conflict.is_none());
}

#[test]
fn propagate_returns_conflict_on_theory_unsat() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let x = _xyz[0];
    let y = _xyz[1];

    let conflict = vec![TheoryLit::new(x, true), TheoryLit::new(y, false)];
    let mut theory = MockTheory::new().with_check_result(TheoryResult::Unsat(conflict));
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.propagate(&ctx);

    assert!(result.conflict.is_some());
}

#[test]
fn propagate_returns_clauses_for_propagations() {
    // The propagate path runs a MANDATORY semantic-verification gate over every
    // theory propagation (propagate.rs, promoted to all builds in #8529 and
    // routed through the cached verify-only solvers in #qfuflia-a2-verifier-reuse):
    // it re-checks `reason ∧ ¬propagated` with a real theory solver and DROPS
    // any propagation the reason does not actually entail. That drop is SOUND
    // (skipping a propagation is completeness-only, never a wrong verdict) and
    // is the gate working as designed. This test previously fed a mock that
    // propagated `z ← (x ∧ y)` over three INDEPENDENT Bool variables — NOT a
    // real entailment (`x=true ∧ y=true ∧ z=false` is satisfiable), so the gate
    // now correctly drops it and no clause is produced (observed 0 propagations
    // where the stale assertion expected 1). Use a genuinely valid EUF
    // entailment — transitivity `a=b ∧ b=c ⊢ a=c` — so the plumbing this test
    // targets (theory propagation → SAT propagation clause, propagated literal
    // FIRST) is actually exercised end-to-end.
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, atoms) =
        create_euf_transitivity_setup();
    let eq_ab = atoms[0];
    let eq_bc = atoms[1];
    let eq_ac = atoms[2];

    // Theory says: a=b and b=c, therefore a=c.
    let prop = TheoryPropagation {
        literal: TheoryLit::new(eq_ac, true),
        reason: vec![TheoryLit::new(eq_ab, true), TheoryLit::new(eq_bc, true)],
        reason_data: None,
    };
    let mut theory = MockTheory::new().with_propagations(vec![prop]);
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    // eq_ab (var 1) and eq_bc (var 2) are true on the trail; eq_ac (var 3) is
    // unassigned.
    let trail = vec![
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
    ];
    let ctx = MockContext::new().with_trail(trail);
    let result = ext.propagate(&ctx);

    // Propagations go through the lightweight path (#4919)
    assert_eq!(result.propagations.len(), 1);
    // Clause should be (eq_ac ∨ ¬eq_ab ∨ ¬eq_bc) — propagated lit first
    let (clause, propagated) = &result.propagations[0];
    assert_eq!(clause.len(), 3);
    assert_eq!(*propagated, clause[0]);
}

#[test]
fn propagate_skips_invalid_semantic_propagation_without_rejection_cache_reset_issue_7965() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, [x_ge_0, x_le_0]) =
        create_lra_bound_axiom_setup();

    let invalid_prop = TheoryPropagation {
        literal: TheoryLit::new(x_ge_0, true),
        reason: vec![TheoryLit::new(x_le_0, true)],
        reason_data: None,
    };
    let mut theory = MockTheory::new().with_propagations(vec![invalid_prop]);
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.propagate(&ctx);

    assert!(
        result.propagations.is_empty(),
        "semantic rejection should drop the invalid propagation"
    );
    assert!(
        ext.theory.rejected_propagations.is_empty(),
        "semantic rejection should no longer clear the theory cache via mark_propagation_rejected()"
    );
}

#[test]
fn check_returns_sat_when_theory_sat() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.check(&ctx);

    assert!(matches!(result, ExtCheckResult::Sat));
}

#[test]
fn check_returns_conflict_when_theory_unsat() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let x = _xyz[0];

    let conflict = vec![TheoryLit::new(x, true)];
    let mut theory = MockTheory::new().with_check_result(TheoryResult::Unsat(conflict));
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.check(&ctx);

    match result {
        ExtCheckResult::Conflict(clause) => {
            assert_eq!(clause.len(), 1);
        }
        _ => panic!("Expected Conflict, got {result:?}"),
    }
}

#[test]
fn check_returns_unknown_for_unknown_result() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new().with_check_result(TheoryResult::Unknown);
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.check(&ctx);

    assert!(matches!(result, ExtCheckResult::Unknown));
}

#[test]
fn backtrack_pops_theory_levels() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    // First push to level 5
    let ctx = MockContext::new().with_level(5);
    ext.propagate(&ctx);
    assert_eq!(ext.theory.push_count, 5);
    assert_eq!(ext.theory_level, 5);

    // Now backtrack to level 2
    ext.backtrack(2);

    assert_eq!(ext.theory.pop_count, 3);
    assert_eq!(ext.theory_level, 2);
    assert_eq!(ext.last_trail_pos, 0); // Restored from stack (was 0 at push time)
}

#[test]
fn backtrack_restores_trail_position_from_stack() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    // SAT variables 1, 2, 3 map to theory atoms x, y, z
    let var_x = Variable::new(1);
    let var_y = Variable::new(2);
    let var_z = Variable::new(3);

    // Push to level 1 with empty trail
    let ctx1 = MockContext::new().with_level(1);
    ext.propagate(&ctx1);
    assert_eq!(ext.theory_level, 1);
    assert_eq!(ext.last_trail_pos, 0); // No trail assignments

    // Push to level 2 with 2 trail assignments
    let ctx2 = MockContext::new()
        .with_level(2)
        .with_trail(vec![Literal::positive(var_x), Literal::negative(var_y)]);
    ext.propagate(&ctx2);
    assert_eq!(ext.theory_level, 2);
    assert_eq!(ext.last_trail_pos, 2); // Processed 2 assignments

    // Push to level 3 with 1 more trail assignment (3 total)
    let ctx3 = MockContext::new().with_level(3).with_trail(vec![
        Literal::positive(var_x),
        Literal::negative(var_y),
        Literal::positive(var_z),
    ]);
    ext.propagate(&ctx3);
    assert_eq!(ext.theory_level, 3);
    assert_eq!(ext.last_trail_pos, 3); // Processed 3 assignments

    // Backtrack to level 2: should restore trail pos to 2 (saved before push to 3)
    ext.backtrack(2);
    assert_eq!(ext.theory_level, 2);
    assert_eq!(ext.last_trail_pos, 2); // Restored, NOT reset to 0

    // Backtrack to level 0: should restore trail pos to 0
    ext.backtrack(0);
    assert_eq!(ext.theory_level, 0);
    assert_eq!(ext.last_trail_pos, 0);
}

#[test]
fn backtrack_handles_no_ops() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    // At level 0, backtrack to 0
    ext.backtrack(0);

    assert_eq!(ext.theory.pop_count, 0);
    assert_eq!(ext.theory_level, 0);
}

#[test]
fn init_resets_theory_and_state() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    // Set some state
    let ctx = MockContext::new().with_level(3);
    ext.propagate(&ctx);
    ext.last_trail_pos = 10;

    // Now init
    ext.init();

    assert_eq!(ext.theory.reset_count, 1);
    assert_eq!(ext.last_trail_pos, 0);
    assert_eq!(ext.theory_level, 0);
}

#[test]
fn can_propagate_always_returns_true() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    assert!(ext.can_propagate(&ctx));
}

#[test]
fn propagate_checks_level0_after_zero_propagation_streak() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );
    ext.has_checked = true;
    ext.zero_propagation_streak = 5;

    let ctx = MockContext::new().with_trail(vec![Literal::positive(Variable::new(1))]);
    let result = ext.propagate(&ctx);

    assert!(result.clauses.is_empty());
    assert!(result.propagations.is_empty());
    assert!(result.conflict.is_none());
    assert_eq!(ext.theory.check_calls, 1);
    assert_eq!(ext.deferred_atom_count, 0);
    assert_eq!(ext.last_trail_pos, 1);
    assert_eq!(ext.eager_stats().batch_defers, 0);
    // #8255: level0 always forces a check now (sat_level == 0 in should_check),
    // so level0_batch_guard_hits is no longer incremented.
    assert_eq!(ext.eager_stats().level0_checks, 1);
}

#[test]
fn propagate_checks_level0_when_deferred_atoms_are_near_batch_target() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );
    ext.has_checked = true;
    // #8452 TL96: Streak thresholds raised to 512/1024/2048. With streak=20
    // (< 512 = PHASE1_STREAK), batch_target is 0, so no deferral happens.
    // Level 0 always forces a check regardless.
    ext.zero_propagation_streak = 20;
    ext.deferred_atom_count = 2;

    let ctx = MockContext::new().with_trail(vec![Literal::positive(Variable::new(1))]);
    let result = ext.propagate(&ctx);

    assert!(result.clauses.is_empty());
    assert!(result.propagations.is_empty());
    assert!(result.conflict.is_none());
    assert_eq!(ext.theory.check_calls, 1);
    assert_eq!(ext.deferred_atom_count, 0);
    assert_eq!(ext.last_trail_pos, 1);
    assert_eq!(ext.eager_stats().batch_defers, 0);
    // #8452 TL96: With streak=20 < PHASE1_STREAK=512, batch_target=0,
    // so level0_batch_guard_hits is 0 (no batching attempted).
    assert_eq!(ext.eager_stats().level0_batch_guard_hits, 0);
    assert_eq!(ext.eager_stats().level0_checks, 1);
}

#[test]
fn propagate_does_not_batch_when_split_is_pending() {
    use ay_core::SplitRequest;
    use num_bigint::BigInt;
    use num_rational::BigRational;

    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );
    ext.has_checked = true;
    ext.zero_propagation_streak = 5;
    ext.pending_split = Some(TheoryResult::NeedSplit(SplitRequest {
        variable: theory_atoms[0],
        value: BigRational::new(BigInt::from(5), BigInt::from(2)),
        floor: BigInt::from(2),
        ceil: BigInt::from(3),
    }));

    let ctx = MockContext::new()
        .with_level(1)
        .with_trail(vec![Literal::positive(Variable::new(1))]);
    let result = ext.propagate(&ctx);

    assert!(result.clauses.is_empty());
    assert!(result.propagations.is_empty());
    assert!(result.conflict.is_none());
    assert_eq!(ext.theory.check_calls, 1);
    assert_eq!(ext.deferred_atom_count, 0);
}

#[test]
fn propagate_stores_split_request_in_pending() {
    use ay_core::SplitRequest;
    use num_bigint::BigInt;
    use num_rational::BigRational;

    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _) = create_test_setup();
    let split = SplitRequest {
        variable: theory_atoms[0],
        value: BigRational::new(BigInt::from(5), BigInt::from(2)),
        floor: BigInt::from(2),
        ceil: BigInt::from(3),
    };
    let mut theory = MockTheory::new().with_check_result(TheoryResult::NeedSplit(split.clone()));
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.propagate(&ctx);
    assert!(result.conflict.is_none());
    assert!(result.clauses.is_empty());
    let pending = ext.take_pending_split();
    assert!(pending.is_some(), "split should be stored as pending");
    match pending.unwrap() {
        TheoryResult::NeedSplit(s) => assert_eq!(s.variable, split.variable),
        other => panic!("expected NeedSplit, got {other:?}"),
    }
    assert!(ext.take_pending_split().is_none());
}

/// Mock theory solver that claims EUF semantic checks are supported.
/// Used to test the `verify_euf_conflict` integration in the extension path.
#[cfg(test)]
struct EufMockTheory {
    inner: MockTheory,
}

#[cfg(test)]
impl EufMockTheory {
    fn new() -> Self {
        Self {
            inner: MockTheory::new(),
        }
    }

    fn with_check_result(mut self, result: TheoryResult) -> Self {
        self.inner = self.inner.with_check_result(result);
        self
    }
}

#[cfg(test)]
impl TheorySolver for EufMockTheory {
    fn assert_literal(&mut self, literal: TermId, value: bool) {
        self.inner.assert_literal(literal, value);
    }

    fn check(&mut self) -> TheoryResult {
        self.inner.check()
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        self.inner.propagate()
    }

    fn push(&mut self) {
        self.inner.push();
    }

    fn pop(&mut self) {
        self.inner.pop();
    }

    fn reset(&mut self) {
        self.inner.reset();
    }

    fn supports_euf_semantic_check(&self) -> bool {
        true
    }
}

#[cfg(test)]
type EufTestSetup = (
    TermStore,
    HashMap<u32, TermId>,
    HashMap<TermId, u32>,
    Vec<TermId>,
    HashSet<TermId>,
    [TermId; 3],
    [TermId; 3],
);

/// Create a test setup with EUF equality terms.
///
/// Returns: (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set,
///           [a, b, c], [eq_ab, eq_bc, eq_ac])
///
/// Variables a, b, c are Int-sorted. Equalities map to SAT variables 1-3.
#[cfg(test)]
fn create_euf_test_setup() -> EufTestSetup {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);

    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);
    let eq_ac = terms.mk_eq(a, c);

    let var_to_term: HashMap<u32, TermId> =
        [(1, eq_ab), (2, eq_bc), (3, eq_ac)].into_iter().collect();
    let term_to_var: HashMap<TermId, u32> =
        [(eq_ab, 1), (eq_bc, 2), (eq_ac, 3)].into_iter().collect();
    let mut theory_atoms = vec![eq_ab, eq_bc, eq_ac];
    theory_atoms.sort_unstable_by_key(|term| term.0);
    let theory_atom_set: HashSet<TermId> = theory_atoms.iter().copied().collect();

    (
        terms,
        var_to_term,
        term_to_var,
        theory_atoms,
        theory_atom_set,
        [a, b, c],
        [eq_ab, eq_bc, eq_ac],
    )
}

/// Valid EUF conflict (a=b, b=c, ¬(a=c)) accepted in propagate().
#[test]
fn propagate_euf_semantic_check_accepts_valid_conflict() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _, eqs) =
        create_euf_test_setup();
    let [eq_ab, eq_bc, eq_ac] = eqs;

    // Transitivity conflict: a=b ∧ b=c ∧ ¬(a=c) is UNSAT
    let conflict = vec![
        TheoryLit::new(eq_ab, true),
        TheoryLit::new(eq_bc, true),
        TheoryLit::new(eq_ac, false),
    ];
    let mut theory = EufMockTheory::new().with_check_result(TheoryResult::Unsat(conflict));
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.propagate(&ctx);

    // Should produce a conflict (not be skipped by verification)
    assert!(
        result.conflict.is_some(),
        "valid EUF conflict should pass semantic check and produce conflict"
    );
}

/// Invalid EUF conflict (a=b, ¬(a=c)) fails closed to Unknown.
#[test]
fn propagate_euf_semantic_check_rejects_invalid_conflict() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _, eqs) =
        create_euf_test_setup();
    let [eq_ab, _eq_bc, eq_ac] = eqs;

    // a=b ∧ ¬(a=c) is SAT (just set c ≠ a, c ≠ b)
    let conflict = vec![TheoryLit::new(eq_ab, true), TheoryLit::new(eq_ac, false)];
    let mut theory = EufMockTheory::new().with_check_result(TheoryResult::Unsat(conflict));
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.propagate(&ctx);
    assert!(
        result.conflict.is_none(),
        "invalid EUF conflict should not be emitted as a SAT conflict (#4704)"
    );
    assert!(
        matches!(ext.take_pending_split(), Some(TheoryResult::Unknown)),
        "invalid EUF conflict should escalate to pending Unknown"
    );
}

/// Valid EUF conflict accepted in check().
#[test]
fn check_euf_semantic_check_accepts_valid_conflict() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _, eqs) =
        create_euf_test_setup();
    let [eq_ab, eq_bc, eq_ac] = eqs;

    let conflict = vec![
        TheoryLit::new(eq_ab, true),
        TheoryLit::new(eq_bc, true),
        TheoryLit::new(eq_ac, false),
    ];
    let mut theory = EufMockTheory::new().with_check_result(TheoryResult::Unsat(conflict));
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.check(&ctx);

    assert!(
        matches!(result, ExtCheckResult::Conflict(_)),
        "valid EUF conflict should pass semantic check in check()"
    );
}

/// Invalid EUF conflict in `check()` fails closed to `Unknown`.
///
/// `a=b ∧ ¬(a=c)` is satisfiable, so the mock "conflict" is spurious. Before
/// the #8595 fail-open removal, `check()` kept the conflict and learned its
/// negation, producing a wrong UNSAT; it must now degrade to `Unknown`,
/// matching the eager `propagate()` sibling.
#[test]
fn check_euf_semantic_check_rejects_invalid_conflict() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _, eqs) =
        create_euf_test_setup();
    let [eq_ab, _eq_bc, eq_ac] = eqs;

    let conflict = vec![TheoryLit::new(eq_ab, true), TheoryLit::new(eq_ac, false)];
    let mut theory = EufMockTheory::new().with_check_result(TheoryResult::Unsat(conflict));
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.check(&ctx);
    assert!(
        matches!(result, ExtCheckResult::Unknown),
        "check() should reject the spurious conflict and degrade to Unknown, not learn a wrong-UNSAT clause"
    );
}

/// Int arithmetic setup: atoms `(> x 2)` and `(< x 1)` over `x: Int`, mapped to
/// SAT vars 1 and 2. `{x>2, x<1}` is LIA-infeasible; `{x>2}` alone is SAT.
///
/// Returns (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set,
///          [x_gt_2, x_lt_1]).
#[cfg(test)]
#[allow(clippy::type_complexity)]
fn create_lia_conflict_setup() -> (
    TermStore,
    HashMap<u32, TermId>,
    HashMap<TermId, u32>,
    Vec<TermId>,
    HashSet<TermId>,
    [TermId; 2],
) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let one = terms.mk_int(BigInt::from(1));
    let x_gt_2 = terms.mk_gt(x, two);
    let x_lt_1 = terms.mk_lt(x, one);

    let var_to_term: HashMap<u32, TermId> = [(1, x_gt_2), (2, x_lt_1)].into_iter().collect();
    let term_to_var: HashMap<TermId, u32> = [(x_gt_2, 1), (x_lt_1, 2)].into_iter().collect();
    let mut theory_atoms = vec![x_gt_2, x_lt_1];
    theory_atoms.sort_unstable_by_key(|term| term.0);
    let theory_atom_set: HashSet<TermId> = theory_atoms.iter().copied().collect();

    (
        terms,
        var_to_term,
        term_to_var,
        theory_atoms,
        theory_atom_set,
        [x_gt_2, x_lt_1],
    )
}

/// Laundering scenario, `Unsat` arm: a semantically-SAT "conflict" (`x > 2`
/// alone) must NOT be learned. Before the #8595 fail-open removal in `check()`
/// this produced a wrong UNSAT for the satisfiable formula; it must now degrade
/// to Unknown via the fail-closed semantic gate.
#[test]
fn check_unsat_arm_rejects_satisfiable_arithmetic_conflict() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, [x_gt_2, _x_lt_1]) =
        create_lia_conflict_setup();
    let conflict = vec![TheoryLit::new(x_gt_2, true)];
    let mut theory = MockTheory::new().with_check_result(TheoryResult::Unsat(conflict));
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    assert!(
        matches!(ext.check(&ctx), ExtCheckResult::Unknown),
        "unverifiable conflict must degrade to Unknown, not launder into a wrong UNSAT clause"
    );
}

/// Completeness, `Unsat` arm: a genuinely infeasible conflict (`x > 2 ∧ x < 1`)
/// passes LIA semantic verification and is still learned as a real conflict.
#[test]
fn check_unsat_arm_learns_infeasible_arithmetic_conflict() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, [x_gt_2, x_lt_1]) =
        create_lia_conflict_setup();
    let conflict = vec![TheoryLit::new(x_gt_2, true), TheoryLit::new(x_lt_1, true)];
    let mut theory = MockTheory::new().with_check_result(TheoryResult::Unsat(conflict));
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    assert!(
        matches!(ext.check(&ctx), ExtCheckResult::Conflict(_)),
        "semantically verified conflict must still be learned as a Conflict"
    );
}

/// Laundering scenario, `UnsatWithFarkas` arm WITHOUT a certificate: a
/// satisfiable literal set must degrade to Unknown through the fail-closed
/// semantic backstop (certificate downgrade must not fail open).
#[test]
fn check_farkas_arm_rejects_satisfiable_conflict_without_certificate() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, [x_gt_2, _x_lt_1]) =
        create_lia_conflict_setup();
    let conflict = vec![TheoryLit::new(x_gt_2, true)];
    // `TheoryConflict::new` carries NO Farkas certificate.
    let mut theory = MockTheory::new().with_check_result(TheoryResult::UnsatWithFarkas(
        ay_core::TheoryConflict::new(conflict),
    ));
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    assert!(
        matches!(ext.check(&ctx), ExtCheckResult::Unknown),
        "unverifiable certificate-less Farkas conflict must degrade to Unknown"
    );
}

/// Completeness, `UnsatWithFarkas` arm WITHOUT a certificate: a genuinely
/// infeasible conflict stays learnable through the semantic backstop — the
/// certificate downgrade must not fail-close valid conflicts.
#[test]
fn check_farkas_arm_learns_infeasible_conflict_without_certificate() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, [x_gt_2, x_lt_1]) =
        create_lia_conflict_setup();
    let conflict = vec![TheoryLit::new(x_gt_2, true), TheoryLit::new(x_lt_1, true)];
    let mut theory = MockTheory::new().with_check_result(TheoryResult::UnsatWithFarkas(
        ay_core::TheoryConflict::new(conflict),
    ));
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    assert!(
        matches!(ext.check(&ctx), ExtCheckResult::Conflict(_)),
        "valid certificate-less Farkas conflict must pass the semantic backstop and be learned"
    );
}

#[test]
fn check_stores_split_request_in_pending() {
    use ay_core::SplitRequest;
    use num_bigint::BigInt;
    use num_rational::BigRational;

    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _) = create_test_setup();
    let split = SplitRequest {
        variable: theory_atoms[0],
        value: BigRational::new(BigInt::from(5), BigInt::from(2)),
        floor: BigInt::from(2),
        ceil: BigInt::from(3),
    };
    let mut theory = MockTheory::new().with_check_result(TheoryResult::NeedSplit(split.clone()));
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.check(&ctx);
    assert!(
        matches!(result, ExtCheckResult::Unknown),
        "check() with split should return Unknown, got {result:?}"
    );
    let pending = ext.take_pending_split();
    assert!(pending.is_some(), "split should be stored as pending");
    match pending.unwrap() {
        TheoryResult::NeedSplit(s) => assert_eq!(s.variable, split.variable),
        other => panic!("expected NeedSplit, got {other:?}"),
    }
}

#[test]
fn check_stores_pending_bound_refinements_on_sat() {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _) = create_test_setup();
    let refinement = BoundRefinementRequest {
        variable: theory_atoms[0],
        rhs_term: None,
        bound_value: BigRational::from(BigInt::from(3)),
        is_upper: true,
        is_integer: false,
        reason: vec![TheoryLit::new(theory_atoms[1], true)],
    };
    let mut theory = MockTheory::new().with_bound_refinements(vec![refinement.clone()]);
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.check(&ctx);
    assert!(matches!(result, ExtCheckResult::Sat));

    let pending = ext.take_pending_bound_refinements();
    assert_eq!(pending, vec![refinement]);
    assert!(ext.take_pending_bound_refinements().is_empty());
}

#[test]
fn propagate_preserves_pending_bound_refinements_until_final_check() {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, xyz) = create_test_setup();
    let refinement = BoundRefinementRequest {
        variable: xyz[0],
        rhs_term: None,
        bound_value: BigRational::from(BigInt::from(3)),
        is_upper: true,
        is_integer: false,
        reason: vec![TheoryLit::new(xyz[1], true)],
    };
    let mut theory = PropagateOnlyRefinementTheory::new(refinement.clone());
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new().with_trail(vec![Literal::positive(Variable::new(1))]);
    let result = ext.propagate(&ctx);
    assert!(result.clauses.is_empty());
    assert!(result.propagations.is_empty());
    assert!(result.conflict.is_none());

    let final_result = ext.check(&ctx);
    assert!(matches!(final_result, ExtCheckResult::Sat));
    assert_eq!(ext.take_pending_bound_refinements(), vec![refinement]);
}

#[test]
fn propagate_inline_bound_refinement_replay_stops_with_pending_requests_issue_6586() {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, xyz) = create_test_setup();
    let refinement = BoundRefinementRequest {
        variable: xyz[0],
        rhs_term: None,
        bound_value: BigRational::from(BigInt::from(3)),
        is_upper: true,
        is_integer: false,
        reason: vec![TheoryLit::new(xyz[1], true)],
    };
    let mut theory = PropagateOnlyRefinementTheory::new(refinement.clone());
    let known_replays = HashSet::default();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    )
    .with_inline_bound_refinement_replay(&known_replays);
    assert!(
        ext.should_stop_for_inline_bound_refinement_handoff(std::slice::from_ref(&refinement)),
        "inline replay mode should recognize unseen refinement requests before propagate()"
    );

    let ctx = MockContext::new().with_trail(vec![Literal::positive(Variable::new(1))]);
    let result = ext.propagate(&ctx);
    assert!(result.clauses.is_empty());
    assert!(result.propagations.is_empty());
    assert!(result.conflict.is_none());
    assert!(
        result.stop,
        "inline replay mode should stop SAT search when a new refinement appears"
    );
    assert_eq!(ext.take_pending_bound_refinements(), vec![refinement]);
}

#[test]
fn propagate_inline_bound_refinement_replay_ignores_known_requests_issue_6586() {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, xyz) = create_test_setup();
    let refinement = BoundRefinementRequest {
        variable: xyz[0],
        rhs_term: None,
        bound_value: BigRational::from(BigInt::from(3)),
        is_upper: true,
        is_integer: false,
        reason: vec![TheoryLit::new(xyz[1], true)],
    };
    let mut theory = PropagateOnlyRefinementTheory::new(refinement.clone());
    let known_replays: HashSet<_> = [BoundRefinementReplayKey::new(&refinement)]
        .into_iter()
        .collect();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    )
    .with_inline_bound_refinement_replay(&known_replays);

    let ctx = MockContext::new().with_trail(vec![Literal::positive(Variable::new(1))]);
    let result = ext.propagate(&ctx);
    assert!(
        !result.stop,
        "already replayed refinements should not re-trigger inline handoff"
    );
    assert_eq!(ext.take_pending_bound_refinements(), vec![refinement]);
}

#[test]
fn backtrack_clears_pending_bound_refinements_from_current_branch() {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, xyz) = create_test_setup();
    let refinement = BoundRefinementRequest {
        variable: xyz[0],
        rhs_term: None,
        bound_value: BigRational::from(BigInt::from(3)),
        is_upper: true,
        is_integer: false,
        reason: vec![TheoryLit::new(xyz[1], true)],
    };
    let mut theory = MockTheory::new().with_bound_refinements(vec![refinement.clone()]);
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new()
        .with_level(1)
        .with_trail(vec![Literal::positive(Variable::new(1))]);
    let _ = ext.propagate(&ctx);
    assert_eq!(ext.pending_bound_refinements, vec![refinement]);

    ext.backtrack(0);
    assert!(ext.pending_bound_refinements.is_empty());
}

// =========================================================================
// ITE relevancy filter tests (#8125)
// =========================================================================

/// Create a setup with an ITE node: `(ite cond then_atom else_atom)`.
///
/// Returns: (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set,
///           cond_term, then_atom, else_atom, ite_term)
///
/// SAT variable mapping:
///   1 -> cond, 2 -> then_atom, 3 -> else_atom, 4 -> ite_term
#[cfg(test)]
type IteTestSetup = (
    TermStore,
    HashMap<u32, TermId>,
    HashMap<TermId, u32>,
    Vec<TermId>,
    HashSet<TermId>,
    TermId,
    TermId,
    TermId,
    TermId,
);

#[cfg(test)]
fn create_ite_test_setup() -> IteTestSetup {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::from(BigInt::from(0)));
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));

    // cond: a Bool variable
    let cond = terms.mk_var("cond", Sort::Bool);
    // then-branch theory atom: (>= x 0)
    let then_atom = terms.mk_ge(x, zero);
    // else-branch theory atom: (>= x 1)
    let else_atom = terms.mk_ge(x, one);
    // ITE: (ite cond (>= x 0) (>= x 1))
    let ite = terms.mk_ite(cond, then_atom, else_atom);

    let var_to_term: HashMap<u32, TermId> = [(1, cond), (2, then_atom), (3, else_atom), (4, ite)]
        .into_iter()
        .collect();
    let term_to_var: HashMap<TermId, u32> = [(cond, 1), (then_atom, 2), (else_atom, 3), (ite, 4)]
        .into_iter()
        .collect();
    // Theory atoms: the predicate atoms, not the ITE or condition
    let theory_atoms = vec![then_atom, else_atom];
    let theory_atom_set: HashSet<TermId> = theory_atoms.iter().copied().collect();

    (
        terms,
        var_to_term,
        term_to_var,
        theory_atoms,
        theory_atom_set,
        cond,
        then_atom,
        else_atom,
        ite,
    )
}

#[test]
fn ite_relevancy_construction_marks_branch_atoms_as_guarded() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, ..) =
        create_ite_test_setup();
    let mut theory = MockTheory::new();
    let ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    // then_atom (sat var 2) should be guarded by cond (sat var 1), is_then=true
    let then_idx = 2usize;
    let then_word = then_idx / 64;
    assert!(
        (ext.ite_guarded_bitset[then_word] >> (then_idx % 64)) & 1 != 0,
        "then-branch atom should be marked as ITE-guarded"
    );
    assert_eq!(
        ext.ite_branch_guards[then_idx],
        (1, true),
        "then-branch guard: cond_var=1, is_then=true"
    );

    // else_atom (sat var 3) should be guarded by cond (sat var 1), is_then=false
    let else_idx = 3usize;
    let else_word = else_idx / 64;
    assert!(
        (ext.ite_guarded_bitset[else_word] >> (else_idx % 64)) & 1 != 0,
        "else-branch atom should be marked as ITE-guarded"
    );
    assert_eq!(
        ext.ite_branch_guards[else_idx],
        (1, false),
        "else-branch guard: cond_var=1, is_then=false"
    );
}

#[test]
fn ite_relevancy_defers_inactive_branch_atom_during_propagate() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, ..) =
        create_ite_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    // Trail: cond=true (var 1), else_atom=true (var 3)
    // Since cond=true, else_atom is in the INACTIVE branch and should be deferred.
    let trail = vec![
        Literal::positive(Variable::new(1)), // cond = true
        Literal::positive(Variable::new(3)), // else_atom = true (inactive branch)
    ];
    let ctx = MockContext::new().with_trail(trail).with_level(1);
    let _ = ext.propagate(&ctx);

    // The else_atom should have been deferred, not asserted to the theory
    assert!(
        !ext.theory
            .assertions
            .iter()
            .any(|(t, _)| *t == theory_atoms[1]),
        "inactive-branch atom should not be asserted to theory"
    );
    assert_eq!(
        ext.ite_deferred_atoms.len(),
        1,
        "one atom should be deferred"
    );
    assert_eq!(
        ext.eager_stats.ite_relevancy_skips, 1,
        "ITE relevancy skip counter should be incremented"
    );
}

#[test]
fn ite_relevancy_passes_active_branch_atom_to_theory() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _, then_atom, ..) =
        create_ite_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    // Trail: cond=true (var 1), then_atom=true (var 2)
    // Since cond=true, then_atom is in the ACTIVE branch and should pass through.
    let trail = vec![
        Literal::positive(Variable::new(1)), // cond = true
        Literal::positive(Variable::new(2)), // then_atom = true (active branch)
    ];
    let ctx = MockContext::new().with_trail(trail).with_level(1);
    let _ = ext.propagate(&ctx);

    assert!(
        ext.theory
            .assertions
            .iter()
            .any(|(t, v)| *t == then_atom && *v),
        "active-branch atom should be asserted to theory"
    );
    assert!(
        ext.ite_deferred_atoms.is_empty(),
        "no atoms should be deferred for active branch"
    );
    assert_eq!(
        ext.eager_stats.ite_relevancy_skips, 0,
        "no ITE relevancy skips for active branch"
    );
}

#[test]
fn ite_relevancy_passes_atom_when_condition_unassigned() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _, _, else_atom, _) =
        create_ite_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    // Trail: only else_atom=true (var 3), cond (var 1) is NOT on the trail.
    // When the condition is unassigned, both branches are potentially active,
    // so the atom should pass through to the theory.
    let trail = vec![
        Literal::positive(Variable::new(3)), // else_atom = true
    ];
    let mut ctx = MockContext::new().with_level(1);
    // Manually set up the trail without setting cond's value
    ctx.trail = trail;
    ctx.values.insert(3, true); // else_atom assigned but cond not assigned

    let _ = ext.propagate(&ctx);

    assert!(
        ext.theory
            .assertions
            .iter()
            .any(|(t, v)| *t == else_atom && *v),
        "atom with unassigned condition should be asserted to theory"
    );
    assert!(
        ext.ite_deferred_atoms.is_empty(),
        "no atoms should be deferred when condition is unassigned"
    );
}

#[test]
fn ite_relevancy_does_not_defer_at_level_zero() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _, _, else_atom, _) =
        create_ite_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    // At decision level 0, ITE filtering is disabled to ensure initial conflicts
    // are detected. This matches the `sat_level > 0` guard in propagate_impl().
    let trail = vec![
        Literal::positive(Variable::new(1)), // cond = true
        Literal::positive(Variable::new(3)), // else_atom = true (inactive branch)
    ];
    let ctx = MockContext::new().with_trail(trail).with_level(0);
    let _ = ext.propagate(&ctx);

    assert!(
        ext.theory.assertions.iter().any(|(t, _)| *t == else_atom),
        "at level 0, inactive-branch atoms should still be asserted"
    );
    assert!(
        ext.ite_deferred_atoms.is_empty(),
        "no atoms should be deferred at level 0"
    );
}

#[test]
fn ite_relevancy_backtrack_clears_deferred_atoms() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, ..) =
        create_ite_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    // Defer an atom
    let trail = vec![
        Literal::positive(Variable::new(1)), // cond = true
        Literal::positive(Variable::new(3)), // else_atom (inactive)
    ];
    let ctx = MockContext::new().with_trail(trail).with_level(1);
    let _ = ext.propagate(&ctx);
    assert_eq!(ext.ite_deferred_atoms.len(), 1);

    // #uflia-deferred-atom-loss: backtrack drops ONLY entries whose SAT
    // assignment level exceeds the backjump target. MockContext::var_level
    // reports Some(0) for every variable, so the deferred entry records
    // level 0 — a level-0 assignment SURVIVES a backtrack to level 0 and
    // must be retained (the former wholesale clear() permanently hid such
    // atoms from the theory: SAT never re-notifies surviving assignments).
    ext.backtrack(0);
    assert_eq!(
        ext.ite_deferred_atoms.len(),
        1,
        "backtrack must retain deferred atoms whose assignment level survives"
    );
    assert!(
        !ext.ite_deferred_atoms[0].3,
        "backtrack must reset the flushed flag on retained entries"
    );
}

#[test]
fn ite_relevancy_multi_guard_conflict_clears_guard() {
    // Test that an atom appearing in branches of two different ITE nodes
    // with different conditions gets its guard REMOVED to prevent
    // incorrect deferral.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::from(BigInt::from(0)));

    let cond1 = terms.mk_var("c1", Sort::Bool);
    let cond2 = terms.mk_var("c2", Sort::Bool);
    // Shared atom: (>= x 0)
    let shared_atom = terms.mk_ge(x, zero);
    let other1 = terms.mk_var("p1", Sort::Bool);
    let other2 = terms.mk_var("p2", Sort::Bool);

    // ITE1: (ite c1 shared_atom other1)
    let _ite1 = terms.mk_ite(cond1, shared_atom, other1);
    // ITE2: (ite c2 other2 shared_atom) -- shared_atom in ELSE branch this time
    let _ite2 = terms.mk_ite(cond2, other2, shared_atom);

    let var_to_term: HashMap<u32, TermId> = [
        (1, cond1),
        (2, cond2),
        (3, shared_atom),
        (4, other1),
        (5, other2),
    ]
    .into_iter()
    .collect();
    let term_to_var: HashMap<TermId, u32> = [
        (cond1, 1),
        (cond2, 2),
        (shared_atom, 3),
        (other1, 4),
        (other2, 5),
    ]
    .into_iter()
    .collect();
    let theory_atoms = vec![shared_atom];
    let theory_atom_set: HashSet<TermId> = theory_atoms.iter().copied().collect();

    let mut theory = MockTheory::new();
    let ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    // shared_atom (var 3) appears in ITE1 as then-branch (guarded by c1=true)
    // and in ITE2 as else-branch (guarded by c2=false).
    // These are CONFLICTING guards, so the guard should be CLEARED.
    let shared_idx = 3usize;
    let shared_word = shared_idx / 64;
    assert!(
        (ext.ite_guarded_bitset[shared_word] >> (shared_idx % 64)) & 1 == 0,
        "atom in multiple ITE contexts with different guards should NOT be marked as guarded"
    );
}

#[test]
fn ite_relevancy_nested_ite_guards_inner_atoms_by_outer_condition() {
    // #8065 Phase 2: nested ITE after ITE lifting.
    //   outer: (ite c1 inner_ite atom3)
    //   inner: (ite c2 atom1 atom2)
    //
    // After recursive branch scanning, atom1 and atom2 (branches of the
    // inner ITE) should be guarded by the OUTER condition c1 (is_then=true),
    // because collect_branch_atoms walks into nested Bool-sorted ITEs and
    // assigns the outermost guard. atom3 is guarded by c1 (is_then=false).
    //
    // However, the inner ITE loop iteration also visits inner_ite directly,
    // assigning atom1 guarded by c2 (is_then=true) and atom2 by c2
    // (is_then=false). Since atom1 now has TWO different guards (c1 from
    // the outer walk and c2 from the inner walk), the multi-guard conflict
    // logic should CLEAR its guard. Same for atom2.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::from(BigInt::from(0)));
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let two = terms.mk_rational(BigRational::from(BigInt::from(2)));

    let c1 = terms.mk_var("c1", Sort::Bool);
    let c2 = terms.mk_var("c2", Sort::Bool);
    let atom1 = terms.mk_ge(x, zero); // (>= x 0)
    let atom2 = terms.mk_ge(x, one); // (>= x 1)
    let atom3 = terms.mk_ge(x, two); // (>= x 2)

    // inner: (ite c2 atom1 atom2)  -- Bool-sorted
    let inner_ite = terms.mk_ite(c2, atom1, atom2);
    // outer: (ite c1 inner_ite atom3)  -- Bool-sorted
    let _outer_ite = terms.mk_ite(c1, inner_ite, atom3);

    let var_to_term: HashMap<u32, TermId> = [
        (1, c1),
        (2, c2),
        (3, atom1),
        (4, atom2),
        (5, atom3),
        (6, inner_ite),
    ]
    .into_iter()
    .collect();
    let term_to_var: HashMap<TermId, u32> = [
        (c1, 1),
        (c2, 2),
        (atom1, 3),
        (atom2, 4),
        (atom3, 5),
        (inner_ite, 6),
    ]
    .into_iter()
    .collect();
    let theory_atoms = vec![atom1, atom2, atom3];
    let theory_atom_set: HashSet<TermId> = theory_atoms.iter().copied().collect();

    let mut theory = MockTheory::new();
    let ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    // atom1 (var 3): guarded by c1 (outer walk) AND by c2 (inner walk).
    // Different guards => conflict => guard CLEARED.
    let atom1_idx = 3usize;
    let atom1_word = atom1_idx / 64;
    assert!(
        (ext.ite_guarded_bitset[atom1_word] >> (atom1_idx % 64)) & 1 == 0,
        "atom1 has conflicting guards from outer and inner ITE => guard should be cleared"
    );

    // atom2 (var 4): same situation -- guarded by c1 and by c2.
    let atom2_idx = 4usize;
    let atom2_word = atom2_idx / 64;
    assert!(
        (ext.ite_guarded_bitset[atom2_word] >> (atom2_idx % 64)) & 1 == 0,
        "atom2 has conflicting guards from outer and inner ITE => guard should be cleared"
    );

    // atom3 (var 5): only guarded by c1 (is_then=false), no conflict.
    let atom3_idx = 5usize;
    let atom3_word = atom3_idx / 64;
    assert!(
        (ext.ite_guarded_bitset[atom3_word] >> (atom3_idx % 64)) & 1 != 0,
        "atom3 only appears in one ITE context => guard should be set"
    );
    assert_eq!(
        ext.ite_branch_guards[atom3_idx],
        (1, false),
        "atom3 is in else-branch of outer ITE, guarded by c1 (var 1)"
    );
}

#[test]
fn ite_relevancy_multiple_ite_same_condition_defers_all_inactive() {
    // Two ITEs sharing the same condition variable:
    //   ITE1: (ite c atom1 other1)
    //   ITE2: (ite c atom2 other2)
    //
    // When c=true, then-branches (atom1, atom2) are active and else-branches
    // (other1, other2) are inactive. Both inactive atoms should be deferred
    // and the ite_relevancy_skips counter should be 2.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::from(BigInt::from(0)));
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let two = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));

    let cond = terms.mk_var("cond", Sort::Bool);
    let atom1 = terms.mk_ge(x, zero); // then-branch of ITE1
    let other1 = terms.mk_ge(x, one); // else-branch of ITE1
    let atom2 = terms.mk_ge(x, two); // then-branch of ITE2
    let other2 = terms.mk_ge(x, three); // else-branch of ITE2

    let _ite1 = terms.mk_ite(cond, atom1, other1);
    let _ite2 = terms.mk_ite(cond, atom2, other2);

    let var_to_term: HashMap<u32, TermId> =
        [(1, cond), (2, atom1), (3, other1), (4, atom2), (5, other2)]
            .into_iter()
            .collect();
    let term_to_var: HashMap<TermId, u32> =
        [(cond, 1), (atom1, 2), (other1, 3), (atom2, 4), (other2, 5)]
            .into_iter()
            .collect();
    let theory_atoms = vec![atom1, other1, atom2, other2];
    let theory_atom_set: HashSet<TermId> = theory_atoms.iter().copied().collect();

    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    // Trail: cond=true (var 1), then other1=true (var 3), other2=true (var 5).
    // other1 is in else-branch of ITE1 (inactive when cond=true).
    // other2 is in else-branch of ITE2 (inactive when cond=true).
    // Both should be deferred.
    let trail = vec![
        Literal::positive(Variable::new(1)), // cond = true
        Literal::positive(Variable::new(3)), // other1 = true (inactive)
        Literal::positive(Variable::new(5)), // other2 = true (inactive)
    ];
    let ctx = MockContext::new().with_trail(trail).with_level(1);
    let _ = ext.propagate(&ctx);

    assert_eq!(
        ext.ite_deferred_atoms.len(),
        2,
        "both inactive-branch atoms should be deferred"
    );
    assert_eq!(
        ext.eager_stats.ite_relevancy_skips, 2,
        "ITE relevancy skip counter should be 2 for two deferred atoms"
    );

    // The active-branch atoms (atom1, atom2) should NOT be deferred.
    // They weren't on the trail, so they shouldn't be in deferred either.
    assert!(
        !ext.ite_deferred_atoms
            .iter()
            .any(|&(t, _, _, _)| t == atom1 || t == atom2),
        "active-branch atoms should not be in deferred set"
    );
}

// =========================================================================
// Native theory-bound propagation dispatch contract tests (#8409)
// =========================================================================

#[test]
fn native_theory_propagation_supported_profile_defaults_to_disabled_fallback() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, xyz) = create_test_setup();
    let x = xyz[0];
    let profile =
        NativeTheoryPropagationProfile::external_codegen_backend_bound_propagation(2, 2, 4, 4);
    let mut theory = MockTheory::new().with_native_theory_propagation_profile(profile);
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    assert_eq!(
        ext.native_theory_propagation_dispatch,
        NativeTheoryPropagationDispatch::DisabledByControl,
        "native theory-bound propagation must be fail-closed by default"
    );
    assert_eq!(ext.eager_stats.native_theory_prop_disabled, 1);
    assert_eq!(ext.eager_stats.native_theory_prop_eligible, 0);

    let ctx = MockContext::new().with_trail(vec![Literal::positive(Variable::new(1))]);
    let result = ext.propagate(&ctx);

    assert!(
        result.clauses.is_empty(),
        "disabled native profile should keep ordinary eager fallback behavior"
    );
    assert_eq!(
        ext.theory.assertions,
        vec![(x, true)],
        "fallback path must still assert the theory literal"
    );
}

#[test]
fn native_theory_propagation_enabled_control_rejects_unsupported_theory() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    ext.recompute_native_theory_propagation_dispatch_for_test(
        NativeTheoryPropagationControl::EnabledForEligibleProfiles,
    );

    assert_eq!(
        ext.native_theory_propagation_dispatch,
        NativeTheoryPropagationDispatch::UnsupportedTheory,
        "enabled control must still reject theories without metadata"
    );
}

#[test]
fn native_theory_propagation_enabled_control_rejects_partial_native_coverage() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let profile =
        NativeTheoryPropagationProfile::external_codegen_backend_bound_propagation(2, 1, 4, 4);
    let mut theory = MockTheory::new().with_native_theory_propagation_profile(profile);
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    ext.recompute_native_theory_propagation_dispatch_for_test(
        NativeTheoryPropagationControl::EnabledForEligibleProfiles,
    );

    assert_eq!(
        ext.native_theory_propagation_dispatch,
        NativeTheoryPropagationDispatch::PartialNativeCoverage,
        "native dispatch is eligible only when every compiled var has native coverage"
    );
}

#[test]
fn native_theory_propagation_enabled_control_rejects_non_small_atoms() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let profile =
        NativeTheoryPropagationProfile::external_codegen_backend_bound_propagation(2, 2, 4, 3);
    let mut theory = MockTheory::new().with_native_theory_propagation_profile(profile);
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    ext.recompute_native_theory_propagation_dispatch_for_test(
        NativeTheoryPropagationControl::EnabledForEligibleProfiles,
    );

    assert_eq!(
        ext.native_theory_propagation_dispatch,
        NativeTheoryPropagationDispatch::NonSmallAtomFallback,
        "non-small bound atoms must keep the interpreted fallback"
    );
}

// =========================================================================
// JIT Theory Dispatch Table tests (#8177)
// =========================================================================

/// Verify that the dispatch table is built during construction when the
/// `jit` feature is enabled and theory atoms exist.
#[test]
#[cfg(feature = "jit")]
fn dispatch_table_built_during_construction() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    assert!(
        ext.jit_dispatch_table.is_some(),
        "dispatch table should be built when theory atoms exist"
    );
    let table = ext.jit_dispatch_table.as_ref().unwrap();
    // All 3 theory atoms (x, y, z) should be in the dispatch table.
    assert_eq!(
        table.len(),
        3,
        "dispatch table should contain all 3 theory atoms"
    );
}

/// Verify that the dispatch table routes Assert correctly through the
/// JIT fast path during propagation.
#[test]
#[cfg(feature = "jit")]
fn dispatch_table_propagation_asserts_atoms() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, xyz) = create_test_setup();
    let x = xyz[0];
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    // Simulate propagation with a trail containing a positive assignment to x.
    let mut ctx = MockContext::new();
    ctx.trail = vec![Literal::positive(Variable::new(1))]; // x = true
    ctx.values.insert(1, true);

    let result = ext.propagate(&ctx);
    // The mock theory returns Sat, so propagation should succeed.
    assert!(
        result.clauses.is_empty(),
        "no conflict clauses on Sat result"
    );
    // x should have been asserted to the theory solver.
    assert_eq!(
        ext.theory.assertions.len(),
        1,
        "one theory atom should be asserted"
    );
    assert_eq!(ext.theory.assertions[0], (x, true));
}

/// Verify that the dispatch table is preserved through the
/// take_cached_data / new_with_cached_data round trip.
#[test]
#[cfg(feature = "jit")]
fn dispatch_table_cached_data_round_trip() {
    let (_terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();

    // Build extension with dispatch table.
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        None, // no TermStore needed for this test
        None,
    );
    assert!(ext.jit_dispatch_table.is_some());

    // Extract cached data (dispatch table is rebuilt each iteration, not cached).
    let mut cached = ext.take_cached_data();

    // Rebuild extension from cached data.
    let ext2 = TheoryExtension::new_with_cached_data(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        &mut cached,
    );
    assert!(
        ext2.jit_dispatch_table.is_some(),
        "rebuilt extension should have dispatch table from cache"
    );
    assert_eq!(ext2.jit_dispatch_table.as_ref().unwrap().len(), 3);
}

/// Verify that the dispatch table correctly skips non-theory atoms
/// during propagation (they produce TheoryDispatchResult::Skip).
#[test]
#[cfg(feature = "jit")]
fn dispatch_table_skips_non_theory_atoms() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    // Assign a variable (id=99) that is NOT a theory atom.
    let mut ctx = MockContext::new();
    ctx.trail = vec![Literal::positive(Variable::new(99))];
    ctx.values.insert(99, true);

    let result = ext.propagate(&ctx);
    assert!(
        result.clauses.is_empty(),
        "no conflict clauses for non-theory atom"
    );
    // No theory atoms should be asserted.
    assert_eq!(
        ext.theory.assertions.len(),
        0,
        "non-theory atom should not be asserted to theory solver"
    );
}
