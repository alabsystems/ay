// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

struct Fixture {
    terms: TermStore,
    roots: Vec<TermId>,
    records: HashMap<TermId, (TermId, u32)>,
    entries: HashMap<TermId, (TermId, TermId, u32)>,
    before: TermId,
    after: TermId,
    license: TermId,
    target: TermId,
}

impl Fixture {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let before = terms.mk_var("rewritten_root", Sort::Bool);
        let first = terms.mk_var("first", Sort::Bool);
        let target = terms.mk_var("target", Sort::Bool);
        let last = terms.mk_var("last", Sort::Bool);
        // Raw nesting is intentional: projection must retain both positions.
        let nested = terms.mk_app(Symbol::named("and"), [target, last], Sort::Bool);
        let after = terms.mk_app(Symbol::named("and"), [first, nested], Sort::Bool);
        let license = terms.mk_app(Symbol::named("="), [before, after], Sort::Bool);
        Self {
            terms,
            roots: vec![before, license],
            records: HashMap::from_iter([(after, (before, 1))]),
            entries: HashMap::from_iter([(before, (after, license, 1))]),
            before,
            after,
            license,
            target,
        }
    }

    fn plan(&mut self) -> Option<(Proof, ProofId)> {
        let source_set = self.roots.iter().copied().collect();
        let mut cx = PlanCx::new(
            &source_set,
            &self.roots,
            &self.records,
            &self.entries,
            &[],
            false,
        );
        let mut planner = PropagationChainPlanner {
            terms: &mut self.terms,
        };
        let result = planner.plan_derive_clause(&mut cx, self.target);
        assert!(cx.in_progress.is_empty(), "every recursive attempt unwinds");
        result.map(|conclusion| (cx.chain, conclusion))
    }

    fn assert_strict(&mut self) {
        assert!(!self.records.contains_key(&self.target));
        let (mut proof, conclusion) = self.plan().expect("derive unrecorded exact conjunct");
        assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &self.roots).is_ok());
        assert!(proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::AndPos(_),
                ..
            }
        )));
        let opposite = self.terms.mk_not_raw(self.target);
        let contrary = proof.add_assume(opposite, None);
        proof.add_resolution(Vec::new(), self.target, conclusion, contrary);
        let quality = ay_proof::check_proof_strict(&proof, &self.terms)
            .expect("each rewrite and projection is independently replayed");
        assert!(quality.is_complete());
        assert_eq!(quality.trust_count, 0);
    }
}

#[test]
fn recorded_after_root_derives_unrecorded_nested_conjunct() {
    Fixture::new().assert_strict();
}

#[test]
fn rewritten_conjunct_requires_current_authored_license_and_stamp() {
    let mut missing = Fixture::new();
    missing.roots.retain(|root| *root != missing.license);
    assert!(missing.plan().is_none());

    let mut late = Fixture::new();
    late.entries.get_mut(&late.before).unwrap().2 = 2;
    assert!(
        late.plan().is_none(),
        "future entries cannot license stamp 1"
    );

    let mut fresh = Fixture::new();
    fresh.assert_strict();
}

#[test]
fn rewritten_conjunct_rejects_forged_parent_and_non_and_descent() {
    let mut forged = Fixture::new();
    let foreign = forged.terms.mk_var("foreign", Sort::Bool);
    let wrong = forged
        .terms
        .mk_app(Symbol::named("and"), [foreign, forged.target], Sort::Bool);
    forged.records.clear();
    forged.records.insert(wrong, (forged.before, 1));
    assert!(
        forged.plan().is_none(),
        "record must reproduce its exact after-root"
    );

    let mut disjunction = Fixture::new();
    let alternative = disjunction.terms.mk_var("alternative", Sort::Bool);
    let after = disjunction.terms.mk_app(
        Symbol::named("or"),
        [disjunction.target, alternative],
        Sort::Bool,
    );
    let license =
        disjunction
            .terms
            .mk_app(Symbol::named("="), [disjunction.before, after], Sort::Bool);
    disjunction.roots = vec![disjunction.before, license];
    disjunction.records = HashMap::from_iter([(after, (disjunction.before, 1))]);
    disjunction.entries = HashMap::from_iter([(disjunction.before, (after, license, 1))]);
    assert!(
        disjunction.plan().is_none(),
        "a possible disjunct is not a consequence"
    );
}

#[test]
fn rewritten_conjunct_cycles_decline_without_parent_assumptions() {
    let mut fixture = Fixture::new();
    let other = fixture.terms.mk_var("other", Sort::Bool);
    let parent = fixture
        .terms
        .mk_app(Symbol::named("and"), [fixture.target, other], Sort::Bool);
    fixture.roots.clear();
    fixture.entries.clear();
    fixture.records =
        HashMap::from_iter([(fixture.after, (parent, 1)), (parent, (fixture.after, 1))]);
    assert!(fixture.plan().is_none());
}

#[test]
fn rewritten_conjunct_scan_precharges_and_bounds_deep_paths() {
    let mut fixture = Fixture::new();
    let source_set = fixture.roots.iter().copied().collect();
    let mut cx = PlanCx::new(
        &source_set,
        &fixture.roots,
        &fixture.records,
        &fixture.entries,
        &[],
        false,
    );
    cx.budget = 0;
    let original_terms = fixture.terms.len();
    let mut planner = PropagationChainPlanner {
        terms: &mut fixture.terms,
    };
    assert!(planner
        .plan_rewritten_conjunct(&mut cx, fixture.target)
        .is_none());
    assert_eq!(cx.chain.steps, [] as [ProofStep; 0]);
    assert_eq!(planner.terms.len(), original_terms);

    cx.budget = PLAN_NODE_BUDGET;
    let sibling = planner.terms.mk_var("deep_sibling", Sort::Bool);
    let mut deep = fixture.target;
    for _ in 0..4096 {
        deep = planner
            .terms
            .mk_app(Symbol::named("and"), [deep, sibling], Sort::Bool);
    }
    let original_terms = planner.terms.len();
    assert!(matches!(
        planner.rewritten_conjunct_path(&mut cx, deep, fixture.target),
        Some(AndPath::Missing)
    ));
    assert_eq!(cx.chain.steps, [] as [ProofStep; 0]);
    assert_eq!(planner.terms.len(), original_terms);
    assert!(
        cx.budget > 0,
        "depth cap stops before the shared work budget"
    );
}
