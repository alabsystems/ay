// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::TheoryLemmaKind;

struct Fixture {
    terms: TermStore,
    len: TermId,
    one: TermId,
    x: TermId,
    p: TermId,
    q: TermId,
    hyp: TermId,
}

impl Fixture {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let len = terms.mk_var("projection_len", Sort::Int);
        let one = terms.mk_int(1.into());
        let x = terms.mk_var("projection_x", Sort::Int);
        let p = terms.mk_var("projection_p", Sort::Bool);
        let q = terms.mk_var("projection_q", Sort::Bool);
        let hyp = terms.mk_app(Symbol::named("="), [len, one], Sort::Bool);
        Self {
            terms,
            len,
            one,
            x,
            p,
            q,
            hyp,
        }
    }

    fn app(&mut self, name: &str, args: &[TermId]) -> TermId {
        self.terms.mk_app(Symbol::named(name), args, Sort::Bool)
    }

    fn guarded(&mut self, body: TermId) -> TermId {
        let not_hyp = self.terms.mk_not_raw(self.hyp);
        self.app("or", &[not_hyp, body])
    }

    fn fragment(
        &mut self,
        source: TermId,
        unit: TermId,
        with_hyp: bool,
    ) -> Result<ExactOriginalProofFragment, ExactOriginalProofError> {
        let mut vars = HashMap::default();
        vars.insert(0, unit);
        let mut trace = ClauseTrace::new();
        trace.add_clause(1, vec![Literal::positive(Variable::new(0))], true);
        let roots = if with_hyp {
            vec![self.hyp, source]
        } else {
            vec![source]
        };
        SatProofManager::new(&vars, &mut self.terms)
            .build_exact_original_proof_fragment(&trace, &roots)
    }

    fn check(&mut self, source: TermId, unit: TermId) {
        let fragment = self
            .fragment(source, unit, true)
            .expect("checked projection should derive unit");
        let step = fragment.bindings[&1].proof_id;
        let mut proof = fragment.proof;
        assert!(proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::GroundEqualitySubstitution,
                ..
            }
        )));
        for step in &proof.steps {
            if let ProofStep::Assume(term) = step {
                assert!(
                    [self.hyp, source].contains(term),
                    "an intermediate image was assumed"
                );
            }
        }
        let not_unit = self.terms.mk_not_raw(unit);
        let opposite = proof.add_assume(not_unit, None);
        proof.add_resolution(Vec::new(), unit, step, opposite);
        ay_proof::check_proof_strict(&proof, &self.terms).unwrap();
    }
}

#[test]
fn ground_substitution_projects_an_authored_conjunct_without_assuming_the_image() {
    let mut f = Fixture::new();
    let lt = f.app("<", &[f.x, f.len]);
    let body = f.app("and", &[lt, f.p]);
    let source = f.guarded(body);
    f.check(source, f.p);
}

#[test]
fn ground_substitution_projects_a_normalized_integer_comparison() {
    let mut f = Fixture::new();
    let lt = f.app("<", &[f.x, f.len]);
    let body = f.app("and", &[lt, f.p]);
    let source = f.guarded(body);
    let zero = f.terms.mk_int(0.into());
    let unit = f.app("<=", &[f.x, zero]);
    f.check(source, unit);
}

#[test]
fn ground_substitution_reorders_disjunctions_with_duplicate_literals() {
    for duplicate in [false, true] {
        let mut f = Fixture::new();
        let lt = f.app("<", &[f.x, f.len]);
        let not_lt = f.terms.mk_not_raw(lt);
        let mut before = vec![not_lt, f.p];
        if duplicate {
            before.push(f.p);
        }
        let source = f.app("or", &before);
        let lt_one = f.app("<", &[f.x, f.one]);
        let not_lt_one = f.terms.mk_not_raw(lt_one);
        let mut after = vec![f.p, not_lt_one];
        if duplicate {
            after.insert(0, f.p);
        }
        let unit = f.app("or", &after);
        f.check(source, unit);
    }
}

#[test]
fn ground_substitution_does_not_project_a_disjunct_or_invent_an_equality() {
    let mut f = Fixture::new();
    let body = f.app("or", &[f.p, f.q]);
    let source = f.guarded(body);
    assert!(f.fragment(source, f.p, true).is_err());
    // len=1, p=false, q=true satisfies both roots and falsifies p.
    let body = f.app("and", &[f.p, f.q]);
    let source = f.guarded(body);
    assert!(f.fragment(source, f.p, false).is_err());
    // Without len=1, the guard can be true even when p=false.
}

#[test]
fn ground_substitution_projection_rejects_indexed_equality_hypotheses() {
    let mut f = Fixture::new();
    let body = f.app("and", &[f.p, f.q]);
    let source = f.guarded(body);
    // An indexed predicate does not establish the named equality in the guard.
    f.hyp = f
        .terms
        .mk_app(Symbol::indexed("=", vec![0]), [f.len, f.one], Sort::Bool);
    assert!(f.fragment(source, f.p, true).is_err());
}

#[test]
fn ground_substitution_projection_preserves_bit_extraction_identity() {
    let mut f = Fixture::new();
    let x = f.terms.mk_var("extract_x", Sort::bitvec(8));
    let zero = f.terms.mk_bitvec(0.into(), 1);
    let lo = f
        .terms
        .mk_app(Symbol::indexed("extract", vec![0, 0]), [x], Sort::bitvec(1));
    let hi = f
        .terms
        .mk_app(Symbol::indexed("extract", vec![1, 1]), [x], Sort::bitvec(1));
    let p = f.app("=", &[lo, zero]);
    let q = f.app("=", &[hi, zero]);
    let body = f.app("and", &[p, f.p]);
    let source = f.guarded(body);
    assert!(f.fragment(source, q, true).is_err());
    f.check(source, p);
}
