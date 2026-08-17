// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independent replay for exact finite-quantifier SAT authority.
//!
//! Universal expansion stays restricted to the audited full-BV and guarded
//! single-Int routes. Existential expansion has a different semantic shape:
//! the canonical expander retains the complete guarded body at every point and
//! returns `None` unless every non-finite carrier is bounded, so standalone
//! success is an exact disjunction. A direct `not (exists ...)` root is replayed
//! by expanding only its single Int child and rebuilding the same shell.
//!
//! Producer evidence must still name the byte-identical ground replacement;
//! this module is an independent authored-syntax check, not blanket trust in
//! the expansion capability.

use ay_core::{Sort, TermData, TermId, TermStore};

use crate::ematching::contains_quantifier;
use crate::executor::quantifier_loop::ExactFiniteExpansionEvidence;
use crate::executor::Executor;
use crate::executor_types::{Result, SolveResult};

impl Executor {
    /// Install exact finite-expansion SAT authority after all nested probes.
    ///
    /// The early preprocessing exit can solve a genuinely quantifier-free
    /// equivalent before E-matching exists. Re-authenticate that exact
    /// transformation only after all pre-restoration nested probes have
    /// finished, validate the final retained model against the complete
    /// expanded vector, and seal the grant to that model. Installing earlier
    /// would let a later certificate probe replace the model while leaving
    /// syntactic expansion evidence behind.
    pub(super) fn install_finite_expansion_if_sat(
        &mut self,
        result: &Result<SolveResult>,
        full_ematching_coverage: bool,
        original: Option<&[TermId]>,
        expansion: Option<&ExactFiniteExpansionEvidence>,
    ) {
        let (Ok(SolveResult::Sat), true, Some(original), Some(expansion)) =
            (result, full_ematching_coverage, original, expansion)
        else {
            return;
        };
        if self.install_exact_finite_expansion_sat_authority(original, expansion) {
            // Canonical equivalence plus exact-model validation over every
            // expanded root and every authored ground sibling is the complete
            // validation for this route. Running the generic post-restore
            // validator would skip the authored forall, mutate/replace the
            // sealed model in fallback probes, and discard the stronger typed
            // authority.
            self.defer_model_validation = false;
            self.last_model_validated = true;
        }
    }
}

pub(super) fn replay(terms: &mut TermStore, root: TermId) -> Option<TermId> {
    if let TermData::Not(inner) = terms.get(root).clone() {
        return replay_negated_existential(terms, inner);
    }
    replay_quantifier(terms, root)
}

fn replay_negated_existential(terms: &mut TermStore, inner: TermId) -> Option<TermId> {
    let TermData::Exists(vars, body, _) = terms.get(inner).clone() else {
        return None;
    };
    if vars.len() != 1 || vars[0].1 != Sort::Int || contains_quantifier(terms, body) {
        return None;
    }
    let expanded = replay_quantifier(terms, inner)?;
    Some(terms.mk_not(expanded))
}

fn replay_quantifier(terms: &mut TermStore, root: TermId) -> Option<TermId> {
    let (vars, body, is_forall) = match terms.get(root).clone() {
        TermData::Forall(vars, body, _) => (vars, body, true),
        TermData::Exists(vars, body, _) => (vars, body, false),
        _ => return None,
    };
    if vars.is_empty() || contains_quantifier(terms, body) {
        return None;
    }
    if is_forall {
        let all_bv = vars.iter().all(|(_, sort)| matches!(sort, Sort::BitVec(_)));
        let guarded_single_int = vars.len() == 1 && vars[0].1 == Sort::Int;
        if !all_bv && !guarded_single_int {
            return None;
        }
    }
    let (expanded, _) = crate::skolemize::finite_domain_expand_with_instances(terms, root)?;
    if contains_quantifier(terms, expanded) {
        return None;
    }
    let (normalized, provenance) =
        crate::skolemize::skolemize_deep_with_provenance(terms, expanded, true);
    provenance
        .is_empty()
        .then_some(normalized.unwrap_or(expanded))
}

#[cfg(test)]
mod tests {
    use ay_core::term::Symbol;
    use num_bigint::BigInt;

    use super::*;

    fn bounded_exists(terms: &mut TermStore, vars: Vec<(String, Sort)>) -> TermId {
        let x = terms.mk_var(&vars[0].0, vars[0].1.clone());
        let zero = terms.mk_int(BigInt::from(0));
        let three = terms.mk_int(BigInt::from(3));
        let lower = terms.mk_le(zero, x);
        let upper = terms.mk_le(x, three);
        let predicate = terms.mk_app(Symbol::named("P"), [x], Sort::Bool);
        let body = terms.mk_and(vec![lower, upper, predicate]);
        terms.mk_exists(vars, body)
    }

    #[test]
    fn negated_single_int_exists_replays_byte_identically() {
        let mut terms = TermStore::new();
        let exists = bounded_exists(&mut terms, vec![("x".to_string(), Sort::Int)]);
        let root = terms.mk_not(exists);
        let canonical = replay(&mut terms, root).expect("narrow negated root must replay");
        let producer = crate::skolemize::expand_finite_domain_subterms(&mut terms, root);

        assert_eq!(canonical, producer);
        assert!(!contains_quantifier(&terms, canonical));
    }

    #[test]
    fn negated_exists_shell_declines_wrong_sort_multiple_binders_and_nesting() {
        let mut terms = TermStore::new();
        let bool_name = "b".to_string();
        let b = terms.mk_var(&bool_name, Sort::Bool);
        let bool_exists = terms.mk_exists(vec![(bool_name, Sort::Bool)], b);
        let bool_root = terms.mk_not(bool_exists);
        assert!(replay(&mut terms, bool_root).is_none());

        let two_vars = vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)];
        let multi_exists = bounded_exists(&mut terms, two_vars);
        let multi_root = terms.mk_not(multi_exists);
        assert!(replay(&mut terms, multi_root).is_none());

        let inner_name = "i".to_string();
        let inner_var = terms.mk_var(&inner_name, Sort::Int);
        let inner_body = terms.mk_eq(inner_var, inner_var);
        let inner = terms.mk_forall(vec![(inner_name, Sort::Int)], inner_body);
        let outer = terms.mk_exists(vec![("x".to_string(), Sort::Int)], inner);
        let nested_root = terms.mk_not(outer);
        assert!(replay(&mut terms, nested_root).is_none());
    }
}
