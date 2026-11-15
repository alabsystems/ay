// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The replay that mints [`CheckedExactFiniteExpansionUnsat`]: the binder
//! audit, the literal-bound expansion of the immutable public roots and, for a
//! refutation the mandatory-artifact gate withheld, the source-derived pass
//! (#source-derived-unsat-replay).
//!
//! The token, its re-validation (`is_current`) and the elementary contradiction
//! checker stay in the parent module. Re-validation re-runs that checker on the
//! sealed expansion; it never re-expands, so nothing here is on that path.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, TermData};
use ay_core::{Sort as CoreSort, TermId, TermStore as CoreTermStore};

use super::{
    exact_finite_expansion_ground_contradiction, exact_finite_expansion_interpreted_operators,
    exact_operator_identities_are_unshadowed, CheckedExactFiniteExpansionUnsat,
    ExactFiniteExpansionContradiction, EXACT_CLOSED_FORALL_WORK_LIMIT,
};
use crate::executor::Executor;

/// Validate the binder-sensitive part of the quantified body before invoking
/// the production expander.
///
/// `subst_vars` indexes substitutions by core name.  A malformed low-level
/// TermStore could otherwise give one binder name multiple Var identities or a
/// Var of the wrong sort, causing the replay to replace a term that is not a
/// well-sorted occurrence of that binder.  Normal elaboration prevents this;
/// the certificate checker enforces it independently because low-level Context
/// mutation is part of the repository's adversarial test model.
fn exact_finite_binder_occurrences_are_well_sorted(
    terms: &CoreTermStore,
    body: TermId,
    binders: &[(String, CoreSort)],
) -> bool {
    exact_finite_binder_identities(terms, body, binders).is_some()
}

/// [`exact_finite_binder_occurrences_are_well_sorted`]'s audit, returning the
/// one `Var` identity each binder name is spelled with in `body` (a name that
/// does not occur is absent).
///
/// The audit alone proves one identity PER SPELLING, not that the identity is
/// the binder's. That is enough for an authored body: the frontend mints every
/// binder a name no declaration holds yet, so a later declaration taking that
/// spelling cannot occur inside it. A body REWRITTEN by folding authored
/// ground terms in can hold such a declaration, so a caller auditing one must
/// also compare the identities returned here with the authored body's.
fn exact_finite_binder_identities(
    terms: &CoreTermStore,
    body: TermId,
    binders: &[(String, CoreSort)],
) -> Option<HashMap<String, u32>> {
    let mut binder_sorts: HashMap<&str, &CoreSort> = HashMap::default();
    for (name, sort) in binders {
        if name.is_empty()
            || !matches!(sort, CoreSort::BitVec(width) if width.width > 0)
            || binder_sorts.insert(name.as_str(), sort).is_some()
        {
            return None;
        }
    }

    let mut remaining = EXACT_CLOSED_FORALL_WORK_LIMIT;
    let mut matched_var_ids: HashMap<String, u32> = HashMap::default();
    let mut seen = HashSet::default();
    let mut stack = vec![body];
    while let Some(term) = stack.pop() {
        if remaining == 0 || terms.entry_stamp(term).is_none() {
            return None;
        }
        remaining -= 1;
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Const(constant) => {
                let well_sorted = match (constant, terms.sort(term)) {
                    (Constant::Bool(_), CoreSort::Bool)
                    | (Constant::Int(_), CoreSort::Int)
                    | (Constant::Rational(_), CoreSort::Real)
                    | (Constant::String(_), CoreSort::String) => true,
                    (
                        Constant::BitVec { width, .. },
                        CoreSort::BitVec(ay_core::BitVecSort { width: sort_width }),
                    ) => width == sort_width && *width > 0,
                    _ => false,
                };
                if !well_sorted {
                    return None;
                }
            }
            TermData::Var(name, id) => {
                if let Some(expected_sort) = binder_sorts.get(name.as_str()) {
                    if terms.sort(term) != *expected_sort {
                        return None;
                    }
                    match matched_var_ids.get(name) {
                        Some(seen_id) if seen_id != id => return None,
                        Some(_) => {}
                        None => {
                            matched_var_ids.insert(name.clone(), *id);
                        }
                    }
                }
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => {
                if terms.sort(term) != &CoreSort::Bool || terms.sort(*inner) != &CoreSort::Bool {
                    return None;
                }
                stack.push(*inner);
            }
            TermData::Ite(condition, then_term, else_term) => {
                if terms.sort(*condition) != &CoreSort::Bool
                    || terms.sort(*then_term) != terms.sort(*else_term)
                    || terms.sort(term) != terms.sort(*then_term)
                {
                    return None;
                }
                stack.extend([*condition, *then_term, *else_term]);
            }
            // The ordinary expander has capture-aware Let support, but the
            // exact source token intentionally keeps a smaller auditable
            // fragment. Parsed lets are normally elaborated away already.
            TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => return None,
            _ => return None,
        }
    }
    Some(matched_var_ids)
}

impl Executor {
    /// Independently re-expand the immutable public roots and prove a narrow
    /// ground contradiction in the complete replacement vector.
    ///
    /// This constructor is intentionally BV-forall-only.  Wide binders are
    /// accepted only when the canonical expander itself proves a bounded guard;
    /// small binders use its exhaustive finite carrier.  Every other quantified
    /// shape, nested quantifier, assumption-bearing query, stale source/root
    /// epoch, incomplete expansion, or non-elementary ground conflict declines.
    pub(in crate::executor) fn try_authorize_current_query_exact_finite_expansion_unsat(
        &mut self,
    ) -> Option<CheckedExactFiniteExpansionUnsat> {
        self.authorize_current_query_finite_expansion_unsat(false)
    }

    /// [`Self::try_authorize_current_query_exact_finite_expansion_unsat`], plus
    /// the source-derived replay (#source-derived-unsat-replay) when the
    /// literal-bound replay finds no contradiction.
    ///
    /// A guard bounded by a destructured datatype field (`outer!fld_len`,
    /// pinned by an authored defining equality) is unreadable to the literal
    /// replay, and a narrow binder's exhaustive carrier leaves every guard
    /// unevaluated, so the false instance never folds to a literal. This
    /// re-expands with the aggregate definitions and constants re-derived
    /// from the public roots ALONE, exactly as the SAT grant's replay
    /// (`replay_from_source`) does, under the same token and the same
    /// elementary contradiction check. Consulted only for a refutation the
    /// mandatory-artifact gate withheld, so like its SAT twin it is a last
    /// resort that can never preempt a more specific certificate.
    pub(in crate::executor) fn try_authorize_current_query_source_derived_finite_expansion_unsat(
        &mut self,
    ) -> Option<CheckedExactFiniteExpansionUnsat> {
        self.authorize_current_query_finite_expansion_unsat(true)
    }

    fn authorize_current_query_finite_expansion_unsat(
        &mut self,
        source_derived: bool,
    ) -> Option<CheckedExactFiniteExpansionUnsat> {
        if crate::executor::model::scoped_term_evaluation_override_active()
            || !self.exact_plain_hard_unsat_scope_is_current()
            || self.should_abort_theory_loop()
            || self.strict_unsat_presentation_required()
        {
            return None;
        }
        // Public-root replay must be independent of producer-local derived
        // bounds and BOOL_GROUND extras retained in finite-domain TLS.
        let _standalone_replay = crate::skolemize::scoped_standalone_finite_domain_replay();
        let (roots, root_entries) = {
            let epoch = self.unsat_query_epoch.as_ref()?;
            (epoch.assertions.clone(), epoch.assertion_entries.clone())
        };
        if roots.is_empty()
            || roots
                .iter()
                .any(|&root| self.ctx.terms.sort(root) != &CoreSort::Bool)
        {
            return None;
        }
        let interpreted_operators =
            exact_finite_expansion_interpreted_operators(&self.ctx.terms, &roots)?;
        if !exact_operator_identities_are_unshadowed(&self.ctx, &interpreted_operators) {
            return None;
        }
        let (expanded_roots, contradiction) =
            self.exact_finite_expansion_unsat_evidence(&roots, source_derived)?;
        if expanded_roots.len() != roots.len() {
            return None;
        }
        let expanded_root_entries = expanded_roots
            .iter()
            .map(|&root| self.ctx.terms.entry_stamp(root))
            .collect::<Option<Vec<_>>>()?;
        let term_snapshot = self.ctx.terms.snapshot_stamp();

        // Recheck after canonical replay: expansion can grow the term store but
        // cannot change the query/source epoch or any authored root entry.
        if !self.exact_plain_hard_unsat_scope_is_current()
            || self.should_abort_theory_loop()
            || !self.unsat_query_epoch.as_ref().is_some_and(|epoch| {
                epoch.assertions == roots && epoch.assertion_entries == root_entries
            })
            || !exact_operator_identities_are_unshadowed(&self.ctx, &interpreted_operators)
            || term_snapshot != self.ctx.terms.snapshot_stamp()
        {
            return None;
        }

        Some(CheckedExactFiniteExpansionUnsat {
            query_epoch: self.query_authority_epoch.clone(),
            source_declaration_stamp: self.ctx.source_context_stamp(),
            roots: roots.into_boxed_slice(),
            root_entries: root_entries.into_boxed_slice(),
            expanded_roots: expanded_roots.into_boxed_slice(),
            expanded_root_entries: expanded_root_entries.into_boxed_slice(),
            contradiction,
            interpreted_operators: interpreted_operators.into_boxed_slice(),
            term_snapshot,
        })
    }

    /// Expand every quantified public root and find the elementary ground
    /// contradiction for the finite-expansion UNSAT theorem.
    ///
    /// Pass 1 is the literal-bound standalone replay, unchanged. Pass 2 runs
    /// only for `source_derived` and only when pass 1 found no contradiction:
    /// each quantified root is re-expanded after the aggregate-definition fold
    /// and with the entailed constants, both re-derived from the public roots
    /// alone; a root that pass 2 cannot expand keeps its pass-1 expansion.
    /// Every conjunct either pass emits is an instance of an authored
    /// universal, rewritten only by equalities the authored roots assert, so
    /// the roots entail the whole expanded vector.
    fn exact_finite_expansion_unsat_evidence(
        &mut self,
        roots: &[TermId],
        source_derived: bool,
    ) -> Option<(Vec<TermId>, ExactFiniteExpansionContradiction)> {
        let mut standalone = Vec::with_capacity(roots.len());
        let mut quantified_roots = 0usize;
        for &root in roots {
            if !crate::ematching::contains_quantifier(&self.ctx.terms, root) {
                standalone.push(Some(root));
                continue;
            }
            quantified_roots += 1;
            let TermData::Forall(vars, body, _) = self.ctx.terms.get(root).clone() else {
                return None;
            };
            if vars.is_empty()
                || self.ctx.terms.sort(body) != &CoreSort::Bool
                || !exact_finite_binder_occurrences_are_well_sorted(&self.ctx.terms, body, &vars)
                || crate::ematching::contains_quantifier(&self.ctx.terms, body)
            {
                return None;
            }
            let expanded =
                crate::skolemize::finite_domain_expand_with_instances(&mut self.ctx.terms, root)
                    .map(|(expanded, _)| expanded)
                    .filter(|&expanded| {
                        self.ctx.terms.sort(expanded) == &CoreSort::Bool
                            && !crate::ematching::contains_quantifier(&self.ctx.terms, expanded)
                    });
            if expanded.is_none() && !source_derived {
                return None;
            }
            standalone.push(expanded);
        }
        if quantified_roots == 0 {
            return None;
        }
        if let Some(expanded) = standalone.iter().copied().collect::<Option<Vec<_>>>() {
            if let Some(found) =
                exact_finite_expansion_ground_contradiction(&self.ctx.terms, &expanded)
            {
                return Some((expanded, found));
            }
        }
        if !source_derived {
            return None;
        }
        let mut derived = Vec::with_capacity(roots.len());
        for (&root, pass_one) in roots.iter().zip(standalone) {
            let TermData::Forall(vars, body, _) = self.ctx.terms.get(root).clone() else {
                derived.push(root);
                continue;
            };
            // Pass 1 audited every quantified authored body, so this is `Some`.
            let authored = exact_finite_binder_identities(&self.ctx.terms, body, &vars)?;
            let expanded = self
                .source_derived_finite_expansion(root, roots, |terms, folded| {
                    // The fold moves authored ground terms under the binder
                    // before the expander substitutes binders BY NAME, so the
                    // folded body must pass the same binder-identity audit AND
                    // spell each binder only with the identity the authored
                    // body binds. A later declaration can take a binder's
                    // spelling; when the fold erases the binder's own
                    // occurrences (or the binder is vacuous), that foreign
                    // variable is the only one so spelled and passes the
                    // one-identity-per-name audit alone.
                    matches!(terms.get(folded), TermData::Forall(folded_vars, folded_body, _)
                    if *folded_vars == vars
                        && terms.sort(*folded_body) == &CoreSort::Bool
                        && !crate::ematching::contains_quantifier(terms, *folded_body)
                        && exact_finite_binder_identities(terms, *folded_body, folded_vars)
                            .is_some_and(|folded| {
                                folded.iter().all(|(name, id)| authored.get(name) == Some(id))
                            }))
                })
                .filter(|&expanded| self.ctx.terms.sort(expanded) == &CoreSort::Bool)
                .or(pass_one)?;
            derived.push(expanded);
        }
        let found = exact_finite_expansion_ground_contradiction(&self.ctx.terms, &derived)?;
        Some((derived, found))
    }
}
