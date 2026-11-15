// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ψ-conjunct roots and witness machinery for the negated-existential
//! ground-instantiation lane (#primes-negated-and-exists), split from the
//! producer so it stays inside the file-length ratchet. Everything here is
//! a hint: the consequence-replay stitcher and the strict validators
//! re-derive every step.

use super::*;

/// One authored clause-shaped root — `Not(And(…, E, …))`, or its elaborated
/// form `(or … (not E) …)` — whose only quantified literal is the negated
/// existential at `exists_index`; every other literal is quantifier-free.
/// `negate_args` recalls the `not_and` clausification (literals are the
/// negated conjuncts) versus the `or` form (literals verbatim).
pub(super) struct PsiNegatedExists {
    root: TermId,
    exists: TermId,
    exists_index: usize,
    bindings: Vec<(String, Sort)>,
    body: TermId,
    args: Vec<TermId>,
    negate_args: bool,
}

impl Executor {
    /// Skolemize the authored multi-binder positive existentials one
    /// binder at a time through the shared `qnt_join` + `sko` chain
    /// builder, returning the chain steps and their Skolem records (whose
    /// witnesses head the candidate columns in binder order).
    pub(super) fn authored_positive_exists_chains(
        &mut self,
        authored: &[TermId],
    ) -> (
        Vec<ExpansionStep>,
        Vec<crate::executor::SkolemInstanceRecord>,
    ) {
        let mut chain: Vec<ExpansionStep> = Vec::new();
        let mut records = Vec::new();
        let mut chained_roots = 0usize;
        for &root in authored {
            if chained_roots >= MAX_NEGATED_EXISTS_ROOTS {
                break;
            }
            let TermData::Exists(bindings, body, _) = self.ctx.terms.get(root).clone() else {
                continue;
            };
            if bindings.len() < 2
                || bindings.len() > MAX_BINDERS
                || crate::ematching::contains_quantifier(&self.ctx.terms, body)
            {
                continue;
            }
            let steps_before = chain.len();
            if crate::executor::qsat_route::skolemize_binders(
                &mut self.ctx.terms,
                root,
                root,
                true,
                &mut chain,
            )
            .is_ok()
            {
                chained_roots += 1;
                for step in &chain[steps_before..] {
                    if let ExpansionStep::Skolem(record) = step {
                        records.push(record.clone());
                    }
                }
            } else {
                chain.truncate(steps_before);
            }
        }
        (chain, records)
    }

    /// Plan ψ-conjunct roots: same dual + ground instances as the bare
    /// shape, except the dual record carries the co-units that discharge
    /// the root's other clause literals. The stitcher clausifies the root
    /// (`or` / `not_and`), derives each co-unit from the authored scope,
    /// and resolves the literals away to reach the `(not E)` unit — so a
    /// false ψ can never refute, and the probe only ever sees `¬φ[t⃗]`
    /// units.
    pub(super) fn plan_psi_negated_exists_instances(
        &mut self,
        authored: &[TermId],
        psi_roots: Vec<PsiNegatedExists>,
        bound_names: &ay_core::kani_compat::DetHashSet<String>,
        skolem: &[crate::executor::SkolemInstanceRecord],
        duals: &mut Vec<NegatedExistsDual>,
        records: &mut Vec<crate::ematching::ForallInstantiationProvenance>,
    ) {
        for psi in psi_roots.into_iter().take(MAX_NEGATED_EXISTS_ROOTS) {
            if records.len() >= MAX_GROUND_INSTANCES {
                break;
            }
            if psi.bindings.is_empty()
                || psi.bindings.len() > MAX_BINDERS
                || crate::ematching::contains_quantifier(&self.ctx.terms, psi.body)
            {
                continue;
            }
            // The unit that discharges each co-literal: the conjunct itself
            // under `not_and`; under `or`, the literal's complement.
            let mut co_units: Vec<TermId> = Vec::with_capacity(psi.args.len() - 1);
            for (index, &arg) in psi.args.iter().enumerate() {
                if index == psi.exists_index {
                    continue;
                }
                co_units.push(if psi.negate_args {
                    arg
                } else if let TermData::Not(inner) = self.ctx.terms.get(arg) {
                    *inner
                } else {
                    self.ctx.terms.mk_not_raw(arg)
                });
            }
            let negated_body = self.ctx.terms.mk_not_raw(psi.body);
            let forall = self.ctx.terms.mk_forall(psi.bindings.clone(), negated_body);
            let Some(tuples) = self.negated_exists_tuples(
                authored,
                &psi.bindings,
                bound_names,
                skolem,
                MAX_GROUND_INSTANCES - records.len(),
            ) else {
                continue;
            };
            let mut minted = 0usize;
            for tuple in tuples {
                let mut substitution: ay_core::kani_compat::DetHashMap<String, TermId> =
                    ay_core::kani_compat::DetHashMap::default();
                for ((name, _), &value) in psi.bindings.iter().zip(&tuple) {
                    substitution.insert(name.clone(), value);
                }
                let Some(instance) = crate::ematching::subst_vars_exact_qf(
                    &mut self.ctx.terms,
                    negated_body,
                    &substitution,
                ) else {
                    continue;
                };
                if crate::ematching::contains_quantifier(&self.ctx.terms, instance)
                    || records.iter().any(|r| r.instance == instance)
                {
                    continue;
                }
                records.push(crate::ematching::ForallInstantiationProvenance {
                    quantifier: forall,
                    binding: tuple,
                    instance,
                });
                minted += 1;
                if records.len() >= MAX_GROUND_INSTANCES {
                    break;
                }
            }
            if minted > 0 {
                duals.push(NegatedExistsDual {
                    not_exists_root: psi.root,
                    exists: psi.exists,
                    forall,
                    co_units,
                });
            }
        }
    }

    /// Hint-first bounded witness tuples for one existential's binders, or
    /// `None` when some binder sort has no ground candidate at all.
    pub(super) fn negated_exists_tuples(
        &self,
        authored: &[TermId],
        bindings: &[(String, Sort)],
        bound_names: &ay_core::kani_compat::DetHashSet<String>,
        skolem: &[crate::executor::SkolemInstanceRecord],
        limit: usize,
    ) -> Option<Vec<Vec<TermId>>> {
        let mut per_binder: Vec<Vec<TermId>> = Vec::with_capacity(bindings.len());
        for (_, sort) in bindings {
            // Hints first (positive-existential Skolem constants, then the
            // closed CEGQI binder values of this check-sat), then the
            // authored ground scan — see
            // `authored_negated_exists_witness_hints`.
            let candidates = self.negated_exists_witness_candidates(
                authored,
                sort,
                bound_names,
                skolem,
                MAX_WITNESSES_PER_SORT,
            );
            if candidates.is_empty() {
                note(|| {
                    "decline: a binder sort has no ground witness in the authored scope".into()
                });
                return None;
            }
            per_binder.push(candidates);
        }
        // Order is load-bearing: `bounded_tuples` leads with the diagonal,
        // but same-sort multi-binder existentials share ONE candidate column
        // per binder, so the positive Skolem witnesses in record order form
        // the STAIRCASE tuple (binder i gets candidate i). Guarantee it a
        // slot inside the cap and try it first.
        let mut tuples = bounded_tuples(&per_binder, limit);
        if per_binder.len() > 1 && limit > 0 {
            let hint_tuple: Vec<TermId> = per_binder
                .iter()
                .enumerate()
                .map(|(index, column)| column.get(index).copied().unwrap_or(column[0]))
                .collect();
            if let Some(position) = tuples.iter().position(|t| t == &hint_tuple) {
                tuples.remove(position);
            } else if tuples.len() >= limit {
                tuples.pop();
            }
            tuples.insert(0, hint_tuple);
        }
        Some(tuples)
    }

    /// Collect authored clause-shaped roots carrying exactly one negated
    /// existential among quantifier-free literals: `Not(And(…, E, …))`
    /// (literals are the negated conjuncts) or the elaborator's desugaring
    /// of it, `(or … (not E) …)` (literals verbatim).
    ///
    /// Ground-instantiation lane only: the direct candidate lane
    /// (`authored_negated_exists`) assumes a bare `(not E)` unit and must
    /// never see these roots.
    pub(super) fn exact_authored_negated_and_exists_roots(
        &self,
        authored: &[TermId],
    ) -> Vec<PsiNegatedExists> {
        let mut out = Vec::new();
        for &root in authored {
            let (args, negate_args) = match self.ctx.terms.get(root).clone() {
                TermData::Not(inner) => match self.ctx.terms.get(inner).clone() {
                    TermData::App(Symbol::Named(name), args) if name == "and" => (args, true),
                    _ => continue,
                },
                TermData::App(Symbol::Named(name), args) if name == "or" => (args, false),
                _ => continue,
            };
            if args.len() < 2 {
                continue;
            }
            let mut found: Option<PsiNegatedExists> = None;
            let mut valid = true;
            for (index, &arg) in args.iter().enumerate() {
                // The existential itself: a bare conjunct under `not_and`,
                // or the `(not E)` literal under `or`.
                let exists = if negate_args {
                    Some(arg)
                } else if let TermData::Not(inner) = self.ctx.terms.get(arg) {
                    Some(*inner)
                } else {
                    None
                };
                let exists_body =
                    exists.and_then(|candidate| match self.ctx.terms.get(candidate) {
                        TermData::Exists(bindings, body, _) => {
                            Some((candidate, bindings.clone(), *body))
                        }
                        _ => None,
                    });
                match exists_body {
                    Some((exists, bindings, body)) => {
                        if found.is_some()
                            || bindings.is_empty()
                            || matches!(
                                self.ctx.terms.get(body),
                                TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..)
                            )
                        {
                            valid = false;
                            break;
                        }
                        found = Some(PsiNegatedExists {
                            root,
                            exists,
                            exists_index: index,
                            bindings,
                            body,
                            args: args.clone(),
                            negate_args,
                        });
                    }
                    None if crate::ematching::contains_quantifier(&self.ctx.terms, arg) => {
                        valid = false;
                        break;
                    }
                    None => {}
                }
            }
            if valid {
                out.extend(found);
            }
        }
        out
    }
}
