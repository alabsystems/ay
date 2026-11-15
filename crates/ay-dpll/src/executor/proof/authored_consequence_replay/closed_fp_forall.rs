// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Direct checked completion for closed instances of authored arithmetic foralls.
//!
//! Zero is a source-side instantiation hint, not a value from the relaxed FP
//! model. A failed hint performs no ground probe and grants no SAT authority.

use super::*;

fn debit(remaining: &mut usize, amount: usize) -> Option<()> {
    *remaining = remaining.checked_sub(amount)?;
    Some(())
}

fn flat_sort(sort: &Sort) -> bool {
    matches!(
        sort,
        Sort::Bool | Sort::Int | Sort::Real | Sort::BitVec(_) | Sort::FloatingPoint(..)
    ) || matches!(sort, Sort::Uninterpreted(name) if name == "RoundingMode")
}

impl Executor {
    pub(in crate::executor) fn try_translate_closed_fp_forall_zero_unsat(&mut self) -> bool {
        if !crate::quant_unit_authority::consequence_replay_enabled()
            || !self.produce_proofs_enabled()
            || self.should_abort_theory_loop()
            || self
                .consequence_replay_direct_state
                .get()
                .is_some_and(|(_, attempts)| attempts >= MAX_DIRECT_REPLAY_ATTEMPTS)
        {
            return false;
        }
        // This existing getter checks the inventory bound before currentness.
        // No mutable solver assertion, unbound assumption, or stale epoch is a
        // source. Require the same frozen provenance the installer will read.
        let Some((epoch, stamp, roots)) = self.bounded_plain_unsat_query_scope(MAX_AUTHORED_ROOTS)
        else {
            return false;
        };
        if self
            .last_assumptions
            .as_ref()
            .is_some_and(|terms| !terms.is_empty())
            || self
                .proof_problem_assertion_provenance
                .as_ref()
                .is_none_or(|provenance| provenance.original_problem_assertions.as_slice() != roots)
        {
            return false;
        }
        let authored = roots.to_vec();
        let candidate = self.build_closed_fp_zero_candidate(&authored);
        let Some((current_epoch, current_stamp, _)) =
            self.bounded_plain_unsat_query_scope(MAX_AUTHORED_ROOTS)
        else {
            return false;
        };
        if !epoch.is_same_epoch(&current_epoch)
            || stamp != current_stamp
            || self.should_abort_theory_loop()
        {
            return false;
        }
        self.install_consequence_replay_candidate(candidate)
    }

    fn build_closed_fp_zero_candidate(&mut self, authored: &[TermId]) -> Option<Proof> {
        // Reuse the consequence lane's source-walk allowance, cumulatively
        // across the AND spine, binders, triggers, and expanded body visits.
        let mut remaining = MAX_AND_PATH_WORK;
        let sources = self.closed_fp_zero_sources(authored, &mut remaining)?;
        let mut plans = ay_core::kani_compat::DetHashMap::default();
        let mut instances = Vec::new();
        for quantifier in sources {
            if self.should_abort_theory_loop() {
                return None;
            }
            // All borrowed source metadata was bounded before this clone.
            let TermData::Forall(vars, body, _) = self.ctx.terms.get(quantifier) else {
                return None;
            };
            let body = *body;
            let vars = vars.clone();
            let mut binding = Vec::with_capacity(vars.len());
            let mut substitution = ay_core::kani_compat::DetHashMap::default();
            for (name, sort) in vars {
                binding.push(match sort {
                    Sort::Int => self.ctx.terms.mk_int(BigInt::from(0)),
                    Sort::Real => self
                        .ctx
                        .terms
                        .mk_rational(num_rational::BigRational::from_integer(BigInt::from(0))),
                    _ => return None,
                });
                substitution.insert(name, *binding.last()?);
            }
            let instance =
                crate::ematching::subst_vars_exact_qf(&mut self.ctx.terms, body, &substitution)?;
            if plans.contains_key(&instance) {
                continue;
            }
            plans.insert(
                instance,
                ConsequencePlan::ForallInstance {
                    quantifier,
                    binding,
                },
            );
            instances.push(instance);
        }
        if instances.is_empty() || !self.claim_direct_consequence_attempt(&plans, &instances) {
            return None;
        }
        let mut checks = 0;
        for instance in instances {
            if self.should_abort_theory_loop() {
                return None;
            }
            // Deliberately do not call the generic consequence-replay builder:
            // its fallback performs a solver probe. This path is proof-only.
            if let Some(candidate) = self.build_fp_instance_refutation(authored, &plans, instance) {
                checks += 1;
                if self.ground_pin_candidate_is_strict(&candidate, authored) {
                    return Some(candidate);
                }
                if checks >= ground_pin::MAX_CANDIDATE_CHECKS {
                    return None;
                }
            }
        }
        None
    }

    fn closed_fp_zero_sources(
        &self,
        authored: &[TermId],
        remaining: &mut usize,
    ) -> Option<Vec<TermId>> {
        let should_stop = self.make_should_stop();
        debit(remaining, authored.len())?;
        let mut stack: Vec<_> = authored.iter().rev().map(|&term| (term, 0)).collect();
        let mut sources = Vec::new();
        while let Some((term, depth)) = stack.pop() {
            debit(remaining, 1)?;
            if should_stop()
                || depth > ground_pin::MAX_INSTANCE_DEPTH
                || term.0 as usize >= self.ctx.terms.len()
            {
                return None;
            }
            if self.ctx.terms.sort(term) != &Sort::Bool {
                return None;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) if name == "and" => {
                    debit(remaining, args.len())?;
                    stack.extend(args.iter().rev().map(|&arg| (arg, depth + 1)));
                }
                TermData::Forall(vars, body, triggers) if !self.ctx.terms.is_no_mbqi(term) => {
                    if vars.is_empty() || vars.len() > MAX_INSTANCES {
                        continue;
                    }
                    debit(remaining, vars.len())?;
                    if vars
                        .iter()
                        .any(|(_, sort)| !matches!(sort, Sort::Int | Sort::Real))
                    {
                        continue;
                    }
                    let mut names = ay_core::kani_compat::DetHashSet::default();
                    for (name, _) in vars {
                        debit(remaining, name.len())?;
                        if !names.insert(name.as_str()) {
                            return None;
                        }
                    }
                    let Some(has_fp) = self.closed_fp_zero_body(*body, vars, remaining)? else {
                        continue;
                    };
                    debit(remaining, triggers.len())?;
                    for group in triggers {
                        debit(remaining, group.len())?;
                        for &trigger in group {
                            self.closed_fp_zero_body(trigger, vars, remaining)??;
                        }
                    }
                    if has_fp {
                        if sources.len() >= MAX_INSTANCES {
                            return None;
                        }
                        sources.push(term);
                    }
                }
                _ => {}
            }
        }
        Some(sources)
    }

    /// `None` is a stopped/exhausted batch; `Some(None)` is unsupported syntax.
    /// Count expanded occurrences, not just distinct DAG nodes: substitution
    /// may revisit shared children. Only flat borrowed sorts reach its clones.
    fn closed_fp_zero_body(
        &self,
        root: TermId,
        vars: &[(String, Sort)],
        remaining: &mut usize,
    ) -> Option<Option<bool>> {
        let should_stop = self.make_should_stop();
        debit(remaining, 1)?;
        let mut stack = vec![(root, 0)];
        let mut has_fp = false;
        while let Some((term, depth)) = stack.pop() {
            debit(remaining, 1)?;
            if should_stop()
                || depth > ground_pin::MAX_INSTANCE_DEPTH
                || term.0 as usize >= self.ctx.terms.len()
            {
                return None;
            }
            let sort = self.ctx.terms.sort(term);
            if !flat_sort(sort) {
                return Some(None);
            }
            has_fp |= matches!(sort, Sort::FloatingPoint(..));
            match self.ctx.terms.get(term) {
                TermData::Const(Constant::Bool(_)) => {}
                TermData::Const(Constant::Int(value) | Constant::BitVec { value, .. }) => {
                    debit(remaining, usize::try_from(value.bits().div_ceil(8)).ok()?)?;
                }
                TermData::Const(Constant::Rational(value)) => {
                    for part in [value.0.numer(), value.0.denom()] {
                        debit(remaining, usize::try_from(part.bits().div_ceil(8)).ok()?)?;
                    }
                }
                TermData::Var(name, _) => {
                    debit(
                        remaining,
                        name.len().checked_add(1)?.checked_mul(vars.len())?,
                    )?;
                    if !vars
                        .iter()
                        .any(|(bound, bound_sort)| bound == name && bound_sort == sort)
                    {
                        return Some(None);
                    }
                }
                TermData::App(symbol, args) => {
                    debit(remaining, symbol.name().len())?;
                    if let Symbol::Indexed(_, indices) = symbol {
                        debit(remaining, indices.len())?;
                    }
                    debit(remaining, args.len())?;
                    stack.extend(args.iter().rev().map(|&arg| (arg, depth + 1)));
                }
                TermData::Not(inner) => {
                    debit(remaining, 1)?;
                    stack.push((*inner, depth + 1));
                }
                TermData::Ite(condition, then_term, else_term) => {
                    debit(remaining, 3)?;
                    stack.extend([*condition, *then_term, *else_term].map(|arg| (arg, depth + 1)));
                }
                _ => return Some(None),
            }
        }
        Some(Some(has_fp))
    }
}

#[cfg(test)]
mod tests;
