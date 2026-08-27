// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Surgery-wide work accounting for proof-repair recognition.
//!
//! Planning runs before the retained-surface audit, so its own parsing,
//! substitution, and certificate reconstruction must be aggregate-bounded.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Constant, TermData};
use ay_core::{Symbol, TermId, TermStore};
use ay_frontend::command::Term as FrontendTerm;
use std::mem::size_of;

use super::surface_source_work;

const MAX_PLANNING_WORK: usize = 32 * 1024 * 1024;
const MAX_CACHED_TERMS: usize = 8_192;
pub(in crate::executor) const MAX_FARKAS_ATTEMPTS: usize = 128;

pub(in crate::executor) fn surgery_sources_are_bounded(
    terms: &TermStore,
    originals: &[(TermId, FrontendTerm)],
) -> bool {
    crate::executor::proof_trust_surgery_surface_audit::surface_sources_have_bounded_work(
        originals.iter().map(|(_, parsed)| parsed),
    ) && crate::executor::proof_surface_syntax::surface_override_roots_have_bounded_work(
        terms,
        originals.iter().map(|(canonical, _)| *canonical),
    )
}

/// What pricing one canonical operand cost, for a scan that may skip a source.
///
/// Distinguishing the middle arm from the last one is the whole point: only
/// [`Self::Exhausted`] means the aggregate planning budget is spent and every
/// scan must stop.
pub(in crate::executor) enum OperandCharge {
    /// Priced and charged. The caller may traverse the operand.
    Charged,
    /// `canonical_term_work` declines to price this operand — it is a binder,
    /// too deep, or carries an unsupported symbol — so nothing about it may be
    /// traversed, substituted into, or printed. The probe's own walk was still
    /// charged. A caller whose recognizer cannot use such a term anyway (the
    /// ground ITE-lift scan: `term_ite_candidates_with_cond` never descends
    /// into a binder) may skip this source and keep scanning.
    Unpriceable,
    /// The aggregate planning budget is gone.
    Exhausted,
}

/// One authority shared by every trust leaf in a surgery attempt.
pub(in crate::executor) struct SurgeryPlanningBudget {
    remaining_work: usize,
    remaining_farkas_attempts: usize,
    canonical_work: HashMap<TermId, usize>,
    source_work: HashMap<TermId, (usize, usize)>,
    retained_row_signability: HashMap<TermId, (usize, bool)>,
}

impl SurgeryPlanningBudget {
    pub(in crate::executor) fn new() -> Self {
        Self {
            remaining_work: MAX_PLANNING_WORK,
            remaining_farkas_attempts: MAX_FARKAS_ATTEMPTS,
            canonical_work: HashMap::default(),
            source_work: HashMap::default(),
            retained_row_signability: HashMap::default(),
        }
    }

    pub(in crate::executor) fn spend_work(&mut self, work: usize) -> bool {
        let Some(remaining) = self.remaining_work.checked_sub(work.max(1)) else {
            return false;
        };
        self.remaining_work = remaining;
        true
    }

    /// Charge one use of an authored surface. The cost is cached, but every
    /// operation is charged because current collectors and matchers rerun.
    /// A canonical id may use only one borrowed authored source in a surgery;
    /// a second address is ambiguous authority and fails closed.
    pub(in crate::executor) fn spend_surface(
        &mut self,
        canonical: TermId,
        parsed: &FrontendTerm,
    ) -> bool {
        let source_address = std::ptr::from_ref(parsed) as usize;
        let work = match self.source_work.get(&canonical) {
            Some(&(address, work)) if address == source_address => work,
            Some(_) => return false,
            None => {
                if self.source_work.len() >= MAX_CACHED_TERMS {
                    return false;
                }
                let Some(work) = surface_source_work(parsed) else {
                    return false;
                };
                self.source_work.insert(canonical, (source_address, work));
                work
            }
        };
        self.spend_work(work)
    }

    /// Classify one exact authored arithmetic row once. Repeated Farkas
    /// candidates reuse the result only for the same canonical id and the
    /// same borrowed source address; ambiguous spellings fail closed.
    pub(in crate::executor) fn retained_row_is_signable(
        &mut self,
        ctx: &mut ay_frontend::Context,
        canonical: TermId,
        parsed: &FrontendTerm,
    ) -> Option<bool> {
        let address = std::ptr::from_ref(parsed) as usize;
        if let Some(&(cached_address, signable)) = self.retained_row_signability.get(&canonical) {
            return (cached_address == address).then_some(signable);
        }
        if self.retained_row_signability.len() >= MAX_CACHED_TERMS
            || !self.spend_surface(canonical, parsed)
        {
            return None;
        }
        let signable = super::surface_is_direct_arithmetic_literal(ctx, parsed);
        self.retained_row_signability
            .insert(canonical, (address, signable));
        Some(signable)
    }

    /// Charge one full traversal of every canonical operand. Cached costs
    /// avoid repeating the preflight, not the downstream solver's work.
    pub(in crate::executor) fn spend_terms(
        &mut self,
        terms: &TermStore,
        operands: &[TermId],
    ) -> bool {
        let mut total = 0usize;
        for &operand in operands {
            let work = match self.canonical_work.get(&operand) {
                Some(&work) => work,
                None => {
                    if self.canonical_work.len() >= MAX_CACHED_TERMS {
                        return false;
                    }
                    let Some(work) = canonical_term_work(terms, operand) else {
                        return false;
                    };
                    self.canonical_work.insert(operand, work);
                    work
                }
            };
            let Some(next) = total.checked_add(work.max(1)) else {
                return false;
            };
            total = next;
        }
        self.spend_work(total)
    }

    /// Price ONE canonical operand for a scan that is allowed to SKIP a source
    /// it cannot use, instead of abandoning the whole search.
    ///
    /// [`Self::spend_terms`] collapses two very different answers into one
    /// `false`: "the aggregate budget is gone" and "`canonical_term_work`
    /// declines to price this term at all" (it refuses every `forall`/`exists`/
    /// `let` outright). A scan over the AUTHORED ASSERTION LIST hits the second
    /// answer on the first quantified assertion in the file and, reading it as
    /// exhaustion, stops — so on a problem with a `forall` anywhere near the
    /// front, every ground source after it becomes invisible to the repair.
    /// Measured on the `inc_some_list` dual-vocabulary obligation
    /// (#dt-uf-bridge-congruence): `originals[4]` of 111 is a `forall`, and the
    /// Shannon-lift leaf's own source (`dn13`, `originals[14]`) was never
    /// examined, so the ITE-lift lane declined a leaf it can actually prove.
    ///
    /// Both outcomes are charged: [`OperandCharge::Unpriceable`] costs the
    /// probe's own traversal, so a refusal buys no free work.
    pub(in crate::executor) fn charge_operand(
        &mut self,
        terms: &TermStore,
        operand: TermId,
    ) -> OperandCharge {
        if let Some(&work) = self.canonical_work.get(&operand) {
            return if self.spend_work(work) {
                OperandCharge::Charged
            } else {
                OperandCharge::Exhausted
            };
        }
        if self.canonical_work.len() >= MAX_CACHED_TERMS {
            return OperandCharge::Exhausted;
        }
        let (work, probe) = canonical_term_work_probe(terms, operand);
        let Some(work) = work else {
            // Charge the refused walk on the SAME scale the success path uses.
            let probe_work = probe.saturating_mul(size_of::<TermData>());
            return if self.spend_work(probe_work) {
                OperandCharge::Unpriceable
            } else {
                OperandCharge::Exhausted
            };
        };
        self.canonical_work.insert(operand, work);
        if self.spend_work(work) {
            OperandCharge::Charged
        } else {
            OperandCharge::Exhausted
        }
    }

    /// Charge a solver-backed provenance reconstruction and all of its rows.
    pub(in crate::executor) fn spend_farkas_attempt(
        &mut self,
        terms: &TermStore,
        operands: &[TermId],
    ) -> bool {
        let Some(remaining) = self.remaining_farkas_attempts.checked_sub(1) else {
            return false;
        };
        if !self.spend_terms(terms, operands) {
            return false;
        }
        self.remaining_farkas_attempts = remaining;
        true
    }

    #[cfg(test)]
    pub(in crate::executor) fn set_remaining_work_for_test(&mut self, work: usize) {
        self.remaining_work = work;
    }
}

/// Bound canonical traversal before substitution, formatting, or solver work.
/// Shared DAGs are charged per occurrence to match recursive consumers.
pub(in crate::executor) fn canonical_term_work(terms: &TermStore, root: TermId) -> Option<usize> {
    canonical_term_work_probe(terms, root).0
}

/// [`canonical_term_work`] plus the traversal the PROBE ITSELF performed.
///
/// A refusal — a binder, an over-deep DAG, an unsupported symbol — still costs
/// real walking, and a caller that reads the refusal as "skip this source"
/// instead of "stop everything" has to pay for it: otherwise a file of
/// `forall`s buys unbounded planning work one free probe at a time. The visit
/// count is the same quantity the success path already folds into its cost
/// (`visits * size_of::<TermData>()`), so both outcomes bill on one scale.
fn canonical_term_work_probe(terms: &TermStore, root: TermId) -> (Option<usize>, usize) {
    const MAX_VISITS: usize = 100_000;
    const MAX_DEPTH: usize = 256;
    const MAX_BYTES: usize = 8 * 1024 * 1024;

    fn bigint_bytes(value: &num_bigint::BigInt) -> Option<usize> {
        let bits = usize::try_from(value.bits()).ok()?;
        let binary = bits.checked_add(7)? / 8;
        // `value_to_surface` and Alethe formatting allocate decimal text.
        // ceil(bits * log10(2)) plus sign/small-value headroom.
        let decimal = bits
            .checked_mul(30_103)?
            .checked_add(99_999)?
            .checked_div(100_000)?
            .checked_add(2)?;
        Some(binary.max(decimal))
    }

    fn symbol_work(symbol: &Symbol, max_indices: usize) -> Option<usize> {
        match symbol {
            Symbol::Named(name) => Some(name.len()),
            Symbol::Indexed(name, indices) => {
                if indices.len() > max_indices {
                    return None;
                }
                name.len()
                    .checked_add(indices.len().checked_mul(size_of::<u32>())?)
            }
            _ => None,
        }
    }

    let mut pending = vec![(root, 0usize)];
    let mut visits = 0usize;
    // The walk is wrapped so its `?` exits land HERE and `visits` survives them:
    // a refusal has to report the work it already did, not zero.
    let work = (|| {
        let mut bytes = 0usize;
        while let Some((term, depth)) = pending.pop() {
            visits = visits.checked_add(1)?;
            if visits > MAX_VISITS || depth > MAX_DEPTH {
                return None;
            }
            let local = match terms.get(term) {
                TermData::Const(Constant::Bool(_)) => 1,
                TermData::Const(Constant::Int(value)) => bigint_bytes(value)?,
                TermData::Const(Constant::Rational(value)) => {
                    bigint_bytes(value.0.numer())?.checked_add(bigint_bytes(value.0.denom())?)?
                }
                TermData::Const(Constant::BitVec { value, width }) => bigint_bytes(value)?
                    .max(usize::try_from(*width).ok()?)
                    .saturating_add(2),
                TermData::Const(Constant::String(value)) => value.len(),
                TermData::Var(name, _) => name.len(),
                TermData::App(symbol, args) => {
                    if pending
                        .len()
                        .saturating_add(visits)
                        .saturating_add(args.len())
                        > MAX_VISITS
                    {
                        return None;
                    }
                    pending.extend(args.iter().map(|&arg| (arg, depth + 1)));
                    symbol_work(symbol, MAX_VISITS.saturating_sub(visits))?
                        .saturating_add(args.len().saturating_mul(4))
                }
                TermData::Not(inner) => {
                    pending.push((*inner, depth + 1));
                    1
                }
                TermData::Ite(cond, then_term, else_term) => {
                    pending.extend([
                        (*cond, depth + 1),
                        (*then_term, depth + 1),
                        (*else_term, depth + 1),
                    ]);
                    3
                }
                TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => return None,
                _ => return None,
            };
            bytes = bytes.checked_add(local)?;
            if bytes > MAX_BYTES {
                return None;
            }
        }
        bytes
            .checked_add(visits.saturating_mul(size_of::<TermData>()))
            .filter(|&work| work <= MAX_BYTES)
    })();
    (work, visits)
}

#[cfg(test)]
mod tests {
    use ay_core::{Sort, TermStore};
    use ay_frontend::command::Term as FrontendTerm;

    use super::{surface_source_work, SurgeryPlanningBudget};

    #[test]
    fn farkas_attempts_share_one_global_boundary() {
        let mut terms = TermStore::new();
        let atom = terms.mk_var("planning_budget_atom", Sort::Bool);
        let mut budget = SurgeryPlanningBudget::new();
        for _ in 0..super::MAX_FARKAS_ATTEMPTS {
            assert!(budget.spend_farkas_attempt(&terms, &[atom]));
        }
        assert!(!budget.spend_farkas_attempt(&terms, &[atom]));
    }

    /// The tri-state charge must separate "cannot price this" from "budget
    /// gone" — the conflation that made one authored `forall` abort the whole
    /// ground ITE-lift scan (#shannon-lift-checkable).
    #[test]
    fn charging_a_binder_operand_is_unpriceable_not_exhaustion() {
        let mut terms = TermStore::new();
        let body = terms.mk_var("charge_binder_body", Sort::Bool);
        let binder = terms.mk_forall(vec![("charge_z".to_string(), Sort::Int)], body);
        assert!(
            super::canonical_term_work(&terms, binder).is_none(),
            "the cost model refuses to price a binder",
        );
        let mut budget = SurgeryPlanningBudget::new();
        assert!(matches!(
            budget.charge_operand(&terms, binder),
            super::OperandCharge::Unpriceable
        ));
        // The scan may go on to price and use an ordinary ground operand.
        assert!(matches!(
            budget.charge_operand(&terms, body),
            super::OperandCharge::Charged
        ));
    }

    /// A refusal is still billed, so a file of binders cannot buy unbounded
    /// planning work one free probe at a time.
    #[test]
    fn an_unpriceable_operand_still_spends_the_aggregate_budget() {
        let mut terms = TermStore::new();
        let body = terms.mk_var("charge_drain_body", Sort::Bool);
        let binder = terms.mk_forall(vec![("charge_drain_z".to_string(), Sort::Int)], body);
        let mut budget = SurgeryPlanningBudget::new();
        budget.set_remaining_work_for_test(1);
        assert!(matches!(
            budget.charge_operand(&terms, binder),
            super::OperandCharge::Exhausted
        ));
    }

    #[test]
    fn one_canonical_source_cannot_reuse_another_surface_address() {
        let mut budget = SurgeryPlanningBudget::new();
        let first = FrontendTerm::Symbol("first_source".to_string());
        let second = FrontendTerm::Symbol("second_source".to_string());
        assert!(budget.spend_surface(ay_core::TermId(7), &first));
        assert!(!budget.spend_surface(ay_core::TermId(7), &second));
    }

    #[test]
    fn repeated_whole_surface_operations_spend_the_aggregate_budget() {
        let fragment = FrontendTerm::App(
            "+".to_string(),
            (0..4_096)
                .map(|index| FrontendTerm::Symbol(format!("fragment_{index}")))
                .collect(),
        );
        let work = surface_source_work(&fragment).expect("bounded fragment has a cost");
        let mut budget = SurgeryPlanningBudget::new();
        budget.set_remaining_work_for_test(work * 2 - 1);
        assert!(budget.spend_surface(ay_core::TermId(8), &fragment));
        assert!(!budget.spend_surface(ay_core::TermId(8), &fragment));
    }

    #[test]
    fn whole_source_estimate_dominates_all_immediate_fragment_estimates() {
        let rows: Vec<FrontendTerm> = (0..64)
            .map(|index| {
                FrontendTerm::App(
                    "=".to_string(),
                    vec![
                        FrontendTerm::Symbol(format!("surface_row_{index}")),
                        FrontendTerm::Const(ay_frontend::command::Constant::Numeral(
                            index.to_string(),
                        )),
                    ],
                )
            })
            .collect();
        let fragment_work = rows.iter().try_fold(0usize, |used, row| {
            used.checked_add(surface_source_work(row)?)
        });
        let whole = FrontendTerm::App("and".to_string(), rows);
        assert!(
            surface_source_work(&whole).expect("whole source is bounded")
                >= fragment_work.expect("all fragments are bounded"),
            "one complete-source charge must dominate a pass over every child",
        );
    }
}
