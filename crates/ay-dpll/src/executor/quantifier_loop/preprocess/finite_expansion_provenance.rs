// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact authored-root lineage for finite quantifier expansion.
//!
//! Proof export records only top-level universal instances. SAT publication
//! instead needs the exact semantic replacement of any supported authored
//! root, including the common `not (exists ...)` shell. Keep that additional
//! lineage separate from proof payload so neither role can impersonate the
//! other.
//!
//! The proof payload itself is derived here too
//! ([`Executor::derive_finite_expansion`]): each recorded universal instance
//! gets a strict `forall_inst` derivation from its authored root when the
//! expansion is made, the way E-matching instances do.

use ay_core::{Sort, TermData, TermId, TermStore};
use ay_frontend::command::Term as FrontendTerm;
use ay_frontend::Context;

use super::super::FiniteExpansionRecord;
use crate::ematching::contains_quantifier;
use crate::executor::proof::native_universal_lineage::NativeUniversalSource;
use crate::executor::{Executor, QuantExpansionRecord};
use crate::proof_tracker::guarded_instance::GuardedInstance;

/// Instances beyond which a finite expansion is not derived. Each derived
/// instance adds about a dozen tracker steps that every proof-mode pass walks
/// before pruning keeps the refutation's cone; 512 covers a full 8-bit domain
/// and the Bool/UF combination cap, not the 4096-cell guarded integer boxes.
const MAX_DERIVED_EXPANSION_INSTANCES: usize = 512;

/// Instances a whole solve's finite expansions may record before the next one
/// is no longer derived: every instance recorded so far in this check-sat,
/// derived or not, counts against it.
///
/// Every derived instance stays in the unpruned tracker proof whether or not
/// the refutation uses it, and export spells each of its `forall_inst` steps
/// through one entry of the printer's authored-surface override table
/// (`add_forall_instance_surface_overrides`), which refuses more than 8192
/// entries. Without this cap 32 universals of 254 instances each, next to a
/// ground conflict that needs none of them, turned a carcara-`valid` `unsat`
/// into `unknown` ("the provisional UNSAT verdict has no proof"; measured on
/// 938ec0327, 30 universals still passed). 1024 keeps the lane at an eighth of
/// that table, leaving the rest to E-matching instances and authored roots.
///
/// It also bounds what a solve that never uses the instances pays: the
/// derivation runs on EVERY tracker-armed public solve, not only under
/// `:produce-proofs` (the tracker backs a default-mode `unsat` too; only
/// competition shedding disarms it). In the CLI's default mode (a budgeted
/// best-effort certificate) it moved 33 of 119 probes from `discharged-trust`
/// to `strict-proof` with every verdict unchanged, and made six slower by 0.6
/// to 1.4 s (opt-level 1), their best-effort reconstruction now running to its
/// step budget (measured on 938ec0327).
const MAX_DERIVED_SOLVE_INSTANCES: usize = 1024;

impl Executor {
    /// Record that the authored top-level universal `original` at stack
    /// position `assertion_index` was replaced in place by its exact
    /// finite-domain expansion `expanded`, and derive that replacement for
    /// proof export ([`Self::derive_finite_expansion`]).
    pub(super) fn record_finite_expansion(
        &mut self,
        original: TermId,
        assertion_index: usize,
        expanded: TermId,
        instances: Vec<(Vec<TermId>, TermId)>,
    ) {
        self.derive_finite_expansion(original, assertion_index, expanded, &instances);
        self.quant_expansion_records.push(QuantExpansionRecord {
            original,
            assertion_index,
            expanded,
            instances,
        });
    }

    /// Derive the finite-domain replacement `expanded` from the original
    /// authored universal at this stack position, instead of
    /// leaving it to be assumed (#fde-forall-provenance).
    ///
    /// Proof authority was frozen before this expansion, and the replacement
    /// must be DERIVED rather than whitelisted as an authored `assume`. Every
    /// folded instance with a checked plan gets the tracker's guarded-instance
    /// derivation (`forall_inst` at the recorded values, closed guards
    /// discharged by `evaluate`); when all of them do, so does the conjunction
    /// the ground solver consumes. Both are indexed as derived units, so the
    /// solve's `add_assumption` reuses them exactly as it reuses an E-matching
    /// instance's `forall_inst` derivation.
    ///
    /// Declines, deriving nothing, when:
    /// * there is no aligned authored universal. After preprocessing changes
    ///   the quantified term, every instance still has to derive from the
    ///   actual authored universal at that position;
    /// * the expansion has more than [`MAX_DERIVED_EXPANSION_INSTANCES`]
    ///   instances, or would take the solve's recorded instances past
    ///   [`MAX_DERIVED_SOLVE_INSTANCES`];
    /// * the authored spelling of `original` is not plain
    ///   ([`surface_is_plain`]). A guard spelled through a `define-fun` is
    ///   checked internally on its unfolded body, and pinned carcara (run
    ///   without `--apply-function-defs`) cannot re-derive the `evaluate` that
    ///   discharges it: a fail-closed `unknown` would become an `unsat` whose
    ///   export is refused (`evaluate conclusion changed under surface
    ///   rewriting`) or holey. The authored replacement cascade declines such
    ///   candidates for the same reason
    ///   (`authored_equality_closure/ground_instances.rs`);
    /// * an authored occurrence of `original` is not spelled as the `forall`
    ///   itself, or two occurrences are spelled differently
    ///   ([`Self::authored_surface_is_plain`]). A Boolean wrapper elaboration
    ///   folds away (`(=> true Q)`, `(not (not Q))`) published a `hole` at
    ///   the `forall_inst` bridge, and two alpha-renamed spellings of one
    ///   universal (one internal root, two surfaces) published `unsat` with
    ///   its export refused (`proof was not generated`).
    ///
    /// A plain root whose authored BODY is not the internal `or` up to the
    /// reshaping the printer bridges (a ternary `distinct` guard, a guard
    /// `(not (bvuge i c))`, an `ite` or `xor` body, a nested `=>`, an `and`
    /// conclusion) still publishes `unsat` with one `hole`: the strict checker
    /// admitted the derivation, but the printer has no external spelling for
    /// the authored-to-internal bridge. It fails closed under
    /// `--strict-proofs`, as the authored cascade documents for the same
    /// shapes. Measured on 938ec0327 over 34 probes this lane moved from
    /// `unknown` to `unsat`: 26 carcara `valid`, 8 `holey`, none refused or
    /// `invalid` (`finite_expansion_provenance.rs` in `group_proofs` pins one).
    ///
    /// An instance or conjunction without a derivation stays underived, which
    /// is all it was before; the replacement itself is unchanged either way.
    fn derive_finite_expansion(
        &mut self,
        original: TermId,
        assertion_index: usize,
        expanded: TermId,
        instances: &[(Vec<TermId>, TermId)],
    ) {
        if !self.produce_proofs_enabled()
            || instances.is_empty()
            || instances.len() > MAX_DERIVED_EXPANSION_INSTANCES
        {
            return;
        }
        let recorded: usize = self
            .quant_expansion_records
            .iter()
            .map(|record| record.instances.len())
            .sum();
        if recorded.saturating_add(instances.len()) > MAX_DERIVED_SOLVE_INSTANCES {
            return;
        }
        // Native insertions have no authored SMT Forall surface. Admit them
        // only from the frozen full query plus positive insertion custody;
        // the parsed/Text path below retains its existing D7 surface rules.
        if let Some(source) = NativeUniversalSource::capture(self) {
            if source.admits(self, original) {
                for (values, target) in instances {
                    let _ = self.derive_native_universal_target(&source, original, values, *target);
                }
                if source.is_current(self)
                    && self.admit_native_universal_terms(&[expanded]).is_some()
                {
                    let _ = self
                        .proof_tracker
                        .add_conjunction_of_derived_units(&mut self.ctx.terms, expanded);
                }
                return;
            }
        }
        let Some(provenance) = self.proof_problem_assertion_provenance.as_ref() else {
            return;
        };
        let Some(&authored) = provenance.original_problem_assertions.get(assertion_index) else {
            return;
        };
        if !self.authored_surface_is_plain(authored) {
            return;
        }
        let plans: Vec<GuardedInstance> = instances
            .iter()
            .filter_map(|(values, instance)| {
                GuardedInstance::plan(&mut self.ctx.terms, authored, values, *instance)
            })
            .collect();
        for plan in &plans {
            let _ = self
                .proof_tracker
                .add_forall_guarded_instance_assertion(&mut self.ctx.terms, plan);
        }
        let _ = self
            .proof_tracker
            .add_conjunction_of_derived_units(&mut self.ctx.terms, expanded);
    }

    /// Whether every authored occurrence of `original` is spelled plainly,
    /// as the `forall` itself, and identically to every other occurrence.
    /// The parsed stack is index-aligned with the authored roots; a
    /// misalignment or a missing occurrence declines.
    fn authored_surface_is_plain(&self, original: TermId) -> bool {
        let roots = self.proof_original_problem_assertions_slice();
        let parsed = self.ctx.assertions_parsed();
        if roots.len() != parsed.len() {
            return false;
        }
        let mut budget = MAX_SURFACE_SCREEN_NODES;
        let mut first: Option<&FrontendTerm> = None;
        for (&root, surface) in roots.iter().zip(parsed) {
            if root != original {
                continue;
            }
            if !spelled_as_forall(surface)
                || first.is_some_and(|first| first != surface)
                || !surface_is_plain(&self.ctx, surface, &mut budget)
            {
                return false;
            }
            first = Some(surface);
        }
        first.is_some()
    }
}

/// Whether an authored root is spelled as the universal itself (annotations
/// aside), not under a Boolean wrapper elaboration folds away.
fn spelled_as_forall(term: &FrontendTerm) -> bool {
    match term {
        FrontendTerm::Forall(..) => true,
        FrontendTerm::Annotated(inner, _) => spelled_as_forall(inner),
        _ => false,
    }
}

/// Parsed nodes [`surface_is_plain`] visits per root before it declines.
const MAX_SURFACE_SCREEN_NODES: usize = 4096;

/// Whether an authored surface is free of the spellings the printer cannot
/// restore around a derivation of the internal term at all: no problem-level
/// `define-fun` (applications are macro-expanded at elaboration), and no
/// `let`, `lambda`, `match` or qualified application. Annotations are
/// transparent. Over budget is not plain. Plain is necessary, not sufficient:
/// a body elaboration reshapes still prints a `hole` (see
/// [`Executor::derive_finite_expansion`]).
fn surface_is_plain(context: &Context, term: &FrontendTerm, budget: &mut usize) -> bool {
    let Some(remaining) = budget.checked_sub(1) else {
        return false;
    };
    *budget = remaining;
    match term {
        FrontendTerm::Const(_) => true,
        FrontendTerm::Symbol(name) => !context.is_defined_fun(name),
        FrontendTerm::App(head, args) | FrontendTerm::IndexedApp(head, _, args) => {
            !context.is_defined_fun(head)
                && args
                    .iter()
                    .all(|arg| surface_is_plain(context, arg, budget))
        }
        FrontendTerm::Forall(_, body) | FrontendTerm::Exists(_, body) => {
            surface_is_plain(context, body, budget)
        }
        FrontendTerm::Annotated(inner, _) => surface_is_plain(context, inner, budget),
        _ => false,
    }
}

pub(super) fn exact_record(
    terms: &mut TermStore,
    original: TermId,
    assertion_index: usize,
    expanded: TermId,
    direct_expansion: Option<TermId>,
) -> Option<FiniteExpansionRecord> {
    let replayed = direct_expansion.or_else(|| replay_negated_existential(terms, original))?;
    (replayed == expanded).then_some(FiniteExpansionRecord {
        original,
        assertion_index,
        expanded,
    })
}

fn replay_negated_existential(terms: &mut TermStore, root: TermId) -> Option<TermId> {
    let TermData::Not(inner) = terms.get(root).clone() else {
        return None;
    };
    let TermData::Exists(vars, body, _) = terms.get(inner).clone() else {
        return None;
    };
    if vars.len() != 1 || vars[0].1 != Sort::Int || contains_quantifier(terms, body) {
        return None;
    }
    let (expanded, _) = crate::skolemize::finite_domain_expand_with_instances(terms, inner)?;
    if contains_quantifier(terms, expanded) {
        return None;
    }
    Some(terms.mk_not(expanded))
}

#[cfg(test)]
mod derivation_tests;

#[cfg(test)]
mod tests {
    use ay_core::term::Symbol;
    use num_bigint::BigInt;

    use super::*;

    fn negated_bounded_exists(terms: &mut TermStore) -> TermId {
        let name = "x".to_string();
        let x = terms.mk_var(&name, Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let three = terms.mk_int(BigInt::from(3));
        let lower = terms.mk_le(zero, x);
        let upper = terms.mk_le(x, three);
        let predicate = terms.mk_app(Symbol::named("P"), [x], Sort::Bool);
        let body = terms.mk_and(vec![lower, upper, predicate]);
        let exists = terms.mk_exists(vec![(name, Sort::Int)], body);
        terms.mk_not(exists)
    }

    #[test]
    fn records_the_exact_negated_existential_root() {
        let mut terms = TermStore::new();
        let root = negated_bounded_exists(&mut terms);
        let expanded = crate::skolemize::expand_finite_domain_subterms(&mut terms, root);
        let record = exact_record(&mut terms, root, 7, expanded, None)
            .expect("supported authored shell replays exactly");

        assert_eq!(record.original, root);
        assert_eq!(record.assertion_index, 7);
        assert_eq!(record.expanded, expanded);
        assert!(!contains_quantifier(&terms, expanded));
    }

    #[test]
    fn declines_ground_drift_and_non_int_shells() {
        let mut terms = TermStore::new();
        let root = negated_bounded_exists(&mut terms);
        let expanded = crate::skolemize::expand_finite_domain_subterms(&mut terms, root);
        let drift = terms.true_term();
        assert!(exact_record(&mut terms, root, 0, drift, None).is_none());

        let name = "b".to_string();
        let b = terms.mk_var(&name, Sort::Bool);
        let exists = terms.mk_exists(vec![(name, Sort::Bool)], b);
        let bool_root = terms.mk_not(exists);
        let bool_expanded = crate::skolemize::expand_finite_domain_subterms(&mut terms, bool_root);
        assert!(exact_record(&mut terms, bool_root, 0, bool_expanded, None).is_none());

        assert_ne!(expanded, root);
    }
}
