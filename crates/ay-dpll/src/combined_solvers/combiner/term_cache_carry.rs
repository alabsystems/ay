// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term-level caches carried between the fresh combiners of one lazy split
//! loop (#lazy-auflia-persistent-structure).
//!
//! The split loops build a fresh `TheoryCombiner` every round (the lazy AUFLIA,
//! AUFLIA-assumption and AUFLRA loops, and every arm of the UFLIA solve), so
//! every round re-derives facts that depend only on the immutable term DAG: the
//! LIA linear forms of every atom and shared equality, and the interface-
//! tracking plan of every asserted literal (LIA or LRA lane). This carry moves
//! those caches from one round's combiner into the next one. Every carried
//! entry is result-neutral (see [`ay_lia::LiaLinearParseCache`] and the
//! interface `track_plan` module), and each component re-checks that the store
//! it was built on is still an append-only prefix of the importer's, so
//! carrying can change the cost of a round and never its result.
//! Assignment-derived state is NOT carried: each round's combiner still starts
//! from the fresh state.

use super::TheoryCombiner;
use crate::combined_solvers::interface_bridge::InterfaceTrackPlans;

/// Term-level caches detached from one combiner for the next.
#[derive(Default)]
pub(crate) struct CombinerTermCacheCarry {
    lia: Option<ay_lia::LiaLinearParseCache>,
    interface: Option<InterfaceTrackPlans>,
}

impl CombinerTermCacheCarry {
    /// Keep each component a newer export carries and the older one where the
    /// newer export has none (a combiner that was already exported, or whose
    /// caches stayed empty, must not erase what the loop holds).
    pub(crate) fn absorb(&mut self, newer: Self) {
        if newer.lia.is_some() {
            self.lia = newer.lia;
        }
        if newer.interface.is_some() {
            self.interface = newer.interface;
        }
    }
}

impl TheoryCombiner<'_> {
    /// Move this combiner's term-level caches out. The combiner stays usable;
    /// it simply recomputes on its next miss.
    pub(crate) fn export_term_cache_carry(&mut self) -> CombinerTermCacheCarry {
        let terms = self.terms;
        CombinerTermCacheCarry {
            lia: self
                .lia
                .as_ref()
                .and_then(ay_lia::LiaSolver::export_linear_parse_cache),
            interface: self
                .interface
                .as_mut()
                .and_then(|interface| interface.export_track_plans(terms)),
        }
    }

    /// Seed this combiner's term-level caches from an earlier export.
    pub(crate) fn import_term_cache_carry(&mut self, carry: CombinerTermCacheCarry) {
        let terms = self.terms;
        if let (Some(lia), Some(cache)) = (self.lia.as_mut(), carry.lia) {
            lia.import_linear_parse_cache(cache);
        }
        if let (Some(interface), Some(plans)) = (self.interface.as_mut(), carry.interface) {
            interface.import_track_plans(terms, plans);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::term::Symbol;
    use ay_core::{Sort, TermStore, TheorySolver};
    use num_bigint::BigInt;
    use num_rational::BigRational;

    /// A combiner whose caches were already exported (or never filled) must
    /// not erase what the loop carries, and the carry must survive the trip
    /// through the next round's combiner.
    #[test]
    fn absorbing_an_empty_export_keeps_the_carried_caches() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let fx = terms.mk_app(Symbol::named("f"), [x], Sort::Int);
        let seven = terms.mk_int(BigInt::from(7));
        let lit = terms.mk_app(Symbol::named("="), [fx, seven], Sort::Bool);

        let mut first = TheoryCombiner::auf_lia(&terms);
        first.register_atom(lit);
        first.assert_literal(lit, true);
        let _ = first.check();
        let mut carry = first.export_term_cache_carry();
        assert!(
            carry.interface.is_some(),
            "the asserted literal was planned"
        );
        let had_lia = carry.lia.is_some();

        carry.absorb(first.export_term_cache_carry());
        assert!(carry.interface.is_some());
        assert_eq!(carry.lia.is_some(), had_lia);

        let mut second = TheoryCombiner::auf_lia(&terms);
        second.import_term_cache_carry(carry);
        let back = second.export_term_cache_carry();
        assert!(back.interface.is_some());
        assert_eq!(back.lia.is_some(), had_lia);
    }

    /// The AUFLRA lane has no LIA solver; its carry is the LRA-lane interface
    /// plans (#combiner-carry-other-lanes), and they survive the round trip.
    #[test]
    fn auf_lra_round_carries_its_real_lane_plans() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let fx = terms.mk_app(Symbol::named("f"), [x], Sort::Real);
        let half = terms.mk_rational(BigRational::new(BigInt::from(1), BigInt::from(2)));
        let lit = terms.mk_app(Symbol::named("="), [fx, half], Sort::Bool);

        let mut first = TheoryCombiner::auf_lra(&terms);
        first.register_atom(lit);
        first.assert_literal(lit, true);
        let carry = first.export_term_cache_carry();
        assert!(carry.lia.is_none(), "AUFLRA has no LIA lane");
        assert!(
            carry.interface.is_some(),
            "the asserted Real literal was planned on the LRA lane"
        );

        let mut second = TheoryCombiner::auf_lra(&terms);
        second.import_term_cache_carry(carry);
        second.register_atom(lit);
        second.assert_literal(lit, true);
        assert!(second.export_term_cache_carry().interface.is_some());
    }
}
