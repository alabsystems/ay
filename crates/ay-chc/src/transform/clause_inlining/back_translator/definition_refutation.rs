// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The satisfiability checks of the AllSAT+MBP projection, refuted with their
//! top-level definitions substituted away first.
//!
//! The formula of a straight-line predicate pins a clause-local array to a
//! store chain (`obj_valid = store(...)`). Kept, every check is an array query
//! the executor answers, and in the default proof-carrying posture it took
//! about two seconds to refute such a formula with no conflict at all
//! (model-checker-consumer realloc-grow pre-discharge VC, 2026-10-14). Substituted away,
//! the same refutation is constant folding or a small bit-vector query.

use super::{ChcExpr, InliningBackTranslator, SmtContext, SmtResult, EXISTENTIAL_QE_CHECK_TIMEOUT};
use ay_core::time::Instant;

impl InliningBackTranslator {
    /// [`SmtContext::check_sat_with_executor_fallback_timeout`] on `query`
    /// within [`EXISTENTIAL_QE_CHECK_TIMEOUT`], except that a query refuted
    /// without its definitions ([`Self::refuted_without_definitions`]) is
    /// `Unsat` at once. That attempt is charged to the same timeout, so one
    /// check retains one absolute end through preprocessing and nested solving.
    /// A result arriving after that end is not published. A `Sat` answer, whose model MBP
    /// reads for every variable, always comes from `query` itself.
    pub(super) fn check_projection_query(smt: &mut SmtContext, query: &ChcExpr) -> SmtResult {
        let Some(local_end) = Instant::now().checked_add(EXISTENTIAL_QE_CHECK_TIMEOUT) else {
            return SmtResult::Unknown;
        };
        let deadline = [
            Some(local_end),
            smt.current_global_deadline(),
            crate::smt::deadline::effective_thread_deadline(),
        ]
        .into_iter()
        .flatten()
        .min()
        .unwrap_or(local_end);
        let _absolute = crate::smt::ScopedSmtDeadline::install_until(deadline);
        let original = match ay_core::resource::current_check_stop() {
            Ok(original) => original,
            Err(_) => return SmtResult::Unknown,
        };
        let guard = ay_core::resource::current_guard();
        let stopped = |smt: &SmtContext| {
            original.as_ref().is_some_and(|stop| stop())
                || guard.as_ref().is_some_and(|guard| guard.poll().is_some())
                || ay_core::resource::check_stop_requested()
                || crate::smt::deadline::lane_cancelled()
                || smt.exact_term_memory_exceeded()
                || smt.deadlines_expired()
                || Instant::now() >= deadline
        };
        if stopped(smt) {
            return SmtResult::Unknown;
        }
        let refuted = Self::refuted_without_definitions(smt, query);
        if stopped(smt) {
            return SmtResult::Unknown;
        }
        if refuted {
            return SmtResult::Unsat;
        }
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return SmtResult::Unknown;
        }
        let result = smt.check_sat_with_executor_fallback_timeout(query, remaining);
        if stopped(smt) {
            SmtResult::Unknown
        } else {
            result
        }
    }

    /// Whether a synthesized definition over arrays is refuted with its
    /// top-level definitions substituted away
    /// ([`ChcExpr::eliminate_top_level_definitions`]; an `unsat` of the result
    /// is one of the definition): it folds to `false`, keeps a literal beside
    /// its negation, or its array-free reduction is refuted by one
    /// [`Self::check_projection_query`] under the same original owner. Such a
    /// definition never fires, so its exact image is `false`. `Some(false)`
    /// means only "not refuted here"; `None` means the original owner stopped
    /// first, which publishes no fact.
    ///
    /// A pinned clause-local array made the exact arena decline these
    /// definitions, and the legacy projection refuted them (its constant and
    /// equality folding, then its first bounded check), until the arena
    /// admitted flat arrays (5eb47055a). Admitted, a definition whose shared
    /// conjuncts contradict each other, conjoined with independent
    /// disjunctions (the stack-slot separation of the model-checker-consumer realloc VC),
    /// spends the arena's whole branch bound, a terminal stop, before any
    /// branch sees the contradiction every branch shares.
    pub(super) fn refuted_definition(formula: &ChcExpr) -> Option<bool> {
        if !formula.contains_array_ops() {
            return Some(false);
        }
        let memory = crate::bmc::memory::Budget::capture(None, None);
        let stopped = || {
            ay_core::resource::current_check_stop()
                .ok()
                .is_none_or(|original| original.is_some_and(|stop| stop()))
                || ay_core::resource::current_guard().is_some_and(|guard| guard.poll().is_some())
                || ay_core::resource::check_stop_requested()
                || ay_core::resource::process_cancelled()
                || crate::smt::deadline::lane_cancelled()
                || crate::smt::smt_deadline_expired()
                || crate::smt::deadline::effective_thread_deadline()
                    .is_some_and(|end| Instant::now() >= end)
                || !memory.open()
        };
        if stopped() {
            return None;
        }
        let reduced = formula.eliminate_top_level_definitions();
        if stopped() {
            return None;
        }
        if matches!(reduced, ChcExpr::Bool(false)) || Self::has_syntactic_contradiction(&reduced) {
            return Some(true);
        }
        // An array query stays with the projection: only an array-free
        // reduction gets the one bounded check (`Unknown` is not a refutation).
        if reduced.contains_array_ops() {
            return Some(false);
        }
        let refuted = Self::check_projection_query(&mut SmtContext::new(), &reduced).is_unsat();
        if stopped() {
            return None;
        }
        Some(refuted)
    }

    /// Whether `query` with its top-level definitions substituted away
    /// ([`ChcExpr::eliminate_top_level_definitions`]; an `unsat` of the
    /// result is one of `query`) is refuted. Tried only for an array query
    /// that the substitution folds to a constant or rids of every array
    /// operation; `false` means only "not refuted here".
    fn refuted_without_definitions(smt: &mut SmtContext, query: &ChcExpr) -> bool {
        if !query.contains_array_ops() {
            return false;
        }
        match query.eliminate_top_level_definitions() {
            ChcExpr::Bool(value) => !value,
            reduced if reduced.contains_array_ops() => false,
            reduced => smt
                .check_sat_with_timeout(&reduced, EXISTENTIAL_QE_CHECK_TIMEOUT)
                .is_unsat(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ChcSort, ChcVar};

    fn valid() -> ChcExpr {
        ChcExpr::var(ChcVar::new(
            "obj_valid",
            ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::Bool)),
        ))
    }

    /// `obj_valid = store(const true, 66, live)` and `obj_valid[66] = read`.
    fn pinned_read(live: bool, read: bool) -> ChcExpr {
        let store = ChcExpr::store(
            ChcExpr::const_array(ChcSort::BitVec(32), ChcExpr::Bool(true)),
            ChcExpr::BitVec(66, 32),
            ChcExpr::Bool(live),
        );
        let select = ChcExpr::select(valid(), ChcExpr::BitVec(66, 32));
        let read = if read { select } else { ChcExpr::not(select) };
        ChcExpr::and(ChcExpr::eq(valid(), store), read)
    }

    #[test]
    fn a_pinned_array_read_is_refuted_without_its_definition() {
        let mut smt = SmtContext::new();
        let query = pinned_read(true, false);
        assert!(InliningBackTranslator::refuted_without_definitions(
            &mut smt, &query
        ));
        assert!(InliningBackTranslator::check_projection_query(&mut smt, &query).is_unsat());
    }

    /// Negative twin: a satisfiable pinned read is not refuted, and its model
    /// comes from the query itself.
    #[test]
    fn a_satisfiable_pinned_read_keeps_its_model() {
        let mut smt = SmtContext::new();
        let query = pinned_read(true, true);
        assert!(!InliningBackTranslator::refuted_without_definitions(
            &mut smt, &query
        ));
        assert!(matches!(
            InliningBackTranslator::check_projection_query(&mut smt, &query),
            SmtResult::Sat(_)
        ));
    }

    fn flag(name: &str) -> ChcExpr {
        ChcExpr::var(ChcVar::new(name, ChcSort::Bool))
    }

    /// Seven independent stack-slot separations: 2^7 alternatives, twice the
    /// exact arena's branch bound, none of which a refutation needs.
    fn separations() -> Vec<ChcExpr> {
        let slot = |i: usize| ChcExpr::var(ChcVar::new(format!("slot_{i}"), ChcSort::BitVec(64)));
        (0..7)
            .map(|i| {
                ChcExpr::or(
                    ChcExpr::bv_ule(slot(i), slot(i + 1)),
                    ChcExpr::bv_ule(slot(i + 1), slot(i)),
                )
            })
            .collect()
    }

    /// The nullary `error` definition of the realloc VC: a pinned
    /// `obj_valid`, `live = fld`, `fld`, and `live` (negated when `refuted`),
    /// beside the separations. `pinned` false drops the array.
    fn error_definition(pinned: bool, refuted: bool) -> ChcExpr {
        let live = if refuted {
            ChcExpr::not(flag("live"))
        } else {
            flag("live")
        };
        let mut conjuncts = vec![ChcExpr::eq(flag("live"), flag("fld")), flag("fld"), live];
        if pinned {
            conjuncts.push(pinned_read(true, true));
        }
        conjuncts.extend(separations());
        ChcExpr::and_all(conjuncts)
    }

    fn close_nullary(formula: ChcExpr) -> Option<crate::PredicateInterpretation> {
        InliningBackTranslator::close_synthesized_interpretation(
            crate::PredicateInterpretation::new(Vec::new(), formula),
        )
    }

    /// Regression (5eb47055a, on main since 47276a301): the exact arena
    /// admits the pinned array and stops on its branch bound, so `error` had
    /// no interpretation and the realloc VC's back-translated Safe model was
    /// refused. Refuted first, the definition closes to `false`.
    #[test]
    fn a_refuted_pinned_array_definition_closes_to_false_before_the_branch_bound() {
        let shared = error_definition(true, true);
        assert_eq!(
            InliningBackTranslator::refuted_definition(&shared),
            Some(true)
        );
        let closed = close_nullary(shared).expect("refuted definition closes");
        assert_eq!(closed.formula, ChcExpr::Bool(false));
        // error_p29: the pinned array read folds to `false` once substituted.
        let read = ChcExpr::and_all(std::iter::once(pinned_read(false, true)).chain(separations()));
        let closed = close_nullary(read).expect("refuted read closes");
        assert_eq!(closed.formula, ChcExpr::Bool(false));
    }

    /// `obj_valid = store(const true, 66, live)`, the separations and `rest`.
    fn pinned_live(rest: Vec<ChcExpr>) -> ChcExpr {
        let store = ChcExpr::store(
            ChcExpr::const_array(ChcSort::BitVec(32), ChcExpr::Bool(true)),
            ChcExpr::BitVec(66, 32),
            flag("live"),
        );
        let pinned = ChcExpr::eq(valid(), store);
        ChcExpr::and_all(std::iter::once(pinned).chain(rest).chain(separations()))
    }

    /// `not (or (not obj_valid[66]) fld)` beside `live` (negated if `refuted`).
    fn guarded_read(refuted: bool) -> ChcExpr {
        let read = ChcExpr::select(valid(), ChcExpr::BitVec(66, 32));
        let guard = ChcExpr::not(ChcExpr::or(ChcExpr::not(read), flag("fld")));
        let live = if refuted {
            ChcExpr::not(flag("live"))
        } else {
            flag("live")
        };
        pinned_live(vec![guard, live])
    }

    /// `x <= 3 /\ not (x <= 5)` (bit-vector), or its satisfiable swap.
    fn range(refuted: bool) -> ChcExpr {
        let x = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(32)));
        let (low, high) = if refuted { (3, 5) } else { (5, 3) };
        pinned_live(vec![
            ChcExpr::bv_ule(x.clone(), ChcExpr::BitVec(low, 32)),
            ChcExpr::not(ChcExpr::bv_ule(x, ChcExpr::BitVec(high, 32))),
        ])
    }

    /// A contradiction no folding exposes (a negated guard, a range) leaves an
    /// array-free reduction that one bounded check refutes, as the legacy
    /// projection's first check did before 5eb47055a.
    #[test]
    fn an_array_free_reduction_is_refuted_by_one_bounded_check() {
        for refuted in [guarded_read(true), range(true)] {
            assert_eq!(
                InliningBackTranslator::refuted_definition(&refuted),
                Some(true)
            );
            let closed = close_nullary(refuted).expect("refuted definition closes");
            assert_eq!(closed.formula, ChcExpr::Bool(false));
        }
    }

    /// Negative twins: a satisfiable pinned definition, with or without a
    /// bounded check, is not refuted (it still reaches the bounded projection,
    /// and is never `false`); a scalar definition is never tried here.
    #[test]
    fn satisfiable_and_scalar_definitions_are_not_refuted() {
        for satisfiable in [
            error_definition(true, false),
            guarded_read(false),
            range(false),
        ] {
            assert_eq!(
                InliningBackTranslator::refuted_definition(&satisfiable),
                Some(false)
            );
            assert!(close_nullary(satisfiable)
                .is_none_or(|closed| closed.formula != ChcExpr::Bool(false)));
        }
        let scalar = error_definition(false, true);
        assert_eq!(
            InliningBackTranslator::refuted_definition(&scalar),
            Some(false)
        );
    }

    /// A stopped original owner publishes no fact: an expired deadline, a
    /// stopped check, a cancelled lane or a zero term budget, on either path.
    #[test]
    fn a_stopped_owner_never_publishes_a_refutation() {
        let refused = || {
            for refuted in [error_definition(true, true), range(true)] {
                assert_eq!(InliningBackTranslator::refuted_definition(&refuted), None);
                assert!(close_nullary(refuted).is_none());
            }
        };
        {
            let _expired = crate::smt::ScopedSmtDeadline::install(std::time::Duration::ZERO);
            refused();
        }
        {
            let _owner = ay_core::resource::enter_check_stop(std::sync::Arc::new(|| true));
            refused();
        }
        {
            let token = crate::cancellation::CancellationToken::new();
            token.cancel();
            let _lane = crate::smt::deadline::ScopedLaneCancellation::install(token, None);
            refused();
        }
        {
            let _memory = crate::bmc::memory::Budget::capture(Some(0), None).install();
            refused();
        }
    }

    /// The publication fence after the substitution: an owner that stops
    /// during it publishes nothing.
    #[test]
    fn publication_fence_refuses_a_definition_refuted_after_owner_stops() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        use std::sync::Arc;
        let polls = Arc::new(AtomicUsize::new(0));
        let observed = Arc::clone(&polls);
        let _owner = ay_core::resource::enter_check_stop(Arc::new(move || {
            observed.fetch_add(1, Ordering::SeqCst) >= 1
        }));
        let shared = error_definition(true, true);
        assert_eq!(InliningBackTranslator::refuted_definition(&shared), None);
        assert_eq!(polls.load(Ordering::SeqCst), 2);
    }

    #[test]
    fn expired_outer_deadline_refuses_even_constant_refutation() {
        let mut smt = SmtContext::new();
        let before = crate::smt::deadline::effective_thread_deadline();
        {
            let _outer = crate::smt::ScopedSmtDeadline::install(std::time::Duration::ZERO);
            assert!(matches!(
                InliningBackTranslator::check_projection_query(&mut smt, &pinned_read(true, false)),
                SmtResult::Unknown
            ));
        }
        assert_eq!(crate::smt::deadline::effective_thread_deadline(), before);
    }

    #[test]
    fn expired_context_deadline_refuses_even_constant_refutation() {
        let mut smt = SmtContext::new();
        smt.set_global_solve_deadline(Some(Instant::now()));
        assert!(matches!(
            InliningBackTranslator::check_projection_query(&mut smt, &pinned_read(true, false)),
            SmtResult::Unknown
        ));
    }

    #[test]
    fn cancelled_lane_refuses_even_constant_refutation() {
        let mut smt = SmtContext::new();
        let token = crate::cancellation::CancellationToken::new();
        token.cancel();
        let _lane = crate::smt::deadline::ScopedLaneCancellation::install(token, None);
        assert!(matches!(
            InliningBackTranslator::check_projection_query(&mut smt, &pinned_read(true, false)),
            SmtResult::Unknown
        ));
    }

    #[test]
    fn stopped_original_owner_never_publishes_constant_refutation() {
        let mut smt = SmtContext::new();
        let _owner = ay_core::resource::enter_check_stop(std::sync::Arc::new(|| true));
        assert!(matches!(
            InliningBackTranslator::check_projection_query(&mut smt, &pinned_read(true, false)),
            SmtResult::Unknown
        ));
    }

    #[test]
    fn publication_fence_refuses_a_refutation_after_owner_stops() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        use std::sync::Arc;
        let mut smt = SmtContext::new();
        let polls = Arc::new(AtomicUsize::new(0));
        let observed = Arc::clone(&polls);
        // Each open fence polls captured and ambient ownership. The third
        // observation is the first fence after the constant simplification.
        let _owner = ay_core::resource::enter_check_stop(Arc::new(move || {
            observed.fetch_add(1, Ordering::SeqCst) >= 2
        }));
        assert!(matches!(
            InliningBackTranslator::check_projection_query(&mut smt, &pinned_read(true, false)),
            SmtResult::Unknown
        ));
        assert_eq!(polls.load(Ordering::SeqCst), 3);
    }

    #[test]
    fn original_absolute_end_surrounds_real_smt_and_is_restored() {
        use std::sync::{Arc, Mutex};
        let mut smt = SmtContext::new();
        let before = crate::smt::deadline::effective_thread_deadline();
        let end = Instant::now() + std::time::Duration::from_secs(2);
        smt.set_global_solve_deadline(Some(end));
        let seen = Arc::new(Mutex::new(Vec::new()));
        let observed = Arc::clone(&seen);
        let _owner = ay_core::resource::enter_check_stop(Arc::new(move || {
            let current = crate::smt::deadline::effective_thread_deadline().unwrap();
            assert!(current <= end);
            // A later duration-derived child scope must never move the end.
            let _nested =
                crate::smt::ScopedSmtDeadline::install(std::time::Duration::from_secs(60));
            assert_eq!(
                crate::smt::deadline::effective_thread_deadline(),
                Some(current)
            );
            observed.lock().unwrap().push(current);
            false
        }));
        assert!(matches!(
            InliningBackTranslator::check_projection_query(&mut smt, &pinned_read(true, true)),
            SmtResult::Sat(_)
        ));
        let seen = seen.lock().unwrap();
        assert!(
            seen.len() >= 6,
            "entry, pre-SMT and publication fences must poll"
        );
        assert_eq!(seen[0], before.map_or(end, |outer| outer.min(end)));
        assert_eq!(crate::smt::deadline::effective_thread_deadline(), before);
    }
}
