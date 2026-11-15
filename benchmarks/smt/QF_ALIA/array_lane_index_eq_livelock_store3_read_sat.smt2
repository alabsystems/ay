; Array-lane Nelson-Oppen livelock reproducer (z3-parity campaign, 2026-09-22).
;
; Two assertions: a three-deep store chain with SYMBOLIC indices and one
; inequality read. z3 5.1.0: sat in 1 ms. As this single QF_ALIA check-sat,
; main decides it through the arrays-to-LIA rescue, whose saturation interns
; the reads the AUFLIA route's array-axiom fixpoint then uses. Whenever the
; route meets the same problem WITHOUT that saturation in the term store (a
; UF beside it, an Int->Bool array, a push/pop scope, or a rescue that bails
; before interning), its first SAT model decides `k0 = i0_0 = k4 = i0_2`
; through `k0`, and the combiner's index pass asserted the EUF-proved
; store-index equalities `k4 = i0_2` / `i0_0 = i0_2` into the array solver as
; external edges on every fixpoint — claiming progress each time although the
; pair stayed undecided for the atom-keyed store-chain walk — until the
; 100-iteration cap returned the sound Unknown (:smt.no_rounds_total 200).
; The pass now restarts the loop only when the edge is new and otherwise
; routes the pair to the ordinary SAT-level model-equality split. This file
; must stay sat; its livelocking twins are in
; crates/ay-dpll/tests/group_regression/array_lane_index_eq_livelock.rs.
(set-info :status sat)
(set-logic QF_ALIA)
(declare-fun k0 () Int)
(declare-fun k4 () Int)
(declare-fun i0_0 () Int)
(declare-fun i0_2 () Int)
(declare-fun v0_0 () Int)
(declare-fun v0_1 () Int)
(declare-fun v0_2 () Int)
(declare-fun s0 () (Array Int Int))
(declare-fun t0 () (Array Int Int))
(assert (= s0 (store (store (store t0 i0_0 v0_0) k4 v0_1) i0_2 v0_2)))
(assert (> (select s0 k0) 3))
(check-sat)
(exit)
