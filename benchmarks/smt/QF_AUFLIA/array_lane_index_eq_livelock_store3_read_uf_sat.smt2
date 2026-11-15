; Array-lane Nelson-Oppen livelock reproducer (z3-parity campaign, 2026-09-23).
;
; QF_ALIA/array_lane_index_eq_livelock_store3_read_sat.smt2 with one UF
; application beside it. z3 5.1.0: sat in 1 ms. The UF keeps the
; arrays-to-LIA rescue from saturating, so the AUFLIA route meets the store
; chain with nothing but its own axiom supply; its first SAT model decides
; `k0 = i0_0 = k4 = i0_2` through `k0`, and the combiner's index pass
; re-asserted the EUF-proved store-index equalities into the array solver on
; every fixpoint, claiming progress each time, until the 100-iteration cap
; returned the sound Unknown: main f399eca07a `unknown (incomplete)` in
; 40 ms, :smt.combiner_checks_total 2, :smt.no_rounds_total 200, both
; postures. With the pass restarting only on a new edge: sat, confirmed,
; 25 split-loop rounds, both postures.
(set-info :status sat)
(set-logic QF_AUFLIA)
(declare-fun k0 () Int)
(declare-fun k4 () Int)
(declare-fun i0_0 () Int)
(declare-fun i0_2 () Int)
(declare-fun v0_0 () Int)
(declare-fun v0_1 () Int)
(declare-fun v0_2 () Int)
(declare-fun s0 () (Array Int Int))
(declare-fun t0 () (Array Int Int))
(declare-fun f (Int) Int)
(assert (= s0 (store (store (store t0 i0_0 v0_0) k4 v0_1) i0_2 v0_2)))
(assert (> (select s0 k0) 3))
(assert (= (f k0) 1))
(check-sat)
(exit)
