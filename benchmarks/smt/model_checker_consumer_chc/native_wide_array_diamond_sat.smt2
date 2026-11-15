; SOURCE-DERIVED EQUIVALENT, NOT AN EXACT ADAPTER CAPTURE.
; Derived from AY bmc/level_alias/tests/fixtures.rs::wide_array_diamond
; and the depth-2 formula in native.rs::array_and_bv129_exact_tree_stages_preserve_original_ground_evidence.
; Four independent tree nodes: Q(0)->P(1), R(2)->P(3).
; Six choices: Q rule0, P facts1/2, R rule3, P facts4/5.
; All unconditional argument links, both alternative facts at each P node,
; both query roots, and the complete original query constraint are retained.
; 2^128 = 340282366920938463463374607431768211456; next differs in bit0.
; This is an SMT SAT witness query, not CHC satisfiability polarity.
; Run under an explicit external wall/RSS envelope; native AY currently returns resourceout.
; ALL admits the solver constant-array extension on the reference Z3 4.8.12.
(set-logic ALL)
(set-info :status sat)
(set-option :produce-models true)
(set-option :timeout 10000)

(declare-const __tree_q_a (Array (_ BitVec 8) (_ BitVec 129)))
(declare-const __tree_q_b (Array (_ BitVec 8) (_ BitVec 129)))
(declare-const __tree_q_x (_ BitVec 129))
(declare-const __tree_q_y (_ BitVec 129))
(declare-const __tree_n0_a0 (Array (_ BitVec 8) (_ BitVec 129)))
(declare-const __tree_n0_a1 (_ BitVec 129))
(declare-const __tree_n1_a0 (Array (_ BitVec 8) (_ BitVec 129)))
(declare-const __tree_n1_a1 (_ BitVec 129))
(declare-const __tree_n2_a0 (Array (_ BitVec 8) (_ BitVec 129)))
(declare-const __tree_n2_a1 (_ BitVec 129))
(declare-const __tree_n3_a0 (Array (_ BitVec 8) (_ BitVec 129)))
(declare-const __tree_n3_a1 (_ BitVec 129))
(declare-const __tree_c0_v0 (Array (_ BitVec 8) (_ BitVec 129)))
(declare-const __tree_c0_v1 (_ BitVec 129))
(declare-const __tree_c3_v0 (Array (_ BitVec 8) (_ BitVec 129)))
(declare-const __tree_c3_v1 (_ BitVec 129))
(declare-const __tree_ind_0 Bool)
(declare-const __tree_ind_1 Bool)
(declare-const __tree_ind_2 Bool)
(declare-const __tree_ind_3 Bool)
(declare-const __tree_ind_4 Bool)
(declare-const __tree_ind_5 Bool)

; First query root and its independent fact occurrence.
(assert (= __tree_q_a __tree_n0_a0))
(assert (= __tree_q_x __tree_n0_a1))
(assert (= __tree_c0_v0 __tree_n1_a0))
(assert (= __tree_c0_v1 __tree_n1_a1))
(assert (=> __tree_ind_1
  (and (= __tree_n1_a0 (store ((as const (Array (_ BitVec 8) (_ BitVec 129))) (_ bv0 129)) (_ bv7 8) (_ bv340282366920938463463374607431768211456 129)))
       (= __tree_n1_a1 (_ bv340282366920938463463374607431768211456 129)))))
(assert (=> __tree_ind_2
  (and (= __tree_n1_a0 (store ((as const (Array (_ BitVec 8) (_ BitVec 129))) (_ bv0 129)) (_ bv7 8) (_ bv340282366920938463463374607431768211457 129)))
       (= __tree_n1_a1 (_ bv340282366920938463463374607431768211457 129)))))
(assert (=> __tree_ind_0
  (and (= __tree_n0_a0 __tree_c0_v0)
       (= __tree_n0_a1 __tree_c0_v1)
       (or __tree_ind_1 __tree_ind_2))))
(assert __tree_ind_0)

; Second query root: its P occurrence is not shared with the first root.
(assert (= __tree_q_b __tree_n2_a0))
(assert (= __tree_q_y __tree_n2_a1))
(assert (= __tree_c3_v0 __tree_n3_a0))
(assert (= __tree_c3_v1 __tree_n3_a1))
(assert (=> __tree_ind_4
  (and (= __tree_n3_a0 (store ((as const (Array (_ BitVec 8) (_ BitVec 129))) (_ bv0 129)) (_ bv7 8) (_ bv340282366920938463463374607431768211456 129)))
       (= __tree_n3_a1 (_ bv340282366920938463463374607431768211456 129)))))
(assert (=> __tree_ind_5
  (and (= __tree_n3_a0 (store ((as const (Array (_ BitVec 8) (_ BitVec 129))) (_ bv0 129)) (_ bv7 8) (_ bv340282366920938463463374607431768211457 129)))
       (= __tree_n3_a1 (_ bv340282366920938463463374607431768211457 129)))))
(assert (=> __tree_ind_3
  (and (= __tree_n2_a0 __tree_c3_v0)
       (= __tree_n2_a1 __tree_c3_v1)
       (or __tree_ind_4 __tree_ind_5))))
(assert __tree_ind_3)

; Complete original query constraint, with both scalar/array observations.
(assert (not (= __tree_q_x __tree_q_y)))
(assert (= (select __tree_q_a (_ bv7 8)) __tree_q_x))
(assert (= (select __tree_q_b (_ bv7 8)) __tree_q_y))
(check-sat)
(get-info :reason-unknown)
(get-info :all-statistics)
(get-model)
