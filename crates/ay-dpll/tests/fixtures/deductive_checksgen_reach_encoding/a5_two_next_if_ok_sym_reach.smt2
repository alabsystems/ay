; The deductive-checksgen SliceBoundsCheck row of escaped_seam_a5_two_next_if_ok_sym (the join R_bb5 == Or(..)): UNSAT.
;
; Captured from the superproject (alabsystems/trust, mem/ever-init-paths d845b42dce2)
; with the reach encoding used for every block (RETIRED_SPELLING_MAX_PATHS = 0 and
; the content-free in-edge summary off), rendered by trust-router's
; in_process_ay_backend::problem_smt2 -- the transcript of the AYProgram the
; in-process lane executes -- with that lane's option block. DECISION_QUEUE D16.
(set-option :produce-proofs true)
(set-option :timeout 60000)
(set-logic QF_LIA)
(declare-fun __trust_u__11 () Int)
(declare-fun __trust_u__13 () Int)
(declare-fun __trust_u__14 () Bool)
(declare-fun __trust_u__5 () Bool)
(declare-fun __trust_u___trust_mir__discr_o () Int)
(declare-fun __trust_u___trust_reach_bb2 () Bool)
(declare-fun __trust_u___trust_reach_bb5 () Bool)
(declare-fun __trust_u_a__slice_len () Int)
(declare-fun __trust_u_c () Bool)
(declare-fun __trust_u_i () Int)
(declare-fun __trust_u_m () Int)
(declare-fun __trust_u_n () Int)
(declare-fun __trust_u_o@1.0 () Int)
(assert (and (= __trust_u_n __trust_u_a__slice_len) (= __trust_u__5 (> __trust_u_m __trust_u_n)) (= __trust_u___trust_reach_bb2 (not (> __trust_u_m __trust_u_a__slice_len))) (= __trust_u___trust_reach_bb5 (or (and __trust_u___trust_reach_bb2 (not __trust_u_c)) (and __trust_u___trust_reach_bb2 __trust_u_c))) __trust_u___trust_reach_bb5 (= __trust_u__11 1) (or (= __trust_u__11 0) (= __trust_u__11 1)) (>= __trust_u_m 0) (<= __trust_u_m 18446744073709551615) (or (= __trust_u___trust_mir__discr_o 0) (= __trust_u___trust_mir__discr_o 1)) (or (= __trust_u__11 0) (= __trust_u__11 1)) (or (and (>= __trust_u_i 0) (< __trust_u_i __trust_u_a__slice_len)) (and (>= __trust_u_i 1) (< __trust_u_i __trust_u_m))) (= __trust_u_n __trust_u_a__slice_len) (= __trust_u__5 (> __trust_u_m __trust_u_n)) (= __trust_u_i __trust_u_o@1.0) (= __trust_u__13 __trust_u_a__slice_len) (= __trust_u__14 (< __trust_u_i __trust_u__13)) (>= __trust_u_i __trust_u__13)))
(check-sat)
