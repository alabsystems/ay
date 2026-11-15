; SATISFIABLE MUTANT TWIN: the guard `i >= _13` flipped to `i < _13` in BOTH or-branches, so the violation is reachable and the query is SAT. It exercises the same recorded-rewrite shape and must NEVER be reported unsat.
;
; Captured from deductive-checksgen's `escaped_local_seam_realmir` fixture
; `escaped_seam_a5_two_next_if_ok_sym_mir.json`, rendered by
; trust-router's `in_process_ay_backend::problem_smt2` (the byte-exact
; transcript of the AYProgram the in-process lane executes). The option
; block is what that lane asks for through the API: a strict-checked UNSAT
; proof.
(set-option :produce-proofs true)
(set-option :check-proofs-strict true)
(set-logic QF_LIA)
(declare-fun __trust_u__11 () Int)
(declare-fun __trust_u__13 () Int)
(declare-fun __trust_u__14 () Bool)
(declare-fun __trust_u__5 () Bool)
(declare-fun __trust_u___trust_mir__discr_o () Int)
(declare-fun __trust_u_a__slice_len () Int)
(declare-fun __trust_u_c () Bool)
(declare-fun __trust_u_i () Int)
(declare-fun __trust_u_m () Int)
(declare-fun __trust_u_n () Int)
(declare-fun __trust_u_o@1.0 () Int)
(assert (and (= __trust_u_n __trust_u_a__slice_len) (= __trust_u__5 (> __trust_u_m __trust_u_n)) (or (and (not (> __trust_u_m __trust_u_a__slice_len)) (not __trust_u_c) (= __trust_u__11 1) (or (= __trust_u__11 0) (= __trust_u__11 1)) (and (>= __trust_u_m 0) (<= __trust_u_m 18446744073709551615)) (and (or (= __trust_u___trust_mir__discr_o 0) (= __trust_u___trust_mir__discr_o 1)) (or (= __trust_u__11 0) (= __trust_u__11 1)) (and (or (and (>= __trust_u_i 0) (< __trust_u_i __trust_u_a__slice_len)) (and (>= __trust_u_i 1) (< __trust_u_i __trust_u_m))) (and (= __trust_u_n __trust_u_a__slice_len) (= __trust_u__5 (> __trust_u_m __trust_u_n)) (and (= __trust_u_i __trust_u_o@1.0) (= __trust_u__13 __trust_u_a__slice_len) (= __trust_u__14 (< __trust_u_i __trust_u__13)) (< __trust_u_i __trust_u__13)))))) (and (not (> __trust_u_m __trust_u_a__slice_len)) __trust_u_c (= __trust_u__11 1) (or (= __trust_u__11 0) (= __trust_u__11 1)) (and (>= __trust_u_m 0) (<= __trust_u_m 18446744073709551615)) (and (or (= __trust_u___trust_mir__discr_o 0) (= __trust_u___trust_mir__discr_o 1)) (or (= __trust_u__11 0) (= __trust_u__11 1)) (and (or (and (>= __trust_u_i 0) (< __trust_u_i __trust_u_a__slice_len)) (and (>= __trust_u_i 1) (< __trust_u_i __trust_u_m))) (and (= __trust_u_n __trust_u_a__slice_len) (= __trust_u__5 (> __trust_u_m __trust_u_n)) (and (= __trust_u_i __trust_u_o@1.0) (= __trust_u__13 __trust_u_a__slice_len) (= __trust_u__14 (< __trust_u_i __trust_u__13)) (< __trust_u_i __trust_u__13)))))))))
(check-sat)

