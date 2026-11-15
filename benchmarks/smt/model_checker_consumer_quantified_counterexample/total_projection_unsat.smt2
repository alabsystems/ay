; Copyright 2026 Andrew Yates
; SPDX-License-Identifier: Apache-2.0
; Authored total-function pin control; not AY output or captured MODEL_CHECKER_CONSUMER source.
; SAT here does not establish a concrete callee implementation.
; Expected UNSAT: a BV136 projection is a complete body, not a table prefix.
(set-logic ALL)
(define-fun identity ((x (_ BitVec 136))) (_ BitVec 136)
  (_ bv0 136))
(declare-const local (_ BitVec 136))
(assert (= local (_ bv43556142965880123323311949751266331066375 136)))
(assert (= (identity local) local))
(assert (forall ((i (_ BitVec 64)))
  (= (identity ((_ zero_extend 72) i)) ((_ zero_extend 72) i))))
(check-sat)
