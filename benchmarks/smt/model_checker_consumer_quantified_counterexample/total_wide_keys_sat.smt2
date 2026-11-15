; Copyright 2026 Andrew Yates
; SPDX-License-Identifier: Apache-2.0
; Authored total-function pin control; not AY output or captured MODEL_CHECKER_CONSUMER source.
; SAT here does not establish a concrete callee implementation.
; Expected SAT: exception keys differing above bit 127 must stay distinct.
(set-logic ALL)
(define-fun summary ((guard Bool) (key (_ BitVec 136))) (_ BitVec 1)
  (ite (and guard (= key (_ bv43556142965880123323311949751266331066375 136))) #b1 #b0))
(define-fun unused () (_ BitVec 72) (_ bv17 72))
(assert (= (summary true (_ bv43556142965880123323311949751266331066375 136)) #b1))
(assert (= (summary true (_ bv7 136)) #b0))
(assert (forall ((i (_ BitVec 64)))
  (=> (bvult i (_ bv65 64))
      (= (summary true ((_ zero_extend 72) i)) #b0))))
(check-sat)
