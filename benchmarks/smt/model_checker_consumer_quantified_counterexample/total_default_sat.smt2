; Copyright 2026 Andrew Yates
; SPDX-License-Identifier: Apache-2.0
; Authored total-function pin control; not AY output or captured MODEL_CHECKER_CONSUMER source.
; SAT here does not establish a concrete callee implementation.
; Expected SAT: the retained else branch fixes index 64 too.
(set-logic ALL)
(define-fun summary ((x (_ BitVec 64))) (_ BitVec 1)
  (ite (bvult x (_ bv64 64)) #b1 #b1))
(declare-const local (_ BitVec 64))
(assert (= local (_ bv7 64)))
(assert (= (summary local) #b1))
(assert (forall ((i (_ BitVec 64)))
  (=> (bvult i (_ bv65 64)) (= (summary i) #b1))))
(check-sat)
