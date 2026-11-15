; Copyright 2026 Andrew Yates
; SPDX-License-Identifier: Apache-2.0
; Independently authored original-source conjunction, not AY output or MC capture.
; Unconstrained function models are not evidence of concrete callee behavior.
; Expected UNSAT: one global function cannot disagree on equal arguments.
(set-logic ALL)
(declare-fun summary (Bool (_ BitVec 64)) (_ BitVec 1))
(declare-const x0 (_ BitVec 64))
(declare-const value0 (_ BitVec 1))
(declare-const x1 (_ BitVec 64))
(declare-const value1 (_ BitVec 1))
(assert (= x0 (_ bv7 64)))
(assert (= value0 (summary true x0)))
(assert (= value0 (_ bv1 1)))
(assert (forall ((i (_ BitVec 64)))
  (=> (bvult i (_ bv65 64)) (= (summary false i) (_ bv1 1)))))
(assert (= x1 x0))
(assert (= value1 value0))
(assert (= (summary true x1) (_ bv0 1)))
(check-sat)
