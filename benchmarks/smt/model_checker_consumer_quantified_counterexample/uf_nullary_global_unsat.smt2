; Copyright 2026 Andrew Yates
; SPDX-License-Identifier: Apache-2.0
; Independently authored original-source conjunction, not AY output or MC capture.
; Unconstrained function models are not evidence of concrete callee behavior.
; Expected UNSAT: the nullary BV136 function is one global value, not fresh per occurrence.
(set-logic ALL)
(declare-fun summary () (_ BitVec 136))
(declare-fun unused ((_ BitVec 72)) (_ BitVec 8))
(declare-const value0 (_ BitVec 136))
(declare-const value1 (_ BitVec 136))
(assert (= value0 summary))
(assert (= value0 (_ bv0 136)))
(assert (= value1 summary))
(assert (= value1 (concat (_ bv1 8) (_ bv0 128))))
(check-sat)
