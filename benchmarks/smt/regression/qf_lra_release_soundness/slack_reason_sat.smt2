; Copyright 2026 Andrew Yates
; SPDX-License-Identifier: Apache-2.0
;
; Hand-authored hermetic regression for #6564.
; Fixing y at zero and bounding x + y derives x <= 3 through a slack row.
; The disjunction keeps x <= 3 registered, forcing the release solver to
; materialize and consume the implied-bound reason without excluding x = 2.
(set-info :smt-lib-version 2.6)
(set-logic QF_LRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (>= y 0))
(assert (<= y 0))
(assert (<= (+ x y) 3))
(assert (or (> x 3) (= x 2)))
(check-sat)
(exit)
