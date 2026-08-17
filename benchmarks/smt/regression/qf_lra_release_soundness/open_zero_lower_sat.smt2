; Copyright 2026 Andrew Yates
; SPDX-License-Identifier: Apache-2.0
;
; Hand-authored hermetic regression for #6582.
; x > 0 and y >= 0 make the lower endpoint of x + y an open zero.
; Therefore x + y <= 0 is false, while the x = 1 branch keeps the formula SAT.
(set-info :smt-lib-version 2.6)
(set-logic QF_LRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (> x 0))
(assert (>= y 0))
(assert (or (<= (+ x y) 0) (= x 1)))
(check-sat)
(exit)
