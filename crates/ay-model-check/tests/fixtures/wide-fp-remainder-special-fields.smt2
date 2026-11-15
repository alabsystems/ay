; Copyright 2026 Andrew Yates
; SPDX-License-Identifier: Apache-2.0
; Field-only remainder results must not materialize a huge finite dyadic.
(set-logic QF_FP)
(set-info :status sat)
(declare-const dividend (_ FloatingPoint 32 200))
(assert (= dividend (fp #b1 #xfffffffe (_ bv1 199))))
(assert (= (fp.rem dividend (_ +oo 32 200)) dividend))
(assert (= (fp.rem dividend (_ -oo 32 200)) dividend))
(assert (= (fp.rem (_ +zero 32 200) dividend) (_ +zero 32 200)))
(assert (= (fp.rem (_ -zero 32 200) dividend) (_ -zero 32 200)))
(assert (fp.isNaN (fp.rem dividend (_ +zero 32 200))))
(assert (fp.isNaN (fp.rem (_ NaN 32 200) dividend)))
(assert (fp.isNaN (fp.rem (_ +oo 32 200) dividend)))
(check-sat)
