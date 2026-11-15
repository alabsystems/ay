; Copyright 2026 Andrew Yates
; SPDX-License-Identifier: Apache-2.0
; The unique pinned operands have remainder -1, so this claim is false.
(set-logic QF_FP)
(set-info :status unsat)
(declare-const dividend (_ FloatingPoint 8 200))
(declare-const divisor (_ FloatingPoint 8 200))
(assert (= dividend ((_ to_fp 8 200) RNE 5.0)))
(assert (= divisor ((_ to_fp 8 200) RNE 3.0)))
(assert (= (fp.rem dividend divisor) (_ +zero 8 200)))
(check-sat)
