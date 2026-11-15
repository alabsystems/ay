; Copyright 2026 Andrew Yates
; SPDX-License-Identifier: Apache-2.0
; SB200 remainder with a non-power-of-two divisor and authored operands.
(set-logic QF_FP)
(set-info :status sat)
(declare-const dividend (_ FloatingPoint 8 200))
(declare-const divisor (_ FloatingPoint 8 200))
(assert (= dividend ((_ to_fp 8 200) RNE 5.0)))
(assert (= divisor ((_ to_fp 8 200) RNE 3.0)))
(assert (= (fp.rem dividend divisor) ((_ to_fp 8 200) RNE (- 1.0))))
(check-sat)
