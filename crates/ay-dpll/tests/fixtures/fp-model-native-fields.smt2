(set-logic QF_FP)
(declare-const x (_ FloatingPoint 63 129))
; 192 packed bits, with both the sign and all 128 stored fraction bits set.
(assert (= x (fp #b1 (_ bv4611686018427387903 63) (_ bv340282366920938463463374607431768211455 128))))
(check-sat)
