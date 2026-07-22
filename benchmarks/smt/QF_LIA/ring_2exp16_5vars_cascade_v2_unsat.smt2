; Same as ring_2exp16_5vars_cascade but divisibility expressed as mod constraints
; instead of explicit multiplier variables, to test whether the issue is
; frontend elimination of equality constraints.
(set-logic QF_LIA)
(declare-const x1 Int) (declare-const x2 Int) (declare-const x3 Int)
(declare-const x4 Int) (declare-const x5 Int)
(declare-const s1 Int) (declare-const s2 Int) (declare-const s3 Int)
(declare-const s4 Int)
(declare-const c1 Int) (declare-const c2 Int) (declare-const c3 Int)
(declare-const c4 Int)

; 16-bit bounds on all data variables
(assert (>= x1 0)) (assert (<= x1 65535))
(assert (>= x2 0)) (assert (<= x2 65535))
(assert (>= x3 0)) (assert (<= x3 65535))
(assert (>= x4 0)) (assert (<= x4 65535))
(assert (>= x5 0)) (assert (<= x5 65535))
(assert (>= s1 0)) (assert (<= s1 65535))
(assert (>= s2 0)) (assert (<= s2 65535))
(assert (>= s3 0)) (assert (<= s3 65535))
(assert (>= s4 0)) (assert (<= s4 65535))

; Carry bounds
(assert (>= c1 0)) (assert (<= c1 1))
(assert (>= c2 0)) (assert (<= c2 1))
(assert (>= c3 0)) (assert (<= c3 1))
(assert (>= c4 0)) (assert (<= c4 1))

; Cascading ring addition
(assert (= (+ x1 x2) (+ (* 65536 c1) s1)))
(assert (= (+ s1 x3) (+ (* 65536 c2) s2)))
(assert (= (+ s2 x4) (+ (* 65536 c3) s3)))
(assert (= (+ s3 x5) (+ (* 65536 c4) s4)))

; All inputs divisible by 3 (expressed via mod = 0)
(assert (= (mod x1 3) 0))
(assert (= (mod x2 3) 0))
(assert (= (mod x3 3) 0))
(assert (= (mod x4 3) 0))
(assert (= (mod x5 3) 0))

; Inputs between 40000 and 60000
(assert (>= x1 40000)) (assert (<= x1 60000))
(assert (>= x2 40000)) (assert (<= x2 60000))
(assert (>= x3 40000)) (assert (<= x3 60000))
(assert (>= x4 40000)) (assert (<= x4 60000))
(assert (>= x5 40000)) (assert (<= x5 60000))

; Ring sum must be 1 (contradicts: all inputs div by 3, so sum div by 3,
; so sum mod 65536 must be ≡ sum mod 3 ≡ 0 mod 3, but
; the only valid sum 262145 mod 65536 = 1, and 262145 mod 3 = 2 ≠ 0)
(assert (= s4 1))

(check-sat)
