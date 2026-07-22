; Ring cascade: 5-stage carry chain with 2^16 modulus, expected UNSAT.
; Models a 5-stage adder pipeline modulo 65536.
; The constraint says the pipeline output must equal a value that's
; impossible given the input constraints.
;
; Each stage: output_i = (input_a_i + input_b_i) mod 65536
; Final constraint forces contradiction with input bounds.
(set-logic QF_LIA)
(declare-const x1 Int) (declare-const x2 Int) (declare-const x3 Int)
(declare-const x4 Int) (declare-const x5 Int)
(declare-const s1 Int) (declare-const s2 Int) (declare-const s3 Int)
(declare-const s4 Int)
(declare-const c1 Int) (declare-const c2 Int) (declare-const c3 Int)
(declare-const c4 Int)
(declare-const result Int)
(declare-const cfinal Int)

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
(assert (>= result 0)) (assert (<= result 65535))

; Carry bounds (0 or 1)
(assert (>= c1 0)) (assert (<= c1 1))
(assert (>= c2 0)) (assert (<= c2 1))
(assert (>= c3 0)) (assert (<= c3 1))
(assert (>= c4 0)) (assert (<= c4 1))
(assert (>= cfinal 0)) (assert (<= cfinal 1))

; Cascading ring addition: x1 + x2 + x3 + x4 + x5 (mod 65536)
(assert (= (+ x1 x2) (+ (* 65536 c1) s1)))
(assert (= (+ s1 x3) (+ (* 65536 c2) s2)))
(assert (= (+ s2 x4) (+ (* 65536 c3) s3)))
(assert (= (+ s3 x5) (+ (* 65536 c4) s4)))

; All inputs are multiples of 3
(declare-const m1 Int) (declare-const m2 Int) (declare-const m3 Int)
(declare-const m4 Int) (declare-const m5 Int)
(assert (= x1 (* 3 m1)))
(assert (= x2 (* 3 m2)))
(assert (= x3 (* 3 m3)))
(assert (= x4 (* 3 m4)))
(assert (= x5 (* 3 m5)))
(assert (>= m1 0)) (assert (>= m2 0)) (assert (>= m3 0))
(assert (>= m4 0)) (assert (>= m5 0))

; Inputs are "large" — between 40000 and 60000 each
(assert (>= x1 40000)) (assert (<= x1 60000))
(assert (>= x2 40000)) (assert (<= x2 60000))
(assert (>= x3 40000)) (assert (<= x3 60000))
(assert (>= x4 40000)) (assert (<= x4 60000))
(assert (>= x5 40000)) (assert (<= x5 60000))

; The ring sum s4 must be 1 (odd).
; Since each x_i ≡ 0 (mod 3), the true sum ≡ 0 (mod 3).
; True sum is in [200000, 300000].
; (true sum) mod 65536 = s4. We need s4 = 1.
; true_sum = 65536*total_carry + s4.
; true_sum ∈ [200000, 300000], s4 = 1.
; total_carry ∈ {3, 4} (since 65536*3 + 1 = 196609 < 200000, so carry >= 4:
;   65536*4 + 1 = 262145 ✓ (in range)
;   65536*3 + 1 = 196609 (< 200000, invalid)
;   65536*5 + 1 = 327681 (> 300000, invalid)
; So true_sum = 262145, which is 3*87381 + 2, not ≡ 0 mod 3. But we need ≡ 0 mod 3.
; 262145 mod 3 = 262145 - 87381*3 = 262145 - 262143 = 2. Not divisible by 3. UNSAT!
(assert (= s4 1))

(check-sat)
