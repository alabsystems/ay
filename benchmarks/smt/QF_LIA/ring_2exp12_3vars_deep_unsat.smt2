; Ring arithmetic modulo 2^12 = 4096, 3 variables, deep carry chain, expected UNSAT
; Models 12-bit ring arithmetic. Larger modulus makes coefficient GCD analysis harder.
;
; x + y = 4096*c1 + s1
; s1 * 3 = 4096*c2 + s2  (multiply ring result by 3)
; s2 + z = 4096*c3 + s3
; s3 = 1000
; x = 2048, y = 2048, z = 500
;
; x + y = 4096, so c1=1, s1=0.
; s1*3 = 0, so c2=0, s2=0.
; s2 + z = 500, so c3=0, s3=500.
; But s3 = 1000 required. UNSAT.
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const s1 Int)
(declare-const s2 Int)
(declare-const s3 Int)
(declare-const c1 Int)
(declare-const c2 Int)
(declare-const c3 Int)

; 12-bit bounds
(assert (>= x 0)) (assert (<= x 4095))
(assert (>= y 0)) (assert (<= y 4095))
(assert (>= z 0)) (assert (<= z 4095))
(assert (>= s1 0)) (assert (<= s1 4095))
(assert (>= s2 0)) (assert (<= s2 4095))
(assert (>= s3 0)) (assert (<= s3 4095))
(assert (>= c1 0)) (assert (<= c1 2))
(assert (>= c2 0)) (assert (<= c2 2))
(assert (>= c3 0)) (assert (<= c3 2))

; Carry chain with multiplication
(assert (= (+ x y) (+ (* 4096 c1) s1)))
(assert (= (* 3 s1) (+ (* 4096 c2) s2)))
(assert (= (+ s2 z) (+ (* 4096 c3) s3)))

; Fixed variable values
(assert (= x 2048))
(assert (= y 2048))
(assert (= z 500))

; Target ring result (contradicts the computation)
(assert (= s3 1000))

(check-sat)
