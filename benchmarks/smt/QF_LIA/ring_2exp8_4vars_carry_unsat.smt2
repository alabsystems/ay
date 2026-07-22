; Ring arithmetic modulo 2^8 = 256, 4 variables, carry chain, expected UNSAT
; Models 8-bit unsigned addition with overflow wrapping.
;
; Variables a, b, c, d in [0, 255] (8-bit unsigned).
; Sum: a + b + c + d = 300 (integer sum)
; Ring constraint: ((a + b) mod 256 + c) mod 256 + d) mod 256 = 100
;
; True ring sum = (a+b+c+d) mod 256 = 300 mod 256 = 44.
; But ring constraint says result = 100. UNSAT.
(set-logic QF_LIA)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(declare-const s1 Int)
(declare-const s2 Int)
(declare-const s3 Int)
(declare-const c1 Int)
(declare-const c2 Int)
(declare-const c3 Int)

; 8-bit bounds
(assert (>= a 0)) (assert (<= a 255))
(assert (>= b 0)) (assert (<= b 255))
(assert (>= c 0)) (assert (<= c 255))
(assert (>= d 0)) (assert (<= d 255))
(assert (>= s1 0)) (assert (<= s1 255))
(assert (>= s2 0)) (assert (<= s2 255))
(assert (>= s3 0)) (assert (<= s3 255))
(assert (>= c1 0)) (assert (<= c1 1))
(assert (>= c2 0)) (assert (<= c2 1))
(assert (>= c3 0)) (assert (<= c3 1))

; Carry chain
(assert (= (+ a b) (+ (* 256 c1) s1)))
(assert (= (+ s1 c) (+ (* 256 c2) s2)))
(assert (= (+ s2 d) (+ (* 256 c3) s3)))

; Integer sum constraint
(assert (= (+ a b c d) 300))

; Ring result constraint (contradicts integer sum mod 256 = 44)
(assert (= s3 100))

(check-sat)
