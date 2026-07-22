; Ring arithmetic modulo 2^4 = 16, 3 variables, 0 if-then-else, expected UNSAT
; Models bounded integer computation in ring Z_{16}.
; Variables x, y, z are in [0, 15] (4-bit unsigned).
; Carry variables model overflow wrapping.
;
; Constraint system:
;   x + y = 16*c1 + s1  (s1 = (x+y) mod 16)
;   s1 + z = 16*c2 + s2  (s2 = (s1+z) mod 16)
;   s2 = 7              (final ring sum = 7)
;   x + y + z = 8       (but actual integer sum = 8)
;
; If x+y+z=8, then s2 = (x+y+z) mod 16 = 8 mod 16 = 8.
; But s2 = 7 contradicts this. UNSAT.
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const s1 Int)
(declare-const s2 Int)
(declare-const c1 Int)
(declare-const c2 Int)

; Variable bounds: 4-bit unsigned
(assert (>= x 0)) (assert (<= x 15))
(assert (>= y 0)) (assert (<= y 15))
(assert (>= z 0)) (assert (<= z 15))
(assert (>= s1 0)) (assert (<= s1 15))
(assert (>= s2 0)) (assert (<= s2 15))
(assert (>= c1 0)) (assert (<= c1 1))
(assert (>= c2 0)) (assert (<= c2 1))

; Ring addition with carries
(assert (= (+ x y) (+ (* 16 c1) s1)))
(assert (= (+ s1 z) (+ (* 16 c2) s2)))

; Contradictory requirements
(assert (= s2 7))
(assert (= (+ x y z) 8))

(check-sat)
