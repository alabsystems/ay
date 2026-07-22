; Ring modular arithmetic: CRT-style cross-constraint reasoning needed.
; 3 variables, expected UNSAT.
;
; x ≡ 1 (mod 4)  -> x = 4a + 1
; x ≡ 2 (mod 6)  -> x = 6b + 2
; 0 <= x <= 255
;
; From CRT: x ≡ 1 (mod 4) and x ≡ 2 (mod 6).
; x = 4a + 1, so 4a + 1 ≡ 2 (mod 6) => 4a ≡ 1 (mod 6).
; gcd(4,6) = 2, and 2 does not divide 1. No solution. UNSAT.
;
; This requires cross-row accumulative GCD or CRT detection.
(set-logic QF_LIA)
(declare-const x Int)
(declare-const a Int)
(declare-const b Int)

; Bounds
(assert (>= x 0)) (assert (<= x 255))
(assert (>= a 0))
(assert (>= b 0))

; Modular constraints
(assert (= x (+ (* 4 a) 1)))
(assert (= x (+ (* 6 b) 2)))

(check-sat)
