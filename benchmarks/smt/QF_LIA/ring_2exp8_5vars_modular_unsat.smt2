; Ring arithmetic modulo 2^8 = 256, 5 variables, modular constraints, expected UNSAT
; This benchmark exercises cross-row GCD/CRT reasoning.
;
; All variables in [0, 255]. The carry chain computes:
;   step1 = (a + b) mod 256
;   step2 = (step1 + c) mod 256
;   step3 = (step2 + d) mod 256
;   step4 = (step3 + e) mod 256
;
; The key constraint: each variable is forced to be even (a=2a', etc.)
; but the final ring result step4 must be odd (= 127).
;
; Since all inputs are even, the sum a+b+c+d+e is even,
; so (a+b+c+d+e) mod 256 is even. But step4 = 127 (odd). UNSAT.
(set-logic QF_LIA)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(declare-const e Int)
(declare-const a2 Int)
(declare-const b2 Int)
(declare-const c2 Int)
(declare-const d2 Int)
(declare-const e2 Int)
(declare-const s1 Int)
(declare-const s2 Int)
(declare-const s3 Int)
(declare-const s4 Int)
(declare-const k1 Int)
(declare-const k2 Int)
(declare-const k3 Int)
(declare-const k4 Int)

; 8-bit bounds
(assert (>= a 0)) (assert (<= a 255))
(assert (>= b 0)) (assert (<= b 255))
(assert (>= c 0)) (assert (<= c 255))
(assert (>= d 0)) (assert (<= d 255))
(assert (>= e 0)) (assert (<= e 255))
(assert (>= s1 0)) (assert (<= s1 255))
(assert (>= s2 0)) (assert (<= s2 255))
(assert (>= s3 0)) (assert (<= s3 255))
(assert (>= s4 0)) (assert (<= s4 255))

; Each input is even
(assert (= a (* 2 a2)))
(assert (= b (* 2 b2)))
(assert (= c (* 2 c2)))
(assert (= d (* 2 d2)))
(assert (= e (* 2 e2)))
(assert (>= a2 0)) (assert (<= a2 127))
(assert (>= b2 0)) (assert (<= b2 127))
(assert (>= c2 0)) (assert (<= c2 127))
(assert (>= d2 0)) (assert (<= d2 127))
(assert (>= e2 0)) (assert (<= e2 127))

; Carry chain
(assert (= (+ a b) (+ (* 256 k1) s1)))
(assert (= (+ s1 c) (+ (* 256 k2) s2)))
(assert (= (+ s2 d) (+ (* 256 k3) s3)))
(assert (= (+ s3 e) (+ (* 256 k4) s4)))
(assert (>= k1 0)) (assert (<= k1 1))
(assert (>= k2 0)) (assert (<= k2 1))
(assert (>= k3 0)) (assert (<= k3 1))
(assert (>= k4 0)) (assert (<= k4 1))

; Final ring result is odd (contradiction: even inputs => even sum mod 256)
(assert (= s4 127))

(check-sat)
