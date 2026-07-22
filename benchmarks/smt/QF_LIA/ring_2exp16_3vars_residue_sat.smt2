; Ring arithmetic modulo 2^16 = 65536, 3 variables, residue constraint, expected SAT.
; Exercises modular reasoning with large modulus and coprime divisibility.
;
; Variables x, y, z in [0, 65535] (16-bit unsigned).
; x = 3*p (x is divisible by 3)
; y = 5*q (y is divisible by 5)
; z = 7*r (z is divisible by 7)
; Ring sum: (x + y + z) mod 65536 = 1
;
; SAT witness: p=0, q=13106, r=1 => x=0, y=65530, z=7, s=1, k=1.
; Check: 0 + 65530 + 7 = 65537 = 65536*1 + 1.
;
; NOTE: The divisibility constraints use DIFFERENT primes (3,5,7), so
; x+y+z is NOT forced to 0 mod 105. For example y=65530 is 0 mod 5 but
; NOT 0 mod 3 or 7. Individual divisibility constraints on different
; variables don't combine via CRT to constrain the sum.
;
; AY currently returns false UNSAT on this benchmark (Gomory soundness
; bug with large-coefficient coprime systems). See #4830.
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const p Int)
(declare-const q Int)
(declare-const r Int)
(declare-const s Int)
(declare-const k Int)

; 16-bit bounds
(assert (>= x 0)) (assert (<= x 65535))
(assert (>= y 0)) (assert (<= y 65535))
(assert (>= z 0)) (assert (<= z 65535))
(assert (>= s 0)) (assert (<= s 65535))

; Divisibility constraints
(assert (= x (* 3 p)))
(assert (= y (* 5 q)))
(assert (= z (* 7 r)))
(assert (>= p 0))
(assert (>= q 0))
(assert (>= r 0))

; Ring addition
(assert (= (+ x y z) (+ (* 65536 k) s)))
(assert (>= k 0))

; Ring result
(assert (= s 1))

(check-sat)
