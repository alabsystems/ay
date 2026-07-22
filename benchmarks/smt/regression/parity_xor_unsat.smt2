; XOR/parity pattern - UNSAT case
; Contradictory parity constraints
(set-logic QF_LIA)
(declare-const a Int)
(declare-const b Int)

; Binary bounds
(assert (>= a 0)) (assert (<= a 1))
(assert (>= b 0)) (assert (<= b 1))

; Contradictory: sum must be both even and odd
(assert (= (mod (+ a b) 2) 0))  ; even
(assert (= (mod (+ a b) 2) 1))  ; odd

(check-sat)
; Expected: unsat
