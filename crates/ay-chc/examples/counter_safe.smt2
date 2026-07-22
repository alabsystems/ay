; Simple safe counter example
; Invariant: 0 <= x <= 10
; This system is SAFE - counter never exceeds 10

(set-logic HORN)

; Declare predicate for the invariant
(declare-rel Inv (Int))

; Declare variables
(declare-var x Int)

; Initial state: x = 0 => Inv(x)
(rule (=> (= x 0) (Inv x)))

; Transition: Inv(x) /\ x < 10 => Inv(x + 1)
(rule (=> (and (Inv x) (< x 10)) (Inv (+ x 1))))

; Safety property: Inv(x) /\ x > 10 => false
; (query says: can we reach a state where x > 10 while satisfying Inv?)
(query (and (Inv x) (> x 10)))
