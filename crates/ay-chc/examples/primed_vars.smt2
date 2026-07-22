; Example with primed variables (transition system style)
; x' represents the next-state value of x

(set-logic HORN)

; Declare predicate
(declare-rel Inv (Int))

; Declare variables (both current and next-state)
(declare-var x Int)
(declare-var x' Int)

; Initial state
(rule (=> (= x 0) (Inv x)))

; Transition relation: x' = x + 1 /\ x < 5 => Inv(x) => Inv(x')
(rule (=> (and (Inv x) (= x' (+ x 1)) (< x 5)) (Inv x')))

; Safety: x <= 5
(query (and (Inv x) (> x 5)))
