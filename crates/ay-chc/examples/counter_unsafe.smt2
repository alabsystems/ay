; Unsafe counter example
; This system is UNSAFE - counter can become negative

(set-logic HORN)

; Declare predicate for the invariant
(declare-rel Inv (Int))

; Declare variables
(declare-var x Int)

; Initial state: x = 5 => Inv(x)
(rule (=> (= x 5) (Inv x)))

; Transition: Inv(x) => Inv(x - 1) (counts down, no lower bound!)
(rule (=> (Inv x) (Inv (- x 1))))

; Safety property: Inv(x) /\ x < 0 => false
; (can we reach a negative value? YES - system is unsafe)
(query (and (Inv x) (< x 0)))
