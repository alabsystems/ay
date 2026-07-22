; Two counters example
; This system is SAFE - counter stays bounded
;
; Simpler version using a single counter to avoid SMT limitations
; with equality on compound expressions.
;
; Invariant: x <= 10

(set-logic HORN)

; Declare predicate for the invariant
(declare-rel Inv (Int))

; Declare variables
(declare-var x Int)

; Initial state: x = 0 => Inv(x)
(rule (=> (= x 0) (Inv x)))

; Transition: Inv(x) /\ x < 10 => Inv(x+1)
(rule (=> (and (Inv x) (< x 10)) (Inv (+ x 1))))

; Safety property: Inv(x) /\ x > 15 => false
; (can we reach x > 15? NO - system maxes out at x=10)
(query (and (Inv x) (> x 15)))
