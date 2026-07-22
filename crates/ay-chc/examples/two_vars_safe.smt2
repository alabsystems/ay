; Two-variable system with composed invariant
; Two separate counters: x and y
; Invariant: x + y <= 10
; This system is SAFE

(set-logic HORN)

; Declare predicates - tracking x and y together
(declare-rel Inv (Int Int))

; Declare variables
(declare-var x Int)
(declare-var y Int)

; Initial state: x = 0 /\ y = 0 => Inv(x, y)
(rule (=> (and (= x 0) (= y 0)) (Inv x y)))

; Transition 1: Inv(x, y) /\ x < 5 => Inv(x+1, y)
(rule (=> (and (Inv x y) (< x 5)) (Inv (+ x 1) y)))

; Transition 2: Inv(x, y) /\ y < 5 => Inv(x, y+1)
(rule (=> (and (Inv x y) (< y 5)) (Inv x (+ y 1))))

; Safety property: Inv(x, y) /\ x + y > 10 => false
(query (and (Inv x y) (> (+ x y) 10)))
