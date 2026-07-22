; Subtraction example - UNSAFE
; This system is UNSAFE - counter can become negative
;
; The program:
;   x = 3
;   while (true) { x -= 1 }
;   // no bound on x
;
; System is unsafe because x can become negative
; Counterexample: 3 -> 2 -> 1 -> 0 -> -1 (4 steps)

(set-logic HORN)

; Declare predicate: Inv(x)
(declare-rel Inv (Int))

; Declare variables
(declare-var x Int)

; Initial state: x = 3 => Inv(x)
(rule (=> (= x 3) (Inv x)))

; Transition: Inv(x) => Inv(x - 1)
(rule (=> (Inv x) (Inv (- x 1))))

; Safety property: Inv(x) /\ x < 0 => false
; (can we reach x < 0? YES - counterexample: 3, 2, 1, 0, -1)
(query (and (Inv x) (< x 0)))
