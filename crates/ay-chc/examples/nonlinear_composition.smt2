; Non-linear CHC example: Composition of two systems
; P tracks counter x, Q tracks counter y
; Safety: P(x) /\ Q(y) /\ x + y > 15 => false
;
; This demonstrates non-linear clauses where the query body
; references multiple predicates.
;
; The system is SAFE: x maxes at 5, y maxes at 10, so x+y <= 15

(set-logic HORN)

; Declare predicates
(declare-rel P (Int))
(declare-rel Q (Int))

; Declare variables
(declare-var x Int)
(declare-var y Int)

; P system: x starts at 0, increments while x < 5
(rule (=> (= x 0) (P x)))
(rule (=> (and (P x) (< x 5)) (P (+ x 1))))

; Q system: y starts at 0, increments while y < 10
(rule (=> (= y 0) (Q y)))
(rule (=> (and (Q y) (< y 10)) (Q (+ y 1))))

; Safety property (NON-LINEAR): P(x) /\ Q(y) /\ x + y > 15 => false
; This is a non-linear query because it references two different predicates
(query (and (P x) (Q y) (> (+ x y) 15)))
