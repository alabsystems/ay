; Hyperedge CHC example: UNSAFE case with multiple body predicates
;
; System:
; - P(x) tracks counter starting at 0, incrementing while x < 10
; - Q(y) tracks counter starting at 0, incrementing while y < 10
; - R(x, y) is reached when P(x) and Q(y) both hold
;
; Safety: R(x, y) => x + y < 15
; This is UNSAFE because max(x) = 10, max(y) = 10, and 10 + 10 = 20 >= 15

(set-logic HORN)

; Declare predicates
(declare-rel P (Int))
(declare-rel Q (Int))
(declare-rel R (Int Int))

; Declare variables
(declare-var x Int)
(declare-var y Int)

; P system: x starts at 0, increments while x < 10
(rule (=> (= x 0) (P x)))
(rule (=> (and (P x) (< x 10)) (P (+ x 1))))

; Q system: y starts at 0, increments while y < 10
(rule (=> (= y 0) (Q y)))
(rule (=> (and (Q y) (< y 10)) (Q (+ y 1))))

; HYPEREDGE: R is reached when both P(x) and Q(y) hold
(rule (=> (and (P x) (Q y)) (R x y)))

; Safety property violated: x + y >= 15 when x=10, y=10
(query (and (R x y) (>= (+ x y) 15)))
