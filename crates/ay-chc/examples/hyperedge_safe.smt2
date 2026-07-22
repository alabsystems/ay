; Hyperedge CHC example: Clause with multiple body predicates
;
; This demonstrates hyperedges (non-linear clauses) where a clause body
; references multiple predicates. Mixed summaries are needed to handle this.
;
; System:
; - P(x) tracks counter starting at 0, incrementing while x < 5
; - Q(y) tracks counter starting at 0, incrementing while y < 3
; - R(x, y) is reached when P(x) and Q(y) both hold
;
; Safety: R(x, y) => x + y <= 8
; This is SAFE because max(x) = 5, max(y) = 3, so x + y <= 8

(set-logic HORN)

; Declare predicates
(declare-rel P (Int))
(declare-rel Q (Int))
(declare-rel R (Int Int))

; Declare variables
(declare-var x Int)
(declare-var y Int)

; P system: x starts at 0, increments while x < 5
(rule (=> (= x 0) (P x)))
(rule (=> (and (P x) (< x 5)) (P (+ x 1))))

; Q system: y starts at 0, increments while y < 3
(rule (=> (= y 0) (Q y)))
(rule (=> (and (Q y) (< y 3)) (Q (+ y 1))))

; HYPEREDGE: R is reached when both P(x) and Q(y) hold
; This clause has TWO body predicates: P(x) and Q(y)
(rule (=> (and (P x) (Q y)) (R x y)))

; Safety property: x + y <= 8 when R(x, y) holds
(query (and (R x y) (> (+ x y) 8)))
