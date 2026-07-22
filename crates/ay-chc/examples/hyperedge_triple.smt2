; Hyperedge CHC example: Three body predicates (triple hyperedge)
;
; System:
; - A(x) tracks counter starting at 0, incrementing while x < 2
; - B(y) tracks counter starting at 0, incrementing while y < 2
; - C(z) tracks counter starting at 0, incrementing while z < 2
; - R(x, y, z) is reached when A(x), B(y), and C(z) all hold
;
; Safety: R(x, y, z) => x + y + z <= 6
; This is SAFE because max(x) = 2, max(y) = 2, max(z) = 2, sum = 6

(set-logic HORN)

; Declare predicates
(declare-rel A (Int))
(declare-rel B (Int))
(declare-rel C (Int))
(declare-rel R (Int Int Int))

; Declare variables
(declare-var x Int)
(declare-var y Int)
(declare-var z Int)

; A system: x starts at 0, increments while x < 2
(rule (=> (= x 0) (A x)))
(rule (=> (and (A x) (< x 2)) (A (+ x 1))))

; B system: y starts at 0, increments while y < 2
(rule (=> (= y 0) (B y)))
(rule (=> (and (B y) (< y 2)) (B (+ y 1))))

; C system: z starts at 0, increments while z < 2
(rule (=> (= z 0) (C z)))
(rule (=> (and (C z) (< z 2)) (C (+ z 1))))

; TRIPLE HYPEREDGE: R is reached when A(x), B(y), and C(z) all hold
(rule (=> (and (and (A x) (B y)) (C z)) (R x y z)))

; Safety property: x + y + z <= 6 when R(x, y, z) holds
(query (and (R x y z) (> (+ (+ x y) z) 6)))
