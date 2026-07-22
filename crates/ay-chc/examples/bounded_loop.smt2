; Bounded loop example
; This system is SAFE - loop counter stays within bounds
;
; The program:
;   i = 0
;   while (i < n) { i++ }
;   assert(i <= n)
;
; Invariant: i <= n

(set-logic HORN)

; Declare predicate: Inv(i, n) - invariant for loop
(declare-rel Inv (Int Int))

; Declare variables
(declare-var i Int)
(declare-var n Int)

; Initial state: i = 0 /\ n >= 0 => Inv(i, n)
(rule (=> (and (= i 0) (>= n 0)) (Inv i n)))

; Loop iteration: Inv(i, n) /\ i < n => Inv(i+1, n)
(rule (=> (and (Inv i n) (< i n)) (Inv (+ i 1) n)))

; Safety: Inv(i, n) /\ i > n => false
; (can we exceed the bound? NO - system is safe)
(query (and (Inv i n) (> i n)))
