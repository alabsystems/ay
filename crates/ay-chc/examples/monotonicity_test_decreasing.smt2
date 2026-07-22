; Monotonicity test for init-bound weakening guard (#937) - DECREASING case
;
; This system tests that PDR handles monotonically-decreasing variables correctly.
; x starts at 5, decreases by 1 each step down to 0, then stops.
;
; System behavior:
; - Init: x = 5
; - Transition: if x > 0 then x' = x - 1 else x' = x
; - Query: x < 0 (can never happen - SAFE)
;
; This tests that the solver correctly identifies x as non-increasing and
; can use that information for generalization. The key invariant is x >= 0.
;
; Expected result: Safe
; Valid invariant: x >= 0 AND x <= 5

(set-logic HORN)

(declare-rel Inv (Int))

(declare-var x Int)
(declare-var xp Int)

; Initial state: x = 5
(rule (=> (= x 5) (Inv x)))

; Transition: decrement while x > 0, then stay at 0
(rule (=> (and (Inv x) (> x 0) (= xp (- x 1))) (Inv xp)))
(rule (=> (and (Inv x) (<= x 0) (= xp x)) (Inv xp)))

; Safety: query whether we can reach x < 0 while satisfying Inv
(query (and (Inv x) (< x 0)))
