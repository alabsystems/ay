; Monotonicity test for init-bound weakening guard (#937)
;
; This system tests that PDR handles monotonically-increasing variables correctly.
; x starts at 0, increases by 1 each step up to 5, then stops.
;
; System behavior:
; - Init: x = 0
; - Transition: if x < 5 then x' = x + 1 else x' = x
; - Query: x > 5 (can never happen - SAFE)
;
; This tests that the solver correctly identifies x as non-decreasing and
; can use that information for generalization. The key invariant is x <= 5.
;
; Expected result: Safe
; Valid invariant: x >= 0 AND x <= 5

(set-logic HORN)

(declare-rel Inv (Int))

(declare-var x Int)
(declare-var xp Int)

; Initial state: x = 0
(rule (=> (= x 0) (Inv x)))

; Transition: increment while x < 5, then stay at 5
(rule (=> (and (Inv x) (< x 5) (= xp (+ x 1))) (Inv xp)))
(rule (=> (and (Inv x) (>= x 5) (= xp x)) (Inv xp)))

; Safety: query whether we can reach x > 5 while satisfying Inv
(query (and (Inv x) (> x 5)))
