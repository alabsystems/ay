(set-logic QF_AUFLIA)
; Non-convex theory combination: the N-O check loop must discover
; that g(a) = g(b) by inspecting LIA model values after the
; arithmetic solver assigns values consistent with the disjunction.
(declare-fun g (Int) Int)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun arr () (Array Int Int))
; a = 1 or a = 2
(assert (or (= a 1) (= a 2)))
; b = 1 or b = 2
(assert (or (= b 1) (= b 2)))
; g(a) + g(b) = 10
(assert (= (+ (g a) (g b)) 10))
; Array select at g(a) and g(b) must be equal
(assert (= (select arr (g a)) (select arr (g b))))
; But we assert they are different — this should be sat when g(a) != g(b)
; and unsat only if g(a) = g(b) in all models
; Since a can be 1 or 2 and b can be 1 or 2, when a != b, g(a) may != g(b)
; So this should be sat
(assert (not (= (g a) (g b))))
(check-sat)
; Expected: sat (e.g., a=1, b=2, g(1)=3, g(2)=7)
(exit)
