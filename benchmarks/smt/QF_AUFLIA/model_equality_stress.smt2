(set-logic QF_AUFLIA)
; This benchmark requires model-based theory combination (Nelson-Oppen).
; Two UF terms f(x) and f(y) have equal model values from LIA,
; but are not EUF-congruent until the N-O bridge speculates x=y.
(declare-fun f (Int) Int)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun a () (Array Int Int))
; Arithmetic constraints force x=y via shared reasoning
(assert (= (+ x 1) (+ y 1)))
; Array stores at f(x) and f(y) must agree
(assert (= (store a (f x) 0) (store a (f y) 0)))
; But f(x) != f(y) should be unsat because x=y implies f(x)=f(y) by congruence
(assert (not (= (f x) (f y))))
(check-sat)
; Expected: unsat
(exit)
