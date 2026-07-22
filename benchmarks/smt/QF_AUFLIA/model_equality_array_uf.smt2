(set-logic QF_AUFLIA)
; Tests N-O model equality discovery with array+UF+LIA interaction.
; The solver must discover that f(x) = f(y) from equal model values,
; then propagate this through array reasoning.
(declare-fun f (Int) Int)
(declare-fun h (Int) Int)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun arr () (Array Int Int))
; x and y are equal modulo arithmetic
(assert (<= 0 x))
(assert (<= x 5))
(assert (= y (- (* 2 x) x)))  ; y = x
; Array is written at position f(x)
(assert (= arr (store ((as const (Array Int Int)) 0) (f x) (h x))))
; Reading at f(y) should get h(x) since f(x)=f(y) and h(x)=h(y)
; Assert that reading at f(y) gives something different from h(y)
(assert (not (= (select arr (f y)) (h y))))
(check-sat)
; Expected: unsat (since y=x, f(y)=f(x), h(y)=h(x), select at f(y) = h(x) = h(y))
(exit)
