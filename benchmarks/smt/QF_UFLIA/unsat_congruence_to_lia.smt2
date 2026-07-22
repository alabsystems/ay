; Congruence-derived equality propagation test
;
; This tests whether EUF propagates congruence-derived equalities to LIA.
; From a=b, EUF derives f(a)=f(b) via congruence closure.
; LIA must know f(a)=f(b) to detect that f(a)<0 and f(a)>=0 is contradictory.
;
; Expected: unsat

(set-logic QF_UFLIA)
(declare-const a Int)
(declare-const b Int)
(declare-fun f (Int) Int)

; EUF: a = b implies f(a) = f(b) by congruence
(assert (= a b))

; LIA: f(a) < 0
(assert (< (f a) 0))

; LIA: f(b) >= 0, but f(b) = f(a) via congruence, so this contradicts above
(assert (>= (f b) 0))

(check-sat)
