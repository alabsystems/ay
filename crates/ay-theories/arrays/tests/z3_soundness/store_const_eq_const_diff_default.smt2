; Array-default congruence soundness reproducer (AY array-extensionality gap).
;
; A single store over a const-array can never equal a const-array with a
; DIFFERENT default value:
;
;     store((as const (Array Int Int)) 0, k, v) = (as const (Array Int Int)) 1
;
; The store fixes exactly one index (k); at every OTHER index the left side
; reads the base default 0 while the right side reads 1, so the two arrays
; disagree at infinitely many indices. Hence the equality is UNSAT.
;
; Why AY previously returned spurious `sat`: the single-Skolem extensionality
; witness can only FORCE agreement at one fresh index `d`, and the solver can
; always equate `d` with the store index `k` to dodge the read-over-const
; conflict — so the positive equality was never refuted. The fix adds the
; array-default congruence axiom `a = b => default(a) = default(b)`:
; `default(store(const 0, k, v))` folds to `default(const 0) = 0` and
; `default(const 1) = 1`, so the consequent `(= 0 1)` is `false` and the
; clause collapses to `(not (= lhs rhs))`, refuting the equality.
;
; z3 answer: unsat. Expected AY answer: unsat.
(set-logic QF_ALIA)
(declare-fun k () Int)
(declare-fun v () Int)
(assert (= (store ((as const (Array Int Int)) 0) k v) ((as const (Array Int Int)) 1)))
(check-sat)
