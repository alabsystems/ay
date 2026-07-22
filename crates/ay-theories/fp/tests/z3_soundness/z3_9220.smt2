; Z3 issue #9220 — push/pop scopes affect later proof performance.
; Source: https://github.com/Z3Prover/z3/issues/9220
;
; Minimized SMT-LIB proxy for the bug0.cpp reproducer (which is pure C++
; API). Pattern: accumulate assertions under push; the inner (check-sat)
; inside the nested scope should return unsat, and after popping back to
; the outer scope, a second (check-sat) should not be influenced by clauses
; learned inside the inner scope.
;
; Expected: first check-sat = unsat, second check-sat = sat.
; Regression guard: both answers must match, regardless of whether
; push/pop leaks learned clauses.
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= y (* 2 x)))
(push)
(assert (> x 0))
(assert (< x 1))
(check-sat)
(pop)
(assert (>= x 0))
(check-sat)
