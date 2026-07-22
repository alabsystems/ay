; Reproducer for Z3 issue #9140 — rem collapses to mod on zero divisor, false UNSAT.
; Source: https://github.com/Z3Prover/z3/issues/9140
; Expected: sat under SMT-LIB semantics (mod/rem by zero are under-specified, so
; (distinct (rem x 0) (mod x 0)) is satisfiable). Original Z3 reported unsat.
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= y 0))
(assert (distinct (rem x y) (mod x y)))
(check-sat)
