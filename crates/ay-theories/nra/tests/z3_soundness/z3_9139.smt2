; Reproducer for Z3 issue #9139 — NRA soundness bug (CVC5 sat, Z3 unsat).
; Source: https://github.com/Z3Prover/z3/issues/9139
; Expected: sat (confirmed by cvc5). Original Z3 returned unsat.
(set-logic QF_NRA)
(declare-const b Real)
(assert (is_int (- (/ (/ (+ 3.0 b) (+ (- (- 3.0)) 2.0))
                      (/ (+ 3.0 b) (+ (- (- 3.0)) 2.0))) b)))
(assert (< (- 2.0) b))
(check-sat)
