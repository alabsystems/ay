; 2026-09-23 differential hunt, D4-a (arrays/witness/w2_const/w2_min.smt2). z3 5.1.0: sat (its model re-checks sat).
; main f399eca07a answered unsat here; a sat file must never become unsat.
(set-logic QF_ALIA)
(declare-fun a0 () (Array Int Int))
(declare-fun i () Int)
(assert (= (store ((as const (Array Int Int)) 1) (+ i 1) 2) (store ((as const (Array Int Int)) 1) 1 (select (store a0 5 2) i))))
(check-sat)
