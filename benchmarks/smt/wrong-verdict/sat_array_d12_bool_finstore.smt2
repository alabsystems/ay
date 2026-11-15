; 2026-09-23 differential hunt, D12 = D4-b (arrays/witness/w3_finstore/min.smt2). z3 5.1.0: sat (its model re-checks sat).
; main f399eca07a answered unsat here; a sat file must never become unsat.
(set-logic ALL)
(declare-fun a1 () (Array Bool Bool))
(declare-fun a2 () (Array Bool Bool))
(declare-fun a3 () (Array Bool Bool))
(declare-fun x0 () Bool)
(declare-fun x1 () Bool)
(declare-fun v0 () Bool)
(assert (= (store (store a2 false true) true true) (store ((as const (Array Bool Bool)) true) x1 true)))
(assert (or (= (store (store (store a3 true false) x0 v0) x0 true) a2) (= a2 (store (store (store a3 x1 true) x0 true) true true))))
(assert (= a1 (store (store ((as const (Array Bool Bool)) false) true true) x0 false)))
(assert (= (select (store (store a2 true false) false false) true) (select (store (store (store (store a3 false true) true v0) x1 false) x1 true) x0)))
(check-sat)
