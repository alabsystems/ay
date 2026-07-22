(set-logic QF_ALIA)
; Store at i, select at j (i != j): value should be unchanged. UNSAT
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(assert (not (= i j)))
(assert (not (= (select (store a i 42) j) (select a j))))
(check-sat)
(exit)
