; Swap pattern: swap a[i] and a[j], then check a'[i] = a[j]
; Expected: unsat
(set-logic QF_AX)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a () (Array Index Element))
(declare-fun i () Index)
(declare-fun j () Index)
(assert (not (= i j)))
(assert (not (= (select (store (store a i (select a j)) j (select a i)) i) (select a j))))
(check-sat)
(exit)
