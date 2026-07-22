; Diamond conflict: b = store(a,i,v), c = store(a,j,w), b = c, i != j
; v must equal select(a,i) and w must equal select(a,j) for b = c.
; Asserting v != select(a,i) makes it UNSAT.
; Expected: unsat
(set-logic QF_AX)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a () (Array Index Element))
(declare-fun b () (Array Index Element))
(declare-fun c () (Array Index Element))
(declare-fun i () Index)
(declare-fun j () Index)
(declare-fun v () Element)
(declare-fun w () Element)
(assert (= b (store a i v)))
(assert (= c (store a j w)))
(assert (not (= i j)))
(assert (= b c))
(assert (not (= v (select a i))))
(check-sat)
(exit)
