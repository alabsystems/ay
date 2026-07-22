; Diamond pattern: a -store(i,v)-> b, a -store(j,w)-> c, b = c, i != j
; If b = c, then at index i: select(b,i) = v (ROW1), select(c,i) = select(a,i) (ROW2)
; So v = select(a,i). Similarly w = select(a,j).
; This is SAT as long as v and w are consistent with a.
; Expected: sat
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
(assert (= v (select a i)))
(assert (= w (select a j)))
(check-sat)
(exit)
