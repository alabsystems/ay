; Two different stores to same base at different indices are both preserved
; b = store(a, i, v1), c = store(a, j, v2), i != j
; select(b, j) = select(a, j) by ROW2
; This is SAT: both stores can coexist
; Expected: sat
(set-logic QF_AX)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a () (Array Index Element))
(declare-fun b () (Array Index Element))
(declare-fun c () (Array Index Element))
(declare-fun i () Index)
(declare-fun j () Index)
(declare-fun v1 () Element)
(declare-fun v2 () Element)
(assert (= b (store a i v1)))
(assert (= c (store a j v2)))
(assert (not (= i j)))
(assert (= (select b j) (select a j)))
(assert (= (select c i) (select a i)))
(check-sat)
(exit)
