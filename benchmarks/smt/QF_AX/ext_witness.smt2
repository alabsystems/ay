; Extensionality witness: a != b and select(a, k) = select(b, k) for all known k
; This tests whether the solver properly generates extensionality witnesses.
; With only one common index and arrays forced different, there must exist
; another index where they differ.
; Expected: sat
(set-logic QF_AX)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a () (Array Index Element))
(declare-fun b () (Array Index Element))
(declare-fun k () Index)
(assert (not (= a b)))
(assert (= (select a k) (select b k)))
(check-sat)
(exit)
