; Reproducer for Z3 issue #9293 — invalid model on select with nested arrays.
; Source: https://github.com/Z3Prover/z3/issues/9293
; Minimized: store-select on a nested array, where the outer select into a
; modified inner store must agree with the stored value. Expected: unsat.
(set-logic ALL)
(declare-fun outer () (Array Int (Array Int Int)))
(declare-fun inner () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun v () Int)
(assert (= (store outer i (store inner j v)) outer))
(assert (not (= (select (select outer i) j) v)))
(check-sat)
