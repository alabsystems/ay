(set-logic QF_AUFLIA)
; Swap two array elements and verify
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(assert (not (= i j)))
(assert (= b (store (store a i (select a j)) j (select a i))))
; After swap: b[i] = a[j] and b[j] = a[i]
(assert (not (= (select b i) (select a j))))
(check-sat)
; Expected: unsat
(exit)
