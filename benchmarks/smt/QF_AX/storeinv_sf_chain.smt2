; Store inverse with store-forwarding chain
; If we write back what's there at 2 positions, the array is unchanged
; Expected: unsat
(set-logic QF_AX)
(set-info :status unsat)
(declare-sort Index 0)
(declare-sort Elem 0)
(declare-fun a () (Array Index Elem))
(declare-fun i () Index)
(declare-fun j () Index)
(assert (not (= i j)))
; Write back the original value at i, then at j
(define-fun a1 () (Array Index Elem) (store a i (select a i)))
(define-fun a2 () (Array Index Elem) (store a1 j (select a j)))
; This should be equal to a
(assert (not (= a2 a)))
(check-sat)
(exit)
