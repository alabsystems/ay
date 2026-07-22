; Mimics SMT-LIB storecomm_t1_np_sf_ai benchmark pattern
; Two arrays built from same base with same 3 stores in different order
; Store-forwarding: reads happen from the constructed arrays
; Expected: unsat
(set-logic QF_AX)
(set-info :status unsat)
(declare-sort Index 0)
(declare-sort Elem 0)
(declare-fun a0 () (Array Index Elem))
(declare-fun i0 () Index)
(declare-fun i1 () Index)
(declare-fun i2 () Index)
(declare-fun e0 () Elem)
(declare-fun e1 () Elem)
(declare-fun e2 () Elem)

; All indices pairwise distinct
(assert (distinct i0 i1 i2))

; Forward order: store i0, i1, i2
(define-fun fwd () (Array Index Elem) (store (store (store a0 i0 e0) i1 e1) i2 e2))
; Reverse order: store i2, i1, i0
(define-fun rev () (Array Index Elem) (store (store (store a0 i2 e2) i1 e1) i0 e0))

; Store-forwarding reads at each stored index:
; Read from fwd and rev at i0 -- both should be e0
(assert (not (= (select fwd i0) (select rev i0))))
(check-sat)
(exit)
