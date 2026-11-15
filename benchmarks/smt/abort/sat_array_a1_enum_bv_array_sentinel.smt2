; 2026-09-23 differential hunt, A1 (arrays/witness/a1_panic/a1_min.smt2). z3 5.1.0: sat.
; main f399eca07a panicked (term store index out of bounds) in both postures.
(set-logic ALL)
(declare-datatypes ((E2 0)) (((e0) (e1))))
(declare-fun a0 () (Array (_ BitVec 2) E2))
(declare-fun a1 () (Array (_ BitVec 2) E2))
(declare-fun a2 () (Array (_ BitVec 2) E2))
(declare-fun x0 () (_ BitVec 2))
(assert (= (store (store (store (store a2 #b11 e0) #b01 e0) #b10 e1) #b00 e1) a2))
(assert (not (= (store (store (store (store a0 #b01 e0) #b10 e1) #b00 e0) #b11 e1) (store (store a1 #b10 e0) #b01 e1))))
(check-sat)
