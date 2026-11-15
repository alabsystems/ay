; 2026-09-29 arrays fix-up (session 5), fresh seed 2909 nestfin_2909_0018. z3 5.1.0: unsat.
; main 9ea9b8b5dd panicked in --z3-mode: bv_range (bv_finite_array.rs, the D9 dense-range
; rewrite) reached the Bool index `false` of the outer (Array Bool ..) and hit
; `unreachable!`. The default posture answers unsat.
(set-logic ALL)
(declare-fun m0 () (Array Bool (Array (_ BitVec 2) (_ BitVec 2))))
(declare-fun b0 () (Array (_ BitVec 2) (_ BitVec 2)))
(assert (= ((as const (Array (_ BitVec 2) (_ BitVec 2))) #b11) (store (select (store m0 true b0) true) #b11 #b00)))
(assert (distinct (store b0 #b01 #b00) (store (select (store m0 true b0) false) #b01 #b00) (store ((as const (Array (_ BitVec 2) (_ BitVec 2))) #b00) #b10 #b11) b0 (store (store (select m0 false) #b10 #b10) #b00 #b01)))
(assert (= (select (store b0 #b10 #b11) #b11) #b00))
(assert (not (= (select m0 true) (store b0 #b11 #b01))))
(check-sat)
