; False-UNSAT: store(store(a,i,v),j,x) = store(store(a,i,w),j,x) with v != w
; Expected: sat (model: i=j, any v!=w, any x — outer store at j overwrites inner at i)
; Minimal repro: when symbolic indices i,j can collide, the outer store at j masks
; the inner store at i. AY incorrectly returns UNSAT because the extensionality
; witness for the inner stores (store(a,i,v) vs store(a,i,w)) is not blocked by
; the outer store overwrite when i=j.
(set-logic QF_AUFLIA)
(set-info :status sat)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun v () Int)
(declare-fun w () Int)
(declare-fun x () Int)
(assert (not (= v w)))
(assert (= (store (store a i v) j x) (store (store a i w) j x)))
(check-sat)
(exit)
