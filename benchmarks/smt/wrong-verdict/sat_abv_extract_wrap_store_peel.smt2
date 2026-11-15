; D9 (2026-09-23 BV hunt): the read index was "provably disjoint" from the
; store index #x05, so the store was peeled and the base read folded against
; T[#xff]. main f399eca07a answered unsat under --z3-mode.
(set-logic QF_ABV)
(declare-fun T () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun y () (_ BitVec 8))
(assert (= (select T #xff) #x00))
(assert (= (select (store T #x05 #x07) ((_ extract 7 0) (bvadd ((_ zero_extend 8) y) #x0100))) #x07))
(check-sat)
