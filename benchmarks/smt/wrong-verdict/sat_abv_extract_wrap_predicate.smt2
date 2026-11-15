; D9 (2026-09-23 arrays + BV hunts): the read index is every byte, not only
; #xff. main f399eca07a answered unsat under --z3-mode (the dense-initializer
; rewrite runs only when proofs are off).
(set-logic QF_ABV)
(declare-fun t () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun y () (_ BitVec 8))
(assert (= (select t #xff) #x00))
(assert (not (= (select t ((_ extract 7 0) (bvadd #x0100 ((_ zero_extend 8) y)))) #x00)))
(check-sat)
