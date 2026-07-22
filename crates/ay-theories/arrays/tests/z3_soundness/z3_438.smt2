; Reproducer for Z3 issue #438 — QF_ABV query hangs.
; Source: https://github.com/Z3Prover/z3/issues/438 (also tracked as AY #8140).
; Minimized hang-pattern scaffold. Expected: sat.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun i () (_ BitVec 8))
(assert (= (select (store a i #x01) i) #x01))
(check-sat)
