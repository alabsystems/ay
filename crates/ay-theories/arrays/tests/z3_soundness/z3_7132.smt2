; Reproducer for Z3 issue #7132 — unsound ABV model.
; Source: https://github.com/Z3Prover/z3/issues/7132
; Minimized core: two arrays forced to differ on an index despite equality of
; their stores. Expected: unsat.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun i () (_ BitVec 8))
(declare-fun v () (_ BitVec 8))
(assert (= (store a i v) (store b i v)))
(assert (= (select a i) v))
(assert (= (select b i) v))
(assert (not (= (select a #x00) (select b #x00))))
(assert (not (= i #x00)))
(check-sat)
