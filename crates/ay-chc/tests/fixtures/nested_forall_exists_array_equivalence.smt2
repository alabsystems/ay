; Independent reference for the parser's exact-rewrite admission boundary.
; The original forall-exists relation permits a nonconstant array: sat.
; Hoisting j before constant-array elimination strengthens it: unsat.
(set-logic ALL)
(declare-const a (Array (_ BitVec 1) Bool))
(assert (= (select a #b0) false))
(assert (= (select a #b1) true))
(push 1)
(assert (forall ((i (_ BitVec 1)))
  (exists ((j Bool)) (= (select a i) j))))
(check-sat)
(pop 1)
(push 1)
(assert (exists ((j Bool)) (= a ((as const (Array (_ BitVec 1) Bool)) j))))
(check-sat)
(pop 1)
