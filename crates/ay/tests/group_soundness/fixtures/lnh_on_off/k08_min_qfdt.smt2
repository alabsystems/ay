; z3 5.1.0: sat sat
(set-logic QF_DT)
(declare-datatypes ((N 0)) (((z) (s (p N)))))
(declare-const e N) (declare-const c0 N) (declare-const c1 N) (declare-const c2 N) (declare-const c3 N) (declare-const c4 N)
(push 1)
(assert (or (= e c0) (= e c1) (= e c2) (= e c3) (= e c4)))
(check-sat)
(assert (not (= e c0)))
(check-sat)
