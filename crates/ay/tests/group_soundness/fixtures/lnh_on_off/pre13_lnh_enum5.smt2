; z3 5.1.0: sat
(set-logic QF_DT)
(set-info :status sat)
(declare-datatypes ((E 0)) (((A) (B) (C) (D) (E5))))
(declare-const e0 E)
(assert (or (= e0 A) (= e0 B) (= e0 C) (= e0 D) (= e0 E5)))
(assert ((_ is D) e0))
(check-sat)
