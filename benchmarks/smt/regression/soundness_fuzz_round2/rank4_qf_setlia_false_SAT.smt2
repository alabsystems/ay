(set-logic QF_SETLIA)
(assert (= (set.singleton 0) (set.singleton 1)))
(check-sat)
