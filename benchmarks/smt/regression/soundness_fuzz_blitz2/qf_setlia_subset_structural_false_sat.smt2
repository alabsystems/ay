(set-logic QF_SETLIA)
(assert (not (set.subset (set.singleton 1) (set.insert 0 (set.singleton 1)))))
(check-sat)
