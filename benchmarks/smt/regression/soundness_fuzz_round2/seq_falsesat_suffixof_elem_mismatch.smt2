; AY=sat z3=unsat (SOUNDNESS CONFLICT) logic=QF_SLIA
(set-logic QF_SLIA)
(declare-fun v1 () (Seq Int))
(declare-fun v2 () (Seq Int))
(declare-fun v3 () (Seq Int))
(assert (= v1 (seq.unit 1)))
(assert (= v2 (seq.++ (seq.unit -1) (seq.unit -1))))
(assert (seq.suffixof v2 (seq.++ v3 v1)))
(check-sat)
