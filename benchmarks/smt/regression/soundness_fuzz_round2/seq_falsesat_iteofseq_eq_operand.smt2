; AY=sat z3=unsat (SOUNDNESS CONFLICT) logic=QF_S
(set-logic QF_S)
(declare-fun v1 () (Seq Bool))
(declare-fun v3 () (Seq Bool))
(declare-fun v5 () Bool)
(assert (= v1 (seq.++ (seq.unit false) (seq.unit false))))
(assert (= v3 (as seq.empty (Seq Bool))))
(assert (= (seq.at v1 0) (ite (seq.nth (seq.unit v5) -3) (seq.unit true) (seq.++ v3 (as seq.empty (Seq Bool)) (as seq.empty (Seq Bool))))))
(check-sat)
