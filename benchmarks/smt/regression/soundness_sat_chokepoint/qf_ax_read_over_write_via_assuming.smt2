(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-info :source |
  SAT-emission-chokepoint soundness fence (#sat-chokepoint).

  A wrong array model driven through check-sat-assuming. Before the single
  emit_sat_verdict funnel, check-sat-assuming emitted SAT through
  finalize_sat_model_validation (the STRICT gate) ONLY and NEVER ran the
  INDEPENDENT model-check gate, so a wrong array model could bypass the
  soundness kernel via this path.

  b = store(store(a, i, v), j, w) with i != j, so by read-over-write
  select(b, i) = v.  The assumption asserts select(b, i) != v, which is
  UNSAT.  z3: unsat.  AY must answer unsat or unknown, NEVER sat.
|)
(set-logic QF_AX)
(declare-sort I 0)
(declare-sort E 0)
(declare-fun a () (Array I E))
(declare-fun b () (Array I E))
(declare-fun i () I)
(declare-fun j () I)
(declare-fun v () E)
(declare-fun w () E)
(declare-fun e1 () E)
(assert (= b (store (store a i v) j w)))
(assert (not (= i j)))
(assert (= e1 (select b i)))
(check-sat-assuming ((not (= e1 v))))
