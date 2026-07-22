(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-info :source |
  SAT-emission-chokepoint soundness fence (#sat-chokepoint).

  A wrong array model driven through the OPTIMIZE path. Before the single
  emit_sat_verdict funnel, finalize_optimization emitted SAT through
  finalize_sat_model_validation (the STRICT gate) ONLY and NEVER ran the
  INDEPENDENT model-check gate, so a wrong optimized array model could bypass
  the soundness kernel via (maximize ...)/(assert-soft ...).

  x = select(store(a, i, 5), i) = 5 by read-over-store, but x is asserted
  distinct from 5, so the hard constraints are UNSAT.  z3: unsat.  With an
  objective present the executor routes SAT through finalize_optimization; AY
  must answer unsat or unknown, NEVER sat.
|)
(set-logic QF_ALIA)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun x () Int)
(assert (= x (select (store a i 5) i)))
(assert (distinct x 5))
(maximize x)
(check-sat)
