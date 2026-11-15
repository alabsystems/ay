;; D10(a), 2026-09-23 linear hunt M6: the second query was answered under the
;; first query's assumption (--z3-mode unsat). z3 5.1.0: sat sat.
(set-logic QF_LIRA)
(declare-fun r0 () Real)
(declare-fun p1 () Bool)
(assert (is_int r0))
(check-sat-assuming (p1))
(check-sat-assuming ((not p1)))
