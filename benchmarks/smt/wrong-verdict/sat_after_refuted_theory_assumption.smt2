;; D10(a), NIA-soundness verifier round 2: an assumption unsatisfiable on its
;; own stayed asserted for the plain check (--z3-mode unsat). z3 5.1.0: unsat sat.
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (>= (* y y x) 3))
(check-sat-assuming ((= (mod x 6) 6)))
(check-sat)
