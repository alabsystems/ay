; CLASS A false-UNSAT (AY=unsat, z3=sat). = (not p), trivially SAT (p=false).
; AY drops the X-free residue conjunct `p` when deciding (not (exists X. (and A(X) p))),
; treating the existential as a tautology. Directly-written equivalent forall
; `(forall X. (not (and (<= 0 X)(<= X 4) p)))` is solved CORRECTLY (sat) — so the bug
; is the not-exists existential decision / QE path, not universal solving.
(set-logic LIA)
(declare-const p Bool)
(assert (not (exists ((X0 Int)) (and (<= 0 X0) (<= X0 4) p))))
(check-sat)
