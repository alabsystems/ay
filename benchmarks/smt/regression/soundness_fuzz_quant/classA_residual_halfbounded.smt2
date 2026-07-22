; Class A residual (half-bounded, NOT finite-domain): (not (exists X. (and (<= X 4) p))).
; = (not p) → sat; AY=unsat. Unbounded-below X → not finite-expandable → the X-free
; residue drop persists. Only MINISCOPING fixes this (∃X.(A∧p) ≡ (∃X.A)∧p).
(set-logic LIA)
(declare-const p Bool)
(assert (not (exists ((X0 Int)) (and (<= X0 4) p))))
(check-sat)
