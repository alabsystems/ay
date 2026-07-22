; CLASS B false-SAT (AY=sat, z3=unsat) — the dangerous direction.
; Refutation needs the DIAGONAL instance (X0=d, X1=d): p(d)=>s(d,d) = p(d); p(d) false
; => antecedent vacuous => LHS true => forces p(d)=true, contradicting (not (p d)).
; AY's e-matching instantiates at the ground pair (d,b) from (s d b) but never the
; diagonal (d,d). Incompleteness manifesting as UNSOUNDNESS — AY should return unknown,
; not sat. Safe fix: never answer sat from saturated-incomplete instantiation → unknown.
(set-logic UF)
(declare-sort U 0)
(declare-fun p (U) Bool)
(declare-fun s (U U) Bool)
(declare-const b U)
(declare-const d U)
(assert (not (p d)))
(assert (forall ((X0 U) (X1 U)) (= (=> (p X0) (s X0 X1)) (p X1))))
(assert (s d b))
(check-sat)
