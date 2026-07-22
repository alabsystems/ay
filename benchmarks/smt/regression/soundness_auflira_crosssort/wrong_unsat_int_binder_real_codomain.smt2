; AUFLIRA WRONG-UNSAT (discovered during the MBQI finite-table-certificate work,
; confirmed pre-existing on clean HEAD). AY answered `unsat` on this SAT formula
; (z3=sat: f := lambda x. ite(x=3, 5.0, 0.0)). Root cause: the quantifier loop fed
; a satisfiable GROUND conjunction {f(3)=5.0} u {f(c)>=0.0} to the ground lane,
; where propagate_tight_bound_equalities (ay-core/src/lib.rs) grouped tight-bound
; terms BY NUMERIC VALUE ONLY, sort-blind - pairing the Real-sorted f(3) (value 5)
; with the INT constant term 5, emitting an ill-sorted Nelson-Oppen equality; EUF
; then saw Int(5)/Rational(5) as distinct constants -> "constant conflict" whose
; only reason was the asserted TRUE fact (= (f 3) 5.0) -> false unit conflict ->
; wrong unsat. Same bug family as #7451 (String=Int cross-sort, same helper).
; Fixed with sort-agreement guards (source + LIA/LRA mirrors + EUF sink).
; Sound outcomes: sat (needs Real-codomain MBQI cert, a completeness follow-up)
; or unknown. NEVER unsat.
(set-info :status sat)
(set-logic AUFLIRA)
(declare-fun f (Int) Real)
(assert (forall ((x Int)) (>= (f x) 0.0)))
(assert (= (f 3) 5.0))
(check-sat)
