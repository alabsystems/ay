; QF_SLIA FALSE-UNSAT witness — assertion-order permutation of
; falseunsat_indexof_substr_oob.smt2 that fired DETERMINISTICALLY at HEAD
; (the original ordering only fired on unlucky build fingerprints).
; Root cause (FIXED): check_extf_int_reductions resolved const_side (the bare
; Int var i) to a constant via its EQC merge (a branch decision i ~ 0) but the
; conflict explanation never included that merge reason — the blocking clause
; universalized a branch-local conflict (indexof reduces to -1 vs i=0) into a
; false UNSAT. Fix: add_term_resolution_explanation(const_side) at both
; conflict sites in extf_pass_int.rs. z3=sat, cvc5=sat.
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun s () String)(declare-fun t () String)(declare-fun u () String)
(declare-fun v () String)(declare-fun w () String)
(declare-fun i () Int)(declare-fun j () Int)(declare-fun k () Int)(declare-fun n () Int)(declare-fun m () Int)
(declare-fun p () Bool)(declare-fun q () Bool)(declare-fun r () Bool)
(assert (= i (str.indexof (str.substr (str.substr t 0 2) 3 1) (str.++ "" s v) 0)))
(assert (= s "b"))(assert (= u ""))(assert (= v "a"))(assert (= w "9"))
(assert (distinct (str.substr (str.at (str.substr "0" 3 -1) 4) 4 1) (str.replace s (str.at (str.substr u 2 2) i) (str.at (str.at w 0) n))))
(check-sat)