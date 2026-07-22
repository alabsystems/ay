; QF_SLIA FALSE-UNSAT (found by diff_fuzz). An Int var bound to str.indexof over
; out-of-range substr operands (= -1) feeds as a str.at index inside str.replace,
; all inside a top-level distinct over deeply-nested out-of-bounds str.substr/at
; terms (all reduce to ""). z3=sat; AY derives a spurious theory conflict -> unsat.
; int-returning-str-fn-bound-to-Int-var x multi-str.at-reduction family. VERY
; FRAGILE (declaration-count/ordering sensitive: term-interning effect). NOT fixed.
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun s () String)(declare-fun t () String)(declare-fun u () String)
(declare-fun v () String)(declare-fun w () String)
(declare-fun i () Int)(declare-fun j () Int)(declare-fun k () Int)(declare-fun n () Int)(declare-fun m () Int)
(declare-fun p () Bool)(declare-fun q () Bool)(declare-fun r () Bool)
(assert (= s "b"))(assert (= u ""))(assert (= v "a"))(assert (= w "9"))
(assert (= i (str.indexof (str.substr (str.substr t 0 2) 3 1) (str.++ "" s v) 0)))
(assert (distinct (str.substr (str.at (str.substr "0" 3 -1) 4) 4 1) (str.replace s (str.at (str.substr u 2 2) i) (str.at (str.at w 0) n))))
(check-sat)
