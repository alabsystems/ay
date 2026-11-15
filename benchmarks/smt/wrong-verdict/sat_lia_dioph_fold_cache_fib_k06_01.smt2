; Satisfiable QF_LIA problem on which AY main (build 10503 .. 8b71d73999)
; answers `unsat` in both postures (default and --z3-mode). z3 5.1.0: sat.
; Planted model: x = -7, y = 13, z = 19.
;
; D2 of the 2026-09-23 hunt (linear/wit/fib_k06_01, generator gen_fib.py).
; Mechanism: the Diophantine solve folds a variable pinned by a pair of
; branch-and-bound atoms (x >= 3, x <= 3) into the equation constant; the
; folded system 13y + 5z = 54 gives z = 3 (mod 13). The substitution and
; modulus caches were keyed on the EQUALITY set alone and kept across the pop
; that retracted the pin (#C8), so the modular check later read z = 3 (mod 13)
; against 18 <= z <= 20 and reported every asserted literal as a conflict.
; Fixed by keying the caches on the folded bounds too
; (ay-lia/src/dioph_cache.rs). `sat` or `unknown` is acceptable; `unsat` is
; the regression.
(set-logic QF_LIA)
(set-info :status sat)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (= (+ (* 21 x) (* 13 y) (* 5 z)) 117))
(assert (<= 18 z))
(assert (<= z 20))
(check-sat)
