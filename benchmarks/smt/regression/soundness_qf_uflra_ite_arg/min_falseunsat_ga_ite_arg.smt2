; QF_UFLRA false-UNSAT (combined EUF+LRA): a Real variable z that is ite-defined
; in LRA and the ARGUMENT of a UF app ga(z) in EUF. AY returns `unsat`;
; z3 returns `sat` (trivially: p=true => z=-3, ga(-3)=5; or p=false => z=-2).
; Minimized (M16) from scripts/diff_fuzz.py (QF_UFLRA seed 2). The soundness
; invariant: AY must NEVER answer `unsat` here (`sat` is correct; `unknown` is
; an acceptable sound fallback). NOTE: M13 shows ga((ite ...)) inlined is fine;
; M12 (no UF) is fine; M11 (Int analog) is fine — the bug is the SHARED Real var
; between the ite-equality (LRA) and the UF arg (EUF).
(set-logic QF_UFLRA)
(declare-const z Real)
(declare-fun ga (Real) Real)
(declare-const p Bool)
(assert (= (ga z) 5))
(assert (= z (ite p (- 3) (- 2))))
(check-sat)
