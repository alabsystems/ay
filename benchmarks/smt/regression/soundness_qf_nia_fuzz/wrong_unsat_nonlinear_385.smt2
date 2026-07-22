; QF_NIA WRONG-UNSAT (found by diff_fuzz QF_NIA seed=3 case 385). AY answers
; `unsat` (with an EMPTY unsat core) but the formula is SAT (z3=sat). This is a
; nonlinear-integer soundness bug: AY derives a false contradiction from a
; satisfiable constraint set. Distinct from wrong-SAT — a wrong-UNSAT means any
; emitted proof is INVALID. z3's satisfying model (verified by hand):
;   x=1, y=-2, z=-1, n=1, m=0, p=true, q=false, r=false, s=true
; (assertion #7 from the original fuzz witness is dropped here — not needed to
;  trigger the bug; dropping any of the remaining assertions flips AY to unknown.)
(set-info :status sat)
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const n Int)
(declare-const m Int)
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(declare-const s Bool)
(assert (and (<= -1 n) (<= n 2)))
(assert (and (<= 0 m) (<= m 0)))
(assert (and (not (distinct (ite s z m) (* 1 z x))) p))
(assert (distinct (* y z) (* x n) (* n z)))
(assert (or (< y (* y z n)) (ite (> (ite false y z) (* -2 n y)) (ite (not q) (> 2 y) (=> q false)) (not (not r)))))
(assert (< (* -1 x n) (* n m)))
(assert (< (+ (* z z) -1) (* n n)))
(check-sat)
