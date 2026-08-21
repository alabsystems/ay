; A top-level, conjunctive-position FP universal — the shape that would make
; `classify_authored_universal` return `universal = true` and put the lane on
; its universal branch. SAT: c = +oo satisfies it (NaN is excluded by the
; disjunct, and fp.leq x +oo holds for every non-NaN x).
(set-logic ALL)
(declare-fun c () Float32)
(assert (forall ((x Float32)) (or (fp.isNaN x) (fp.leq x c))))
(check-sat)
