; Z3 issue #7204 — Missing universes for UF sorts in model.
; Source: https://github.com/Z3Prover/z3/issues/7204
;
; Assertion: (not (x != x)) for uninterpreted-sort x : mysort.
; Z3 reports sat but the returned model has an empty sort list / empty
; universe for `mysort`, even though x takes a value there. This is a
; model-builder gap (the simplifier eliminates the assertion before model
; construction runs).
;
; Expected: sat with a non-empty universe for `mysort` (at least {x}).
; Soundness check: must not claim unsat; the formula (x = x) is trivially
; satisfiable for any mysort element.
(set-logic UF)
(declare-sort mysort 0)
(declare-const x mysort)
(assert (not (distinct x x)))
(check-sat)
