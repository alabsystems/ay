; ay #3073: (distinct (mod x 3) (mod (+ x 1) 3)) /\ 0 <= x < 10, sat at x = 0.
; z4 9208a5cf (reverted by 7e0b77d75e) answered it UNSAT through ay-chc's
; SmtContext, and #3073 blamed Gomory after a cube test. Rebuilt at 9208a5cf
; (2026-11-08) the UNSAT persists with the cube test disabled: a new slack row
; was written over its expression's basic variables, and a later pivot left
; two rows owning one basic variable. Slack rows are substituted over
; non-basic variables since #4842 (`get_or_create_slack`). Must never be UNSAT.
(set-logic QF_LIA)
(set-info :status sat)
(declare-const x Int)
(assert (distinct (mod x 3) (mod (+ x 1) 3)))
(assert (>= x 0))
(assert (< x 10))
(check-sat)
