; ay #3073: (distinct (mod x 3) (mod (+ x 1) 3)) /\ 0 <= x < 10, sat at x = 0.
; z4 9208a5cf (reverted by 7e0b77d75e) answered it UNSAT through ay-chc's
; SmtContext, and #3073 blamed Gomory after a cube test. Rebuilt at 9208a5cf
; (2026-11-08) the UNSAT persists with the cube test disabled: a new slack row
; was written over its expression's basic variables, and a later pivot left
; two rows owning one basic variable. Slack rows are substituted over
; non-basic variables since #4842 (`get_or_create_slack`). Must never be UNSAT.
; The mod elimination as ay-chc's eliminate_mod_recursive spells it.
(set-logic QF_LIA)
(set-info :status sat)
(declare-const x Int)
(declare-const q1 Int)
(declare-const r1 Int)
(declare-const q2 Int)
(declare-const r2 Int)
(assert (= x (+ (* 3 q1) r1)))
(assert (>= r1 0))
(assert (< r1 3))
(assert (= (+ x 1) (+ (* 3 q2) r2)))
(assert (>= r2 0))
(assert (< r2 3))
(assert (distinct r1 r2))
(assert (>= x 0))
(assert (< x 10))
(check-sat)
