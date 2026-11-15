; `(and (< x 3) (= x x))` elaborates to `(< x 3)`. The certificate once assumed
; that folded body, which the input does not assert, and `--strict-proofs`
; withheld `unsat`; it now assumes the conjunction as written and projects
; `(< x 3)` with `and_pos`, so every strict route answers `unsat`
; (`crates/ay/tests/group_soundness/strict_folded_premise.rs`).
(set-info :status unsat)
(set-logic ALL)
(declare-const x Int)
(assert (and (< x 3) (= x x)))
(assert (>= x 5))
(check-sat)
