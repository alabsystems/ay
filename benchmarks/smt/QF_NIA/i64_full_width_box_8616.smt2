; Regression: a FULL-WIDTH 64-bit integer box reaching NIA bounded enumeration.
;
; `x, y in [i64::MIN, i64::MAX]` is exactly the box model-checker-consumer emits for a 64-bit
; signed-overflow obligation. Phase 3 of `try_bounded_enumeration` computed the
; per-variable range as `hi - lo + 1` in `i64`, which overflows on this box:
; `ay` panicked at crates/ay-theories/nia/src/bounded_enum.rs:264:25 with
; "attempt to subtract with overflow" and published `unknown (:reason-unknown
; "internal solver error")`. Measured 10 times while compiler_consumer verified
; library/core (core::num::nonzero::NonZero::<i64>::unchecked_mul and
; NonZero::<isize>::unchecked_mul).
;
; The box is astronomically past MAX_ENUM_DOMAIN, so enumeration must simply
; DECLINE. Satisfiable (x = 6, y = 1), so `unsat` here would be a wrong answer.
; status: sat
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (>= x (- 9223372036854775808)))
(assert (<= x 9223372036854775807))
(assert (>= y (- 9223372036854775808)))
(assert (<= y 9223372036854775807))
(assert (> (* x y) 5))
(check-sat)
