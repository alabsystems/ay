; Regression: an `i128::MIN` constant reaching the NIA clausal local-search lane.
;
; -170141183460469231731687303715884105728 is the lower bound of a 128-bit
; signed-overflow obligation, and it fits `Mono::coeff` — but its negation does
; not. `atom_lit` builds `lhs - rhs` through `neg_poly`, which negated the
; coefficient unchecked: `ay` panicked at
; crates/ay-theories/nia/src/local_search.rs:586:19 with "attempt to negate with
; overflow". Measured 3 times while compiler_consumer verified library/core
; (core::num::<impl i128>::unchecked_mul).
;
; The constant must survive normalization to reach `neg_poly`, which is why the
; atom is a `distinct` and not a strict inequality (integer `>` against a
; constant is normalized to `>= k+1`, and `i128::MIN + 1` negates fine).
;
; The Pythagorean part is what pushes the solve past every box-shaped fallback
; and into the local-search lane. Satisfiable — (x, y, z) = 33334 * (3, 4, 5)
; satisfies every conjunct — so `unsat` here would be a wrong answer.
; status: sat
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (> x 0))
(assert (> y 0))
(assert (> z 0))
(assert (= (+ (* x x) (* y y)) (* z z)))
(assert (> x 100000))
(assert (> (* x y z) 1000000000000))
(assert (distinct x (- 170141183460469231731687303715884105728)))
(check-sat)
