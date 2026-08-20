; #cooper-period-blowup repro (evals/repros).
;
; WHAT BLOWS UP. Cooper's two instance sweeps materialise (1 + |B|) * delta
; interned terms explicitly. `delta` is the lcm of the divisors, and one of
; those divisors is `m` -- the lcm of the bound variable's COEFFICIENTS, which
; the unit-coefficient reduction mints as a fresh `m | v` literal. This file
; writes no `mod` atom at all, yet m = delta = 2^20, so the sweeps ask for
; ~2^20 terms. That is why selfcheck::DIVISOR_PERIOD_CAP does not catch it:
; that cap reads divisors from the INPUT literals, and here there are none.
;
; WHY `apply` AND NOT `check-sat`. A plain `(check-sat)` on this assertion does
; NOT reach Cooper -- the in-solve deep_qe site (check_sat.rs) is gated on
; `deep_qe_retry_armed`, which only the Unknown fallback sets, and the ordinary
; lanes decide such a file first. An earlier revision of this repro was a
; check-sat file and reproduced nothing: it answered unsat in 0.04s / 24 MB on
; the pre-fix binary, byte-identical to the fixed one. `(apply qe-light)` calls
; the eliminator directly and does fire, in default mode, with no flags.
;
; MEASURED, pre-fix (commit 85805c8957) vs post-fix, same host, same build.
; The header dominates this file: the SMT below it is 142 bytes.
;
;   invocation                       pre-fix                      post-fix
;   -------------------------------  ---------------------------  --------------
;   ay FILE (default memory limit)   1.50 GB, 1.8s, exit 124,     11 MB, 0.01s,
;                                    (:reason-unknown "memout")   goal unchanged
;   ay -memory:60000 FILE            3.07 GB, 8.5s, goal comes    11 MB, 0.00s,
;                                    back with `exists` INTACT    goal unchanged
;
; So pre-fix the 3 GB bought nothing: the bounded differential self-check
; discarded the elimination regardless, and under the default memory limit the
; run lost the session outright. The sweeps poll no interrupt (qe_prepass.rs
; checks only BETWEEN eliminator invocations), so this was uninterruptible.
;
; The same shape as a satisfiability query, for anyone who wants one: wrap it
; as (assert (forall ((a Int)) (exists ((v Int)) (and (= (* 1048576 v) x)
; (<= a v))))) and run with --no-proof (which is what routes it into the
; pre-pass). z3 says unsat; pre-fix AY answers unknown(memout) at 1.52 GB /
; 1.9s, post-fix unknown(incomplete quantifier-cegqi) at 31 MB / 0.03s.
; Neither side answers it, so this shape shows only the cost, not a new
; verdict -- which is why the `apply` form above is the primary repro.
;
; The unit-level regression lives in
; crates/ay-dpll/src/qe/cooper/tests.rs::
;   large_coefficient_period_refuses_without_allocating
; which asserts the fail-closed `NotSupported` AND the interned-term count --
; the latter being the assertion that actually fails if the ceiling is removed.
(set-logic LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (exists ((v Int)) (and (= (* 1048576 v) x) (<= y v))))
(apply qe-light)
