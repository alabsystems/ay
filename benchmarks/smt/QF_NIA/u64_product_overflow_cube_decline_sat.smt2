(set-info :smt-lib-version 2.6)
(set-logic QF_NIA)
(set-info :source |
deductive verifier, deductive-checksgen test reassigned_param_mul_realmir: the integer
component of the unsigned 64-bit multiplication-overflow obligation of
wrongvar_unsafe_release (a < 1000, b any u64). Satisfiable: a = 2, b = 2^63,
a * b = 2^64. The pinned z3 5.3.3 answers sat (a = 999, b = 2^64 - 1).
ay answered unknown (incomplete) from 4e96ceb505 until the cube test's
declined steps stopped moving the LP point (#cube-decline-no-trace).
|)
(set-info :license "https://www.apache.org/licenses/LICENSE-2.0")
(set-info :category "industrial")
(set-info :status sat)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun _4 () Bool)
(assert (<= 0 a))
(assert (<= a 18446744073709551615))
(assert (<= 0 b))
(assert (<= b 18446744073709551615))
(assert (= _4 (< a 1000)))
(assert (< a 1000))
(assert (>= a 0))
(assert (>= b 0))
(assert (or (< (* a b) 0) (> (* a b) 18446744073709551615)))
(check-sat)
(exit)
