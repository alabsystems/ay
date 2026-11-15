(set-info :smt-lib-version 2.6)
(set-logic QF_NIA)
(set-info :source |
Minimal form of u64_product_overflow_cube_decline_sat.smt2: one product of a
bounded and an unbounded-in-u64 factor exceeding u64::MAX. Satisfiable:
a = 2, b = 2^63. The pinned z3 5.3.3 answers sat (a = 999, b = 2^64 - 1).
ay answered unknown (incomplete) from 4e96ceb505 until the cube test's
declined steps stopped moving the LP point (#cube-decline-no-trace).
|)
(set-info :license "https://www.apache.org/licenses/LICENSE-2.0")
(set-info :category "crafted")
(set-info :status sat)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (and (<= 0 a) (< a 1000) (<= 0 b) (<= b 18446744073709551615)))
(assert (> (* a b) 18446744073709551615))
(check-sat)
(exit)
