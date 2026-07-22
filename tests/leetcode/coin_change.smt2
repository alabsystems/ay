; LeetCode #322: Coin Change
; Denominations [10, 9, 1], amount = 37.
; The optimum is 4 coins (10 + 9 + 9 + 9); assert total <= 4 is satisfiable.
(set-option :produce-models true)
(set-logic QF_LIA)
(declare-const c10 Int)
(declare-const c9 Int)
(declare-const c1 Int)
(declare-const total Int)
(assert (>= c10 0))
(assert (>= c9 0))
(assert (>= c1 0))
(assert (= (+ (* 10 c10) (* 9 c9) c1) 37))
(assert (= total (+ c10 c9 c1)))
(assert (<= total 4))
(check-sat)
(get-model)
