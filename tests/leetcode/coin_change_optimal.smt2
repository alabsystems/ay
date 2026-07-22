; LeetCode #322: Coin Change — optimality certificate
; Denominations [10, 9, 1], amount = 37.
; 3 coins are not enough (max reachable with 3 coins is 30), so total <= 3
; is unsat, proving the 4-coin solution optimal.
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
(assert (<= total 3))
(check-sat)
