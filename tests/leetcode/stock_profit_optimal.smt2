; LeetCode #121: Best Time to Buy and Sell Stock — optimality certificate
; prices = [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8]
; profit >= 9 is impossible, so this is unsat, proving 8 optimal.
(set-logic QF_LIA)
(declare-const buy Int)
(declare-const sell Int)
(declare-const pbuy Int)
(declare-const psell Int)
(declare-const profit Int)
(assert (and (<= 0 buy) (< buy 12)))
(assert (and (<= 0 sell) (< sell 12)))
(assert (< buy sell))
(assert (= pbuy
  (ite (= buy 0) 3 (ite (= buy 1) 1 (ite (= buy 2) 4 (ite (= buy 3) 1
  (ite (= buy 4) 5 (ite (= buy 5) 9 (ite (= buy 6) 2 (ite (= buy 7) 6
  (ite (= buy 8) 5 (ite (= buy 9) 3 (ite (= buy 10) 5 8)))))))))))))
(assert (= psell
  (ite (= sell 0) 3 (ite (= sell 1) 1 (ite (= sell 2) 4 (ite (= sell 3) 1
  (ite (= sell 4) 5 (ite (= sell 5) 9 (ite (= sell 6) 2 (ite (= sell 7) 6
  (ite (= sell 8) 5 (ite (= sell 9) 3 (ite (= sell 10) 5 8)))))))))))))
(assert (= profit (- psell pbuy)))
(assert (>= profit 9))
(check-sat)
