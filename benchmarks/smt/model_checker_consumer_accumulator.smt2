; model-checker-consumer-style loop accumulator CHC benchmark.
; Models: countdown loop with accumulator: n starts at N, sum accumulates n each step.
; Init: n = 5, sum = 0
; Trans: sum' = sum + n, n' = n - 1 (while n > 0)
; Property: when n = 0, sum = 15 (i.e., sum <= 15)
; Expected: sat (safe) - Z3 Spacer proves this
(set-logic HORN)

(declare-fun Inv (Int Int) Bool)

; Init: n = 5, sum = 0
(assert (forall ((n Int) (sum Int))
  (=> (and (= n 5) (= sum 0))
      (Inv n sum))))

; Transition: while n > 0, sum' = sum + n, n' = n - 1
(assert (forall ((n Int) (sum Int) (n1 Int) (sum1 Int))
  (=> (and (Inv n sum)
           (> n 0)
           (= sum1 (+ sum n))
           (= n1 (- n 1)))
      (Inv n1 sum1))))

; Safety: when n = 0, sum <= 15
(assert (forall ((n Int) (sum Int))
  (=> (and (Inv n sum) (= n 0) (> sum 15))
      false)))

(check-sat)
(exit)
