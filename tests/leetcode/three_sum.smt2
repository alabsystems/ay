; LeetCode #15 variant: Three Sum (a + b = c)
; array = [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8]
; Find distinct indices i, j, k with a[i] + a[j] = a[k].
(set-option :produce-models true)
(set-logic QF_LIA)
(declare-const i Int)
(declare-const j Int)
(declare-const k Int)
(declare-const vi Int)
(declare-const vj Int)
(declare-const vk Int)
(assert (and (<= 0 i) (< i 12)))
(assert (and (<= 0 j) (< j 12)))
(assert (and (<= 0 k) (< k 12)))
(assert (distinct i j k))
(assert (= vi
  (ite (= i 0) 3 (ite (= i 1) 1 (ite (= i 2) 4 (ite (= i 3) 1
  (ite (= i 4) 5 (ite (= i 5) 9 (ite (= i 6) 2 (ite (= i 7) 6
  (ite (= i 8) 5 (ite (= i 9) 3 (ite (= i 10) 5 8)))))))))))))
(assert (= vj
  (ite (= j 0) 3 (ite (= j 1) 1 (ite (= j 2) 4 (ite (= j 3) 1
  (ite (= j 4) 5 (ite (= j 5) 9 (ite (= j 6) 2 (ite (= j 7) 6
  (ite (= j 8) 5 (ite (= j 9) 3 (ite (= j 10) 5 8)))))))))))))
(assert (= vk
  (ite (= k 0) 3 (ite (= k 1) 1 (ite (= k 2) 4 (ite (= k 3) 1
  (ite (= k 4) 5 (ite (= k 5) 9 (ite (= k 6) 2 (ite (= k 7) 6
  (ite (= k 8) 5 (ite (= k 9) 3 (ite (= k 10) 5 8)))))))))))))
(assert (= (+ vi vj) vk))
(check-sat)
(get-model)
