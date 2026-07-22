; LeetCode #1: Two Sum
; nums = [2, 7, 11, 15], target = 9
; Find distinct indices i, j with nums[i] + nums[j] = 9.
(set-option :produce-models true)
(set-logic QF_LIA)
(declare-const i Int)
(declare-const j Int)
(declare-const vi Int)
(declare-const vj Int)
(assert (and (<= 0 i) (< i 4)))
(assert (and (<= 0 j) (< j 4)))
(assert (distinct i j))
(assert (= vi (ite (= i 0) 2 (ite (= i 1) 7 (ite (= i 2) 11 15)))))
(assert (= vj (ite (= j 0) 2 (ite (= j 1) 7 (ite (= j 2) 11 15)))))
(assert (= (+ vi vj) 9))
(check-sat)
(get-model)
