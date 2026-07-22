; LeetCode #84: Largest Rectangle in Histogram — optimality certificate
; heights = [2, 1, 5, 6, 2, 3]; area >= 11 is impossible, so this is unsat,
; proving the area-10 rectangle optimal.
(set-logic QF_LIA)
(declare-const left Int)
(declare-const right Int)
(declare-const height Int)
(declare-const width Int)
(declare-const area Int)
(assert (and (<= 0 left) (<= left right) (<= right 5)))
(assert (>= height 1))
(assert (=> (and (<= left 0) (<= 0 right)) (<= height 2)))
(assert (=> (and (<= left 1) (<= 1 right)) (<= height 1)))
(assert (=> (and (<= left 2) (<= 2 right)) (<= height 5)))
(assert (=> (and (<= left 3) (<= 3 right)) (<= height 6)))
(assert (=> (and (<= left 4) (<= 4 right)) (<= height 2)))
(assert (=> (and (<= left 5) (<= 5 right)) (<= height 3)))
(assert (= width (+ (- right left) 1)))
(assert (= area
  (ite (= width 1) height
  (ite (= width 2) (* 2 height)
  (ite (= width 3) (* 3 height)
  (ite (= width 4) (* 4 height)
  (ite (= width 5) (* 5 height) (* 6 height))))))))
(assert (>= area 11))
(check-sat)
