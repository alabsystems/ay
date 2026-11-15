; witness: x1=36893488147419103229
; Formerly answered UNSAT after a GMI cut at a fractional integer bound.
(set-logic QF_LIA)
(set-info :status sat)
(declare-const x1 Int)
(assert (<= (+ (* (- 9007199254740991) x1) 7) (- 332306998946228931305442019886759931)))
(assert (<= x1 36893488147419103230))
(assert (= (mod (* 4294967297 x1) 7) 5))
(check-sat)
