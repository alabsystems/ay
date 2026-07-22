; Pigeonhole principle: 3 pigeons into 2 holes (UNSAT)
; p_ij = 1 means pigeon i goes to hole j
; Each pigeon goes to exactly one hole, each hole has at most one pigeon.
; 3 pigeons, 2 holes -> impossible.
(set-logic QF_LIA)

; 6 binary variables
(declare-fun p11 () Int) (declare-fun p12 () Int)
(declare-fun p21 () Int) (declare-fun p22 () Int)
(declare-fun p31 () Int) (declare-fun p32 () Int)

; Binary domain
(assert (and (<= 0 p11) (<= p11 1)))
(assert (and (<= 0 p12) (<= p12 1)))
(assert (and (<= 0 p21) (<= p21 1)))
(assert (and (<= 0 p22) (<= p22 1)))
(assert (and (<= 0 p31) (<= p31 1)))
(assert (and (<= 0 p32) (<= p32 1)))

; Each pigeon in exactly one hole
(assert (= (+ p11 p12) 1))
(assert (= (+ p21 p22) 1))
(assert (= (+ p31 p32) 1))

; Each hole has at most one pigeon
(assert (<= (+ p11 p21 p31) 1))
(assert (<= (+ p12 p22 p32) 1))

(check-sat)
