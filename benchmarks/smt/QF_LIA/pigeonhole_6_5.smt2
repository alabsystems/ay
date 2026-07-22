; Pigeonhole principle: 6 pigeons into 5 holes (UNSAT)
; With ITE encoding similar to ASP->SMT translations
(set-logic QF_LIA)

; 30 binary variables: p_ij for i=1..6, j=1..5
(declare-fun p11 () Int) (declare-fun p12 () Int) (declare-fun p13 () Int) (declare-fun p14 () Int) (declare-fun p15 () Int)
(declare-fun p21 () Int) (declare-fun p22 () Int) (declare-fun p23 () Int) (declare-fun p24 () Int) (declare-fun p25 () Int)
(declare-fun p31 () Int) (declare-fun p32 () Int) (declare-fun p33 () Int) (declare-fun p34 () Int) (declare-fun p35 () Int)
(declare-fun p41 () Int) (declare-fun p42 () Int) (declare-fun p43 () Int) (declare-fun p44 () Int) (declare-fun p45 () Int)
(declare-fun p51 () Int) (declare-fun p52 () Int) (declare-fun p53 () Int) (declare-fun p54 () Int) (declare-fun p55 () Int)
(declare-fun p61 () Int) (declare-fun p62 () Int) (declare-fun p63 () Int) (declare-fun p64 () Int) (declare-fun p65 () Int)

; Binary domains
(assert (and (<= 0 p11) (<= p11 1))) (assert (and (<= 0 p12) (<= p12 1))) (assert (and (<= 0 p13) (<= p13 1))) (assert (and (<= 0 p14) (<= p14 1))) (assert (and (<= 0 p15) (<= p15 1)))
(assert (and (<= 0 p21) (<= p21 1))) (assert (and (<= 0 p22) (<= p22 1))) (assert (and (<= 0 p23) (<= p23 1))) (assert (and (<= 0 p24) (<= p24 1))) (assert (and (<= 0 p25) (<= p25 1)))
(assert (and (<= 0 p31) (<= p31 1))) (assert (and (<= 0 p32) (<= p32 1))) (assert (and (<= 0 p33) (<= p33 1))) (assert (and (<= 0 p34) (<= p34 1))) (assert (and (<= 0 p35) (<= p35 1)))
(assert (and (<= 0 p41) (<= p41 1))) (assert (and (<= 0 p42) (<= p42 1))) (assert (and (<= 0 p43) (<= p43 1))) (assert (and (<= 0 p44) (<= p44 1))) (assert (and (<= 0 p45) (<= p45 1)))
(assert (and (<= 0 p51) (<= p51 1))) (assert (and (<= 0 p52) (<= p52 1))) (assert (and (<= 0 p53) (<= p53 1))) (assert (and (<= 0 p54) (<= p54 1))) (assert (and (<= 0 p55) (<= p55 1)))
(assert (and (<= 0 p61) (<= p61 1))) (assert (and (<= 0 p62) (<= p62 1))) (assert (and (<= 0 p63) (<= p63 1))) (assert (and (<= 0 p64) (<= p64 1))) (assert (and (<= 0 p65) (<= p65 1)))

; Each pigeon in exactly one hole (using ITE-like encoding: sum = 1)
(assert (= (+ p11 p12 p13 p14 p15) 1))
(assert (= (+ p21 p22 p23 p24 p25) 1))
(assert (= (+ p31 p32 p33 p34 p35) 1))
(assert (= (+ p41 p42 p43 p44 p45) 1))
(assert (= (+ p51 p52 p53 p54 p55) 1))
(assert (= (+ p61 p62 p63 p64 p65) 1))

; Each hole has at most one pigeon
(assert (<= (+ p11 p21 p31 p41 p51 p61) 1))
(assert (<= (+ p12 p22 p32 p42 p52 p62) 1))
(assert (<= (+ p13 p23 p33 p43 p53 p63) 1))
(assert (<= (+ p14 p24 p34 p44 p54 p64) 1))
(assert (<= (+ p15 p25 p35 p45 p55 p65) 1))

(check-sat)
