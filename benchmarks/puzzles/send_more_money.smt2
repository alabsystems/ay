; Author: Andrew Yates <andrewyates.name@gmail.com>
; SEND+MORE=MONEY cryptarithmetic. Classic 8-variable distinct puzzle.
; Z3 solves in <0.5s. Expected solution: {S=9,E=5,N=6,D=7,M=1,O=0,R=8,Y=2}.
; Performance tracked by #8762.
(set-logic QF_LIA)
(declare-const S Int)
(declare-const E Int)
(declare-const N Int)
(declare-const D Int)
(declare-const M Int)
(declare-const O Int)
(declare-const R Int)
(declare-const Y Int)
(assert (and (>= S 0) (<= S 9)))
(assert (and (>= E 0) (<= E 9)))
(assert (and (>= N 0) (<= N 9)))
(assert (and (>= D 0) (<= D 9)))
(assert (and (>= M 0) (<= M 9)))
(assert (and (>= O 0) (<= O 9)))
(assert (and (>= R 0) (<= R 9)))
(assert (and (>= Y 0) (<= Y 9)))
; Leading digits can't be zero
(assert (>= S 1))
(assert (>= M 1))
; All digits distinct
(assert (distinct S E N D M O R Y))
; SEND + MORE = MONEY
;   S*1000 + E*100 + N*10 + D
; + M*1000 + O*100 + R*10 + E
; = M*10000 + O*1000 + N*100 + E*10 + Y
(assert (= (+ (* 1000 S) (* 100 E) (* 10 N) D
              (* 1000 M) (* 100 O) (* 10 R) E)
           (+ (* 10000 M) (* 1000 O) (* 100 N) (* 10 E) Y)))
(check-sat)
