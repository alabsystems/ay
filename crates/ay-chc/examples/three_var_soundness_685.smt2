; Copyright 2026 Andrew Yates
; Author: Andrew Yates <andrewyates.name@gmail.com>
;
; Minimal reproducer for soundness bug #685
; AY returns SAT (wrong), Z3 returns UNSAT (correct)
;
; Expected: UNSAT - The abort state IS reachable:
; 1. Init: pc=0, x=0, c=0
; 2. After 6 iterations: pc=0, x=6, c=6
; 3. c=6 > 5 AND x=6 <= 100 -> abort triggers
; 4. State (pc=-2, x=6, c=6) is reachable, query fails

(set-logic HORN)
(declare-fun S (Int Int Int) Bool)  ; (pc, x, counter)

; Init: pc=0, x=0, counter=0
(assert (forall ((pc Int) (x Int) (c Int))
    (=> (and (= pc 0) (= x 0) (= c 0)) (S pc x c))))

; Loop: pc=0, counter <= 5 -> both x and counter increment
(assert (forall ((pc Int) (x Int) (c Int))
    (=> (and (S pc x c) (= pc 0) (<= c 5))
        (S 0 (+ x 1) (+ c 1)))))

; Abort: pc=0, counter > 5, x <= 100 -> abort (pc=-2)
(assert (forall ((pc Int) (x Int) (c Int))
    (=> (and (S pc x c) (= pc 0) (> c 5) (<= x 100))
        (S (- 2) x c))))

; Query: abort unreachable
(assert (forall ((pc Int) (x Int) (c Int))
    (=> (and (S pc x c) (= pc (- 2))) false)))

(check-sat)
