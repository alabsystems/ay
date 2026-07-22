; model-checker-consumer-style datatype CHC benchmark.
; Models: struct with two integer fields, mutation loop.
; Init: x = 0, y = 0
; Trans: x' = x + 1, y' = y + 1
; Property: x = y (fields stay equal)
; Expected: sat (safe) - Z3 Spacer proves this
(set-logic HORN)

(declare-datatype Pair ((mk (fst Int) (snd Int))))

(declare-fun Inv (Pair) Bool)

; Init
(assert (forall ((p Pair))
  (=> (and (= (fst p) 0) (= (snd p) 0))
      (Inv p))))

; Transition
(assert (forall ((p Pair) (p1 Pair))
  (=> (and (Inv p)
           (= (fst p1) (+ (fst p) 1))
           (= (snd p1) (+ (snd p) 1)))
      (Inv p1))))

; Safety: fst = snd
(assert (forall ((p Pair))
  (=> (and (Inv p) (not (= (fst p) (snd p))))
      false)))

(check-sat)
(exit)
