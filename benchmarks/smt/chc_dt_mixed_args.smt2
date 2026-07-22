; Predicate with mixed DT and scalar arguments.
; Tests that DT flattening correctly handles mixed argument lists.
; Predicate: inv(counter: Int, state: Pair)
; Init: counter = 0, state = Pair(0, 0)
; Trans: counter' = counter + 1, state.fst' = state.fst + 1, state.snd stays
; Safety: counter = state.fst
; Expected: sat (safe)
(set-logic HORN)

(declare-datatype Pair ((mk (fst Int) (snd Int))))

(declare-fun |inv| (Int Pair) Bool)

; Init
(assert
  (forall ((c Int) (p Pair))
    (=> (and (= c 0) (= (fst p) 0) (= (snd p) 0))
        (inv c p))))

; Trans
(assert
  (forall ((c Int) (p Pair) (c2 Int) (p2 Pair))
    (=> (and (inv c p)
             (= c2 (+ c 1))
             (= (fst p2) (+ (fst p) 1))
             (= (snd p2) (snd p)))
        (inv c2 p2))))

; Safety: counter = fst(state)
(assert
  (forall ((c Int) (p Pair))
    (=> (and (inv c p) (not (= c (fst p))))
        false)))

(check-sat)
(exit)
