; BENCHMARK 2: Bounded Loop (i < 100)
; Tests: Loop bound inference, bounded iteration
; Z3: 0.02s | AY Target: <0.2s
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((i Int)) (=> (= i 0) (Inv i))))
(assert (forall ((i Int) (i_next Int)) 
  (=> (and (Inv i) (< i 100) (= i_next (+ i 1)))
      (Inv i_next))))
(assert (forall ((i Int)) (=> (and (Inv i) (not (and (>= i 0) (<= i 100)))) false)))
(check-sat)
(get-model)
