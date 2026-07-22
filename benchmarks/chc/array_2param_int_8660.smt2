; Simple CHC benchmark with 2 Array (Int Int) sorted predicate parameters
; Models model-checker-consumer-like pattern: heap memory + valid-map, both Int-indexed.
(set-logic HORN)

; Two array parameters: mem (Int->Int) and valid (Int->Int) + scalar index
(declare-fun inv ((Array Int Int) (Array Int Int) Int) Bool)

; Initial: mem[0] = 42, valid[0] = 1, i = 0
(assert (forall ((mem (Array Int Int)) (valid (Array Int Int)) (i Int))
  (=> (and (= (select mem 0) 42) (= (select valid 0) 1) (= i 0))
      (inv mem valid i))))

; Transition: mem' = store(mem, i, select(mem, i) + 1), valid' = valid, i' = i + 1
(assert (forall ((mem (Array Int Int)) (valid (Array Int Int)) (i Int)
                 (mem2 (Array Int Int)) (valid2 (Array Int Int)) (i2 Int))
  (=> (and (inv mem valid i)
           (< i 10)
           (= mem2 (store mem i (+ (select mem i) 1)))
           (= valid2 valid)
           (= i2 (+ i 1)))
      (inv mem2 valid2 i2))))

; Safety: mem[0] >= 42 always
(assert (forall ((mem (Array Int Int)) (valid (Array Int Int)) (i Int))
  (=> (inv mem valid i)
      (not (< (select mem 0) 42)))))

(check-sat)
