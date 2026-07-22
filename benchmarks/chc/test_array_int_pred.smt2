; Simple CHC benchmark with Array Int Int sorted predicate parameter
(set-logic HORN)

; Predicate with integer array parameter and integer counter
(declare-fun inv ((Array Int Int) Int) Bool)

; Initial: arr[0] = 10, i = 0
(assert (forall ((arr (Array Int Int)) (i Int))
  (=> (and (= (select arr 0) 10) (= i 0))
      (inv arr i))))

; Transition: i' = i + 1, requires i < 5
(assert (forall ((arr (Array Int Int)) (i Int)
                 (arr2 (Array Int Int)) (i2 Int))
  (=> (and (inv arr i)
           (< i 5)
           (= arr2 (store arr i (+ (select arr i) 1)))
           (= i2 (+ i 1)))
      (inv arr2 i2))))

; Safety: arr[0] >= 10 (the initial store never overwrites index 0 after i >= 1)
(assert (forall ((arr (Array Int Int)) (i Int))
  (=> (inv arr i)
      (not (< (select arr 0) 10)))))

(check-sat)
