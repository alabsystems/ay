; Counter safe example in CHC-COMP SMT-LIB2 format
(set-logic HORN)

(declare-fun Inv (Int) Bool)

; Initial: x = 0 => Inv(x)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))

; Transition: Inv(x) /\ x < 10 => Inv(x+1)
(assert (forall ((x Int) (y Int))
    (=> (and (Inv x) (< x 10) (= y (+ x 1)))
        (Inv y))))

; Safety query: Inv(x) /\ x > 10 => false
(assert (forall ((x Int)) (=> (and (Inv x) (> x 10)) false)))

(check-sat)
