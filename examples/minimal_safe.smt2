; Minimal safe CHC - invariant: x >= 0
(set-logic HORN)

(declare-fun inv (Int) Bool)

; Init: x = 0
(assert (inv 0))

; Trans: x >= 0 => inv(x+1)
(assert (forall ((x Int))
    (=> (and (inv x) (>= x 0))
        (inv (+ x 1)))))

; Query: inv(x) and x < 0 => false
(assert (forall ((x Int))
    (=> (and (inv x) (< x 0))
        false)))

(check-sat)
