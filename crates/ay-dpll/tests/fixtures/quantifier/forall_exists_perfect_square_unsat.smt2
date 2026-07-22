; forall x. exists y. y*y = x is false: 2 is not a perfect square.
(set-logic NIA)
(assert (forall ((x Int)) (exists ((y Int)) (= (* y y) x))))
(check-sat)
