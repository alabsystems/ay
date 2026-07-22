(set-logic HORN)

(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(declare-fun R (Int) Bool)

; Fact: P(0)
(assert
  (forall ((x Int))
    (=>
      (= x 0)
      (P x)
    )
  )
)

; Transition: P(x) /\ xp = x + 1 => P(xp)
(assert
  (forall ((x Int) (xp Int))
    (=>
      (and
        (P x)
        (= xp (+ x 1))
      )
      (P xp)
    )
  )
)

; Propagation chain: P -> Q -> R
(assert
  (forall ((x Int))
    (=>
      (P x)
      (Q x)
    )
  )
)

(assert
  (forall ((x Int))
    (=>
      (Q x)
      (R x)
    )
  )
)

; Safety query: R(x) /\ x < 0 => false
(assert
  (forall ((x Int))
    (=>
      (and
        (R x)
        (< x 0)
      )
      false
    )
  )
)

(check-sat)
(exit)
