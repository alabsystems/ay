; Test for init-guarded implication strengthening (#967)
; Andrew Yates <andrewyates.name@gmail.com>
;
; This is a simplified test that the solver can prove safe.
; A=0 is init-only, B always increments. Bad state A=0 AND B>5 is unreachable.
;
(set-logic HORN)
(declare-fun |P| ( Int Int ) Bool)

; Init: A=0, B=0
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and (= A 0) (= B 0))
      (P A B)
    )
  )
)

; Transition: A' = A+1, B' = B+1
(assert
  (forall ( (A Int) (B Int) (A1 Int) (B1 Int) )
    (=>
      (and (P A B) (= A1 (+ A 1)) (= B1 (+ B 1)))
      (P A1 B1)
    )
  )
)

; Bad: A=0 AND B > 5 (unreachable since A and B start at 0 and increment together)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and (P A B) (= A 0) (> B 5))
      false
    )
  )
)

(check-sat)
(exit)
