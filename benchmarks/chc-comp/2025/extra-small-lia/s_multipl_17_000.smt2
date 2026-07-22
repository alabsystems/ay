(set-logic HORN)


(declare-fun |LOOPX| ( Int ) Bool)
(declare-fun |LOOPY| ( Int Int ) Bool)

(assert
  (forall ( (A Int) ) 
    (=>
      (and
        (= A 3138)
      )
      (LOOPX A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (LOOPX A)
        (and (= C 0) (= B A))
      )
      (LOOPY B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (LOOPY B A)
        (let ((a!1 (or (<= A 0) (not (= (mod A 3) 0)))))
  (and (= D (+ 2 A)) a!1 (= C B)))
      )
      (LOOPY C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (LOOPY A B)
        (and (= C (+ A B)) (not (<= B 0)) (= (mod B 3) 0))
      )
      (LOOPX C)
    )
  )
)
(assert
  (forall ( (A Int) ) 
    (=>
      (and
        (LOOPX A)
        (not (= (mod A 6) 0))
      )
      false
    )
  )
)

(check-sat)
(exit)
