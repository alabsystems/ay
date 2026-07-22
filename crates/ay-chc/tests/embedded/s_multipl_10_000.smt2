(set-logic HORN)


(declare-fun |SAD| ( Int Int Int ) Bool)
(declare-fun |FUN| ( Int Int Int ) Bool)
(declare-fun |WEE| ( Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (and (= A 0) (not (<= C 0)) (= B 0))
      )
      (FUN A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (FUN A B E)
        (and (= C (+ 1 A)) (not (<= E B)) (= D (+ 1 B)))
      )
      (FUN C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (FUN B A E)
        (and (= C B) (>= A E) (= D 0))
      )
      (SAD C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (SAD A B E)
        (and (= C (+ (- 1) A)) (not (<= E B)) (= D (+ 1 B)))
      )
      (SAD C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (SAD B A E)
        (and (= C B) (>= A E) (= D 0))
      )
      (WEE C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (WEE A B E)
        (and (= C (+ 1 A)) (not (<= E B)) (= D (+ 1 B)))
      )
      (WEE C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (WEE B A C)
        (and (>= A C) (not (= B C)))
      )
      false
    )
  )
)

(check-sat)
(exit)
