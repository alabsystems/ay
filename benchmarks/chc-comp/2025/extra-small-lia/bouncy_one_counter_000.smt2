(set-logic HORN)


(declare-fun |itp2| ( Int Int Int ) Bool)
(declare-fun |itp1| ( Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (and (= B 0) (= A 0) (= C 0))
      )
      (itp1 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (itp1 A B C)
        (and (= E (+ 1 B)) (= D (+ 1 A)) (= F (+ (- 2) C)))
      )
      (itp1 D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (itp1 A B C)
        true
      )
      (itp2 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (itp2 A B C)
        (and (= E (+ (- 3) B)) (= D (+ (- 1) A)) (= F (+ 2 C)))
      )
      (itp2 D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (itp2 A C B)
        (and (or (not (<= C 0)) (not (>= B 0))) (<= A 0))
      )
      false
    )
  )
)

(check-sat)
(exit)
