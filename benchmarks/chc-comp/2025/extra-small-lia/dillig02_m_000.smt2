(set-logic HORN)


(declare-fun |inv| ( Int Int Int Int Int Int ) Bool)
(declare-fun |inv1| ( Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (and (= E 0) (= D 0) (= C (+ A (* (- 1) B))) (= B 0) (= A 1) (= F 0))
      )
      (inv A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (inv A B C D E F)
        true
      )
      (inv1 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (inv1 E F A C B D)
        (let ((a!1 (= H (ite (= (mod G 2) 1) (+ 1 C) C))))
  (and (= I (+ 1 B)) a!1 (= G (+ A C B D)) (= J (+ 2 D))))
      )
      (inv1 E F G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (inv1 A B C D E F)
        true
      )
      (inv A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (inv A B C E F D)
        (not (= E F))
      )
      false
    )
  )
)

(check-sat)
(exit)
