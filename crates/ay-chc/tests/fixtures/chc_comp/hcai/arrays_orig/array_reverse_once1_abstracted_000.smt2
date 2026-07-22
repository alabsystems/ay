(set-logic HORN)


(declare-fun |write1| ( Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |incr| ( Int Int Int Int Int Int ) Bool)
(declare-fun |init| ( Int Int Int Int Int ) Bool)
(declare-fun |write2| ( Int Int Int Int Int Int Int ) Bool)
(declare-fun |end| ( Int Int Int Int Int ) Bool)
(declare-fun |read1| ( Int Int Int Int Int Int ) Bool)
(declare-fun |loop| ( Int Int Int Int Int Int ) Bool)
(declare-fun |read2| ( Int Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (v_3 Int) (v_4 Int) ) 
    (=>
      (and
        (and (not (<= A B)) (<= 0 B) (= v_3 B) (= v_4 C))
      )
      (init A B C v_3 v_4)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (and (<= 0 B) (<= 0 D) (not (<= A B)) (not (<= A D)) (not (= B D)))
      )
      (init A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (v_5 Int) ) 
    (=>
      (and
        (init A B C D E)
        (= 0 v_5)
      )
      (loop A v_5 B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (loop A B C D E F)
        (not (<= (+ A (* (- 2) B)) 1))
      )
      (read1 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (v_7 Int) ) 
    (=>
      (and
        (read1 A B v_7 C F G)
        (read1 A B D E F G)
        (and (= v_7 B) (not (= B D)))
      )
      (read2 A B C D E F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (v_5 Int) (v_6 Int) (v_7 Int) ) 
    (=>
      (and
        (read1 A B v_5 C D E)
        (and (= v_5 B) (= v_6 B) (= v_7 C))
      )
      (read2 A B C v_6 v_7 D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (read2 B C D A E H I)
        (read2 B C D F G H I)
        (let ((a!1 (not (= (+ B (* (- 1) C)) (+ 1 F)))))
  (and (= A (+ (- 1) B (* (- 1) C))) a!1))
      )
      (write1 B C D E F G H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (v_8 Int) ) 
    (=>
      (and
        (read2 C D E A F G H)
        (and (= B (+ (- 1) C (* (- 1) D))) (= A (+ (- 1) C (* (- 1) D))) (= v_8 F))
      )
      (write1 C D E F B v_8 G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (write1 A B C D E F G H)
        (not (= B E))
      )
      (write2 A B C E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (v_7 Int) (v_8 Int) ) 
    (=>
      (and
        (write1 A B C D v_7 E F G)
        (and (= v_7 B) (= v_8 B))
      )
      (write2 A B C v_8 D F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (write2 A B C D E F G)
        (not (= (+ A (* (- 1) B)) (+ 1 D)))
      )
      (incr A B D E F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (write2 C D E A F G H)
        (and (= B (+ (- 1) C (* (- 1) D))) (= A (+ (- 1) C (* (- 1) D))))
      )
      (incr C D B E G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (incr B C D E F G)
        (= A (+ 1 C))
      )
      (loop B A D E F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (loop A B C D E F)
        (>= (* 2 B) (+ (- 1) A))
      )
      (end A C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (end B C D A E)
        (and (not (= D E)) (>= C 0) (not (<= B C)) (= A (+ (- 1) B (* (- 1) C))))
      )
      false
    )
  )
)

(check-sat)
(exit)
