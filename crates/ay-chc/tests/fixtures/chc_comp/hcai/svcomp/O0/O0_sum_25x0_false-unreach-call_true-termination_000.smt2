(set-logic HORN)


(declare-fun |main@verifier.error.split| ( ) Bool)
(declare-fun |main@entry| ( ) Bool)
(declare-fun |sum@.split| ( Int Int Int ) Bool)
(declare-fun |sum| ( Bool Bool Bool Int Int Int ) Bool)
(declare-fun |sum@_call| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (v_3 Bool) (v_4 Bool) (v_5 Bool) ) 
    (=>
      (and
        (and true (= v_3 true) (= v_4 true) (= v_5 true))
      )
      (sum v_3 v_4 v_5 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (v_3 Bool) (v_4 Bool) (v_5 Bool) ) 
    (=>
      (and
        (and true (= v_3 false) (= v_4 true) (= v_5 true))
      )
      (sum v_3 v_4 v_5 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (v_3 Bool) (v_4 Bool) (v_5 Bool) ) 
    (=>
      (and
        (and true (= v_3 false) (= v_4 false) (= v_5 false))
      )
      (sum v_3 v_4 v_5 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (v_3 Bool) (v_4 Bool) (v_5 Bool) ) 
    (=>
      (and
        (sum@.split C B A)
        (and (= v_3 true) (= v_4 false) (= v_5 false))
      )
      (sum v_3 v_4 v_5 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        true
      )
      (sum@_call A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) (F Int) (G Bool) (H Int) (I Bool) (J Int) (K Bool) (L Bool) (M Int) (N Int) (O Int) (v_15 Bool) (v_16 Bool) ) 
    (=>
      (and
        (sum@_call N O)
        (sum G v_15 v_16 A B E)
        (and (= v_15 false)
     (= v_16 false)
     (or (not G) (not D) (not C))
     (or (not I) D (not C))
     (or (not K) (and K I) (and K G))
     (or (not K) (not G) (= H E))
     (or (not K) (not G) (= M H))
     (or (not K) (not I) (= J F))
     (or (not K) (not I) (= M J))
     (or (not G) (= A (+ (- 1) O)))
     (or (not G) (= B (+ 1 N)))
     (or (not G) (and G C))
     (or (not I) (= F (+ N O)))
     (or (not I) (and I C))
     (or (not L) (and L K))
     (= L true)
     (not (= (<= 1 O) D)))
      )
      (sum@.split M N O)
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        true
      )
      main@entry
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (v_6 Bool) (v_7 Bool) (v_8 Bool) (v_9 Int) (v_10 Int) ) 
    (=>
      (and
        main@entry
        (sum v_6 v_7 v_8 v_9 v_10 A)
        (and (= v_6 true)
     (= v_7 false)
     (= v_8 false)
     (= 25 v_9)
     (= 0 v_10)
     (or (not D) (and D C))
     (or (not E) (and E D))
     (or (not F) (and F E))
     (= B true)
     (= F true)
     (= B (= A 25)))
      )
      main@verifier.error.split
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@verifier.error.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
