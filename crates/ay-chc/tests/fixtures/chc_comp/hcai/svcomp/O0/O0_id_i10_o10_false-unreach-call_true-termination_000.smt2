(set-logic HORN)


(declare-fun |main@verifier.error.split| ( ) Bool)
(declare-fun |main@entry| ( ) Bool)
(declare-fun |id@_call| ( Int ) Bool)
(declare-fun |id| ( Bool Bool Bool Int Int ) Bool)
(declare-fun |id@.split| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (v_2 Bool) (v_3 Bool) (v_4 Bool) ) 
    (=>
      (and
        (and true (= v_2 true) (= v_3 true) (= v_4 true))
      )
      (id v_2 v_3 v_4 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (v_2 Bool) (v_3 Bool) (v_4 Bool) ) 
    (=>
      (and
        (and true (= v_2 false) (= v_3 true) (= v_4 true))
      )
      (id v_2 v_3 v_4 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (v_2 Bool) (v_3 Bool) (v_4 Bool) ) 
    (=>
      (and
        (and true (= v_2 false) (= v_3 false) (= v_4 false))
      )
      (id v_2 v_3 v_4 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (v_2 Bool) (v_3 Bool) (v_4 Bool) ) 
    (=>
      (and
        (id@.split B A)
        (and (= v_2 true) (= v_3 false) (= v_4 false))
      )
      (id v_2 v_3 v_4 A B)
    )
  )
)
(assert
  (forall ( (A Int) ) 
    (=>
      (and
        true
      )
      (id@_call A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Bool) (F Int) (G Bool) (H Bool) (I Int) (J Bool) (K Bool) (L Int) (M Int) (v_13 Bool) (v_14 Bool) ) 
    (=>
      (and
        (id@_call M)
        (id E v_13 v_14 A B)
        (and (= v_13 false)
     (= v_14 false)
     (or (not G) (not E) (not D))
     (or (not H) (not G) (= I 0))
     (or (not H) (not G) (= L I))
     (or (not H) (not G) D)
     (or (not J) (and J E) (and H G))
     (or (not J) (not E) (= F C))
     (or (not J) (not E) (= L F))
     (or (not E) (= A (+ (- 1) M)))
     (or (not E) (= C (+ 1 B)))
     (or (not E) (and G E))
     (or (not H) G)
     (or (not K) (and K J))
     (= K true)
     (= D (= M 0)))
      )
      (id@.split L M)
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
  (forall ( (A Int) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (v_6 Bool) (v_7 Bool) (v_8 Bool) (v_9 Int) ) 
    (=>
      (and
        main@entry
        (id v_6 v_7 v_8 v_9 A)
        (and (= v_6 true)
     (= v_7 false)
     (= v_8 false)
     (= 10 v_9)
     (or (not D) (and D C))
     (or (not E) (and E D))
     (or (not F) (and F E))
     (= B true)
     (= F true)
     (= B (= A 10)))
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
