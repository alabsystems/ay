(set-logic HORN)


(declare-fun |main@verifier.error.split| ( ) Bool)
(declare-fun |id@_call| ( Int ) Bool)
(declare-fun |id| ( Bool Bool Bool Int Int ) Bool)
(declare-fun |id@.split| ( Int Int ) Bool)
(declare-fun |main@entry| ( Int ) Bool)

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
  (forall ( (A Int) ) 
    (=>
      (and
        true
      )
      (main@entry A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (v_9 Bool) (v_10 Bool) (v_11 Bool) ) 
    (=>
      (and
        (main@entry B)
        (id v_9 v_10 v_11 C D)
        (and (= v_9 true)
     (= v_10 false)
     (= v_11 false)
     (= A B)
     (or (not G) (and G F))
     (or (not H) (and H G))
     (or (not I) (and I H))
     (= E true)
     (= I true)
     (= E (= D 20)))
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
