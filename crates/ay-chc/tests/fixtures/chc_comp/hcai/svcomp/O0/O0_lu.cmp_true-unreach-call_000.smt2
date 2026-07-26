(set-logic HORN)


(declare-fun |main@_bb| ( Int Int (Array Int Int) Int (Array Int Int) ) Bool)
(declare-fun |__VERIFIER_assert@_1| ( (Array Int Int) (Array Int Int) Int ) Bool)
(declare-fun |main@verifier.error.split| ( ) Bool)
(declare-fun |__VERIFIER_assert@_call3| ( (Array Int Int) (Array Int Int) Int ) Bool)
(declare-fun |main@_bb2| ( Int Int Int (Array Int Int) (Array Int Int) Int ) Bool)
(declare-fun |main@entry| ( (Array Int Int) (Array Int Int) ) Bool)
(declare-fun |__VERIFIER_assert| ( Bool Bool Bool (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) Int ) Bool)

(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (v_3 Bool) (v_4 Bool) (v_5 Bool) (v_6 (Array Int Int)) (v_7 (Array Int Int)) ) 
    (=>
      (and
        (and true (= v_3 true) (= v_4 true) (= v_5 true) (= v_6 A) (= v_7 B))
      )
      (__VERIFIER_assert v_3 v_4 v_5 A v_6 B v_7 C)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (v_3 Bool) (v_4 Bool) (v_5 Bool) (v_6 (Array Int Int)) (v_7 (Array Int Int)) ) 
    (=>
      (and
        (and true (= v_3 false) (= v_4 true) (= v_5 true) (= v_6 A) (= v_7 B))
      )
      (__VERIFIER_assert v_3 v_4 v_5 A v_6 B v_7 C)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (v_3 Bool) (v_4 Bool) (v_5 Bool) (v_6 (Array Int Int)) (v_7 (Array Int Int)) ) 
    (=>
      (and
        (and true (= v_3 false) (= v_4 false) (= v_5 false) (= v_6 A) (= v_7 B))
      )
      (__VERIFIER_assert v_3 v_4 v_5 A v_6 B v_7 C)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (v_3 Bool) (v_4 Bool) (v_5 Bool) (v_6 (Array Int Int)) (v_7 (Array Int Int)) ) 
    (=>
      (and
        (__VERIFIER_assert@_call3 A B C)
        (and (= v_3 true) (= v_4 false) (= v_5 false) (= v_6 A) (= v_7 B))
      )
      (__VERIFIER_assert v_3 v_4 v_5 A v_6 B v_7 C)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) ) 
    (=>
      (and
        true
      )
      (__VERIFIER_assert@_1 A B C)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D (Array Int Int)) (E (Array Int Int)) (F Int) ) 
    (=>
      (and
        (__VERIFIER_assert@_1 D E F)
        (and (or (not C) (and C B)) (not A) (= C true) (= A (= F 0)))
      )
      (__VERIFIER_assert@_call3 D E F)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) ) 
    (=>
      (and
        true
      )
      (main@entry A B)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C (Array Int Int)) (D (Array Int Int)) (E Bool) (F Bool) (G Int) (H Int) (I Int) (J (Array Int Int)) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (main@entry A B)
        (and (or (not F) (not E) (= D B))
     (or (not F) (not E) (= L D))
     (or (not F) (not E) (= J C))
     (or (not F) (not E) (= G 0))
     (or (not F) (not E) (= I G))
     (or (not E) (and F E))
     (= E true)
     (or (not F) (not E) (= C A)))
      )
      (main@_bb H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G (Array Int Int)) (H (Array Int Int)) (I (Array Int Int)) (J Int) (K Int) (L Int) (M (Array Int Int)) (N (Array Int Int)) (O Int) (P (Array Int Int)) (Q (Array Int Int)) (R Bool) (S Bool) (T Int) (U Int) (V Int) (W (Array Int Int)) (X Int) (Y (Array Int Int)) (v_25 Bool) (v_26 Bool) ) 
    (=>
      (and
        (main@_bb2 U L A G H X)
        (__VERIFIER_assert S v_25 v_26 G N H I J)
        (let ((a!1 (or (not E) (not (= (<= 50 L) D))))
      (a!2 (or (not S) (= K (+ X (* 8 L))))))
  (and (= v_25 false)
       (= v_26 false)
       (or (not E) (not C) (not B))
       (or (not (<= K 0)) (not S) (<= X 0))
       (or (not S) F (not E))
       (or (not S) (not R) (= P M))
       (or (not S) (not R) (= Q N))
       (or (not S) (not R) (= Y Q))
       (or (not S) (not R) (= W P))
       (or (not S) (not R) (= T O))
       (or (not S) (not R) (= V T))
       a!1
       (or (not E) (= J (ite D 1 0)))
       (or (not E) (and E B))
       (or (not R) (and S R))
       a!2
       (or (not S) (= O (+ 1 L)))
       (or (not S) (not (<= X 0)))
       (or (not S) (and S E))
       (= R true)
       (not (= (<= 6 A) C))))
      )
      (main@_bb U V W X Y)
    )
  )
)
(assert
  (forall ( (A Bool) (B (Array Int Int)) (C (Array Int Int)) (D Bool) (E Bool) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) (K (Array Int Int)) (L Int) ) 
    (=>
      (and
        (main@_bb G H K L B)
        (and (or (not E) (not D) (= C B))
     (or (not E) (not D) (= J C))
     (or (not E) (not D) (= F 0))
     (or (not E) (not D) (= I F))
     (or (not D) (and E D))
     (= A true)
     (= D true)
     (not (= (<= 6 H) A)))
      )
      (main@_bb2 G H I J K L)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Bool) (C Bool) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Bool) (J (Array Int Int)) (K Bool) (L (Array Int Int)) (M Bool) (N Bool) (O (Array Int Int)) (P Int) (Q Int) (R (Array Int Int)) (S Int) (T (Array Int Int)) (U Bool) (V Bool) (W Int) (X Int) (Y Int) (Z Int) (A1 (Array Int Int)) (B1 (Array Int Int)) (C1 Int) ) 
    (=>
      (and
        (main@_bb2 X Y Q A B1 C1)
        (let ((a!1 (or (not K) (= G (+ X (* 400 Y) (* 8 Q)))))
      (a!2 (or (not M) (= F (+ X (* 400 Y) (* 8 Q)))))
      (a!3 (or (not V) (= P (+ X (* 400 Y) (* 8 Q))))))
  (and (or (<= X 0) (not K) (not (<= G 0)))
       (or (<= X 0) (not M) (not (<= F 0)))
       (or C (not M) (not B))
       (or (not N) (not M) (= O J))
       (or (not N) (not M) (= R O))
       (or I (not K) (not M))
       (or (not I) (not N) (not M))
       (or (not V) (<= X 0) (not (<= P 0)))
       (or (not V) (and V K) (and N M))
       (or (not V) (not K) (= L H))
       (or (not V) (not K) (= R L))
       (or (not V) (not U) (= T R))
       (or (not V) (not U) (= A1 T))
       (or (not V) (not U) (= W S))
       (or (not V) (not U) (= Z W))
       a!1
       (or (not K) (not (<= X 0)))
       (or (not K) (and M K))
       (or (not M) (= I (= Y Q)))
       (or (not M) (= D (+ 2 E)))
       a!2
       (or (not M) (= E (+ Y Q)))
       (or (not M) (not (<= X 0)))
       (or (not M) (and M B))
       (or (not N) M)
       (or (not U) (and V U))
       a!3
       (or (not V) (= S (+ 1 Q)))
       (or (not V) (not (<= X 0)))
       (= U true)
       (not (= (<= 6 Q) C))))
      )
      (main@_bb2 X Y Z A1 B1 C1)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C (Array Int Int)) (D Int) (E Int) (F Bool) (G Bool) (H Int) (I Bool) (J Bool) (K Bool) (L Bool) (M Int) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) ) 
    (=>
      (and
        (main@_bb2 A H E B C D)
        (let ((a!1 (or (not J) (not (= (<= 50 H) I)))))
  (and (or (not J) (not G) (not F))
       (or (not L) (not K) (not J))
       (or (not P) (and O P))
       (or (not Q) (and Q P))
       (or (not R) (and R Q))
       a!1
       (or (not J) (= M (ite I 1 0)))
       (or (not J) (and J F))
       (or (not L) (and L J))
       (or (not O) (= N (= M 0)))
       (or (not O) (and O L))
       (or (not O) N)
       (= R true)
       (not (= (<= 6 E) G))))
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
