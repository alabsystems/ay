(set-logic HORN)


(declare-fun |ERR| ( ) Bool)
(declare-fun |MAIN| ( Int Int Bool Bool Bool Int Bool Bool Int Bool Bool Bool ) Bool)
(declare-fun |Age_step| ( Bool Int Bool Int Bool Bool Int Bool ) Bool)
(declare-fun |INIT_STATE| ( ) Bool)
(declare-fun |Sofar_step| ( Bool Bool Bool Bool Bool Bool ) Bool)
(declare-fun |top_step| ( Int Int Bool Bool Bool Int Int Bool Bool Bool Int Bool Bool Int Bool Bool Int Int Bool Bool Bool Int Bool Bool Int Bool Bool ) Bool)
(declare-fun |top_reset| ( Int Int Bool Bool Bool Int Bool Bool Int Bool Bool Int Int Bool Bool Bool Int Bool Bool Int Bool Bool ) Bool)
(declare-fun |Sofar_reset| ( Bool Bool Bool Bool ) Bool)
(declare-fun |Age_reset| ( Bool Int Bool Bool Int Bool ) Bool)

(assert
  (forall ( (A Bool) (B Int) (C Bool) (D Bool) (E Int) (F Bool) ) 
    (=>
      (and
        (and (= D A) (= F true) (= E B))
      )
      (Age_reset A B C D E F)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Int) (E Bool) (F Int) (G Bool) (H Bool) (I Int) (J Bool) ) 
    (=>
      (and
        (let ((a!1 (and (or (not E) (= D (+ 1 F))) (or E (= D 0)))))
  (and (= A G) (= B A) (= H C) (or (not B) (= D 0)) (or B a!1) (not J) (= I D)))
      )
      (Age_step C D E F G H I J)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) ) 
    (=>
      (and
        (and (= D true) (= C A))
      )
      (Sofar_reset A B C D)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) ) 
    (=>
      (and
        (and (= A F) (= G D) (or B (= D (or E C))) (or (not B) (= D C)) (not H) (= B A))
      )
      (Sofar_step C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Bool) (F Int) (G Bool) (H Bool) (I Int) (J Bool) (K Bool) (L Int) (M Int) (N Bool) (O Bool) (P Bool) (Q Int) (R Bool) (S Bool) (T Int) (U Bool) (V Bool) ) 
    (=>
      (and
        (Sofar_reset C D N O)
        (Age_reset H I J S T U)
        (Age_reset E F G P Q R)
        (and (= M B) (= V true) (= L A))
      )
      (top_reset A B C D E F G H I J K L M N O P Q R S T U V)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Int) (F Bool) (G Bool) (H Int) (I Bool) (J Int) (K Bool) (L Bool) (M Bool) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Bool) (T Bool) (U Bool) (V Int) (W Int) (X Bool) (Y Bool) (Z Bool) (A1 Int) (B1 Bool) (C1 Bool) (D1 Int) (E1 Bool) (F1 Bool) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Int) (M1 Bool) (N1 Bool) (O1 Int) (P1 Bool) (Q1 Bool) ) 
    (=>
      (and
        (Age_step T J D E F N1 O1 P1)
        (Age_step S N G H I K1 L1 M1)
        (Sofar_step A M K L I1 J1)
        (let ((a!1 (= U (or (not M) (<= N (+ O P)))))
      (a!2 (and (or (not (>= N O)) T) (<= J P) (>= P 1) (>= O 1))))
  (and (= H A1)
       (= G1 P)
       (= H1 O)
       (= B F1)
       (= C B)
       (= D C1)
       (= F E1)
       (= G Z)
       (= I B1)
       (= K X)
       (= L Y)
       a!1
       (= A a!2)
       (or (not C) (and (= P R) (= O Q)))
       (or C (and (= P V) (= O W)))
       (not Q1)
       (= E D1)))
      )
      (top_step Q
          R
          S
          T
          U
          V
          W
          X
          Y
          Z
          A1
          B1
          C1
          D1
          E1
          F1
          G1
          H1
          I1
          J1
          K1
          L1
          M1
          N1
          O1
          P1
          Q1)
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        true
      )
      INIT_STATE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Bool) (F Int) (G Bool) (H Bool) (I Int) (J Bool) (K Bool) (L Int) (M Int) (N Bool) (O Bool) (P Int) (Q Int) (R Bool) (S Bool) (T Bool) (U Int) (V Bool) (W Bool) (X Int) (Y Bool) (Z Bool) (A1 Int) (B1 Int) (C1 Bool) (D1 Bool) (E1 Bool) (F1 Int) (G1 Bool) (H1 Bool) (I1 Int) (J1 Bool) (K1 Bool) (L1 Bool) ) 
    (=>
      (and
        (top_step L M N O L1 P Q R S T U V W X Y Z A1 B1 C1 D1 E1 F1 G1 H1 I1 J1 K1)
        INIT_STATE
        (top_reset A B C D E F G H I J K P Q R S T U V W X Y Z)
        true
      )
      (MAIN A1 B1 C1 D1 E1 F1 G1 H1 I1 J1 K1 L1)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Bool) (E Bool) (F Int) (G Int) (H Bool) (I Bool) (J Bool) (K Int) (L Bool) (M Bool) (N Int) (O Bool) (P Bool) (Q Int) (R Int) (S Bool) (T Bool) (U Bool) (V Int) (W Bool) (X Bool) (Y Int) (Z Bool) (A1 Bool) (B1 Bool) ) 
    (=>
      (and
        (top_step B C D E B1 F G H I J K L M N O P Q R S T U V W X Y Z A1)
        (MAIN F G H I J K L M N O P A)
        true
      )
      (MAIN Q R S T U V W X Y Z A1 B1)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Bool) (F Int) (G Bool) (H Bool) (I Int) (J Bool) (K Bool) (L Bool) ) 
    (=>
      (and
        (MAIN A B C D E F G H I J K L)
        (not L)
      )
      ERR
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        ERR
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
