(set-logic HORN)


(declare-fun |ERR| ( ) Bool)
(declare-fun |top_step| ( Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Bool Int Bool Int Int Int Int Int Int Bool Bool Bool Int Bool Int Int Int Int Int Int Bool Bool Bool ) Bool)
(declare-fun |DRAGON_reset| ( Int Int Int Int Int Int Bool Int Int Int Int Int Int Bool ) Bool)
(declare-fun |MAIN| ( Int Bool Int Int Int Int Int Int Bool Bool Bool Bool ) Bool)
(declare-fun |excludes12_fun| ( Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool ) Bool)
(declare-fun |INIT_STATE| ( ) Bool)
(declare-fun |DRAGON_step| ( Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Int Int Int Bool Int Int Int Int Int Int Bool Int Int Int Int Int Int Bool ) Bool)
(declare-fun |Sofar_step| ( Bool Bool Bool Bool Bool Bool ) Bool)
(declare-fun |First_step| ( Int Int Int Bool Int Bool ) Bool)
(declare-fun |top_reset| ( Int Bool Int Int Int Int Int Int Bool Bool Bool Int Bool Int Int Int Int Int Int Bool Bool Bool ) Bool)
(declare-fun |Sofar_reset| ( Bool Bool Bool Bool ) Bool)
(declare-fun |First_reset| ( Int Bool Int Bool ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Bool) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Bool) ) 
    (=>
      (and
        (and (= I B) (= J C) (= K D) (= L E) (= M F) (= N true) (= H A))
      )
      (DRAGON_reset A B C D E F G H I J K L M N)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Int) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Bool) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Bool) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Bool) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Bool) ) 
    (=>
      (and
        (let ((a!1 (and (>= I1 1) (= M1 0) (= L1 0) (= K1 0) (= J1 0)))
      (a!2 (and (>= I1 1) (>= (+ J1 M1 L1 K1) 1)))
      (a!3 (and (or C (= D1 M1)) (or (not C) (= D1 (+ (- 1) M1)))))
      (a!5 (and (or M (= D1 M1)) (or (not M) (= D1 (+ M1 L1 K1 J1)))))
      (a!7 (and (or (= D1 M1) B) (or (not B) (= D1 (+ (- 1) M1 K1)))))
      (a!9 (or (not T) (and (or K (= D1 M1)) (or (not K) (= D1 0)))))
      (a!10 (and (or H (= D1 M1)) (or (not H) (= D1 (+ 1 M1 L1)))))
      (a!12 (and (or F (= G1 I1)) (or (not F) (= G1 (+ 1 I1)))))
      (a!14 (and (or (= G1 I1) D) (or (not D) (= G1 (+ 1 I1)))))
      (a!16 (and (or (= G1 I1) C) (or (not C) (= G1 (+ 1 I1)))))
      (a!18 (and (or N (= G1 I1)) (or (not N) (= G1 (+ 1 I1)))))
      (a!20 (and (or M (= G1 I1)) (or (not M) (= G1 (+ (- 1) I1)))))
      (a!22 (and (or L (= G1 I1)) (or (not L) (= G1 (+ (- 1) I1)))))
      (a!24 (and (or H (= G1 I1)) (or (not H) (= G1 (+ (- 1) I1)))))
      (a!26 (and (or E (= G1 I1)) (or (not E) (= G1 (+ (- 1) I1)))))
      (a!28 (and (or (= C1 L1) F) (or (not F) (= C1 (+ (- 1) L1)))))
      (a!30 (or (not W) (and (or M (= C1 L1)) (or (not M) (= C1 0)))))
      (a!31 (and (or I (= C1 L1)) (or (not I) (= C1 (+ (- 1) L1)))))
      (a!33 (or (not Q) (and (or H (= C1 L1)) (or (not H) (= C1 0)))))
      (a!34 (and (or (= C1 L1) E) (or (not E) (= C1 (+ 1 L1)))))
      (a!36 (and (or D (= E1 K1)) (or (not D) (= E1 (+ (- 1) K1)))))
      (a!38 (or (not W) (and (or M (= E1 K1)) (or (not M) (= E1 1)))))
      (a!39 (or (not U) (and (or B (= E1 K1)) (or (not B) (= E1 1)))))
      (a!41 (or (not S) (and (or J (= E1 K1)) (or (not J) (= E1 0)))))
      (a!42 (and (or H (= E1 K1)) (or (not H) (= E1 (+ K1 J1)))))
      (a!44 (and (or (= F1 J1) N) (or (not N) (= F1 (+ (- 1) J1)))))
      (a!46 (or (not W) (and (or (= F1 J1) M) (or (not M) (= F1 0)))))
      (a!47 (and (or (= F1 J1) L) (or (not L) (= F1 (+ 1 J1)))))
      (a!49 (and (or (= F1 J1) K) (or (not K) (= F1 (+ 1 J1)))))
      (a!51 (and (or (= F1 J1) J) (or (not J) (= F1 (+ 1 J1)))))
      (a!53 (and (or (= F1 J1) I) (or (not I) (= F1 (+ 1 J1)))))
      (a!55 (or (not Q) (and (or (= F1 J1) H) (or (not H) (= F1 0))))))
(let ((a!4 (or W (and (or (not Y) a!3) (or Y (= D1 M1)))))
      (a!13 (or Z (and (or (not A1) a!12) (or A1 (= G1 I1)))))
      (a!29 (or W (and (or (not A1) a!28) (or A1 (= C1 L1)))))
      (a!37 (or W (and (or (not Z) a!36) (or Z (= E1 K1)))))
      (a!45 (or W (and (or (not X) a!44) (or X (= F1 J1))))))
(let ((a!6 (or U (and a!4 (or (not W) a!5))))
      (a!15 (or Y (and a!13 (or (not Z) a!14))))
      (a!32 (or Q (and (or R (and a!29 a!30)) (or (not R) a!31))))
      (a!40 (or S (and (or U (and a!37 a!38)) a!39)))
      (a!48 (or T (and (or V (and a!45 a!46)) (or (not V) a!47)))))
(let ((a!8 (or T (and a!6 (or (not U) a!7))))
      (a!17 (or X (and a!15 (or (not Y) a!16))))
      (a!35 (or G (and (or P (and a!32 a!33)) (or (not P) a!34))))
      (a!43 (or G (and (or Q (and a!40 a!41)) (or (not Q) a!42))))
      (a!50 (or S (and a!48 (or (not T) a!49)))))
(let ((a!11 (or G (and (or Q (and a!8 a!9)) (or (not Q) a!10) (= O N1))))
      (a!19 (or W (and a!17 (or (not X) a!18))))
      (a!52 (or R (and a!50 (or (not S) a!51)))))
(let ((a!21 (or V (and a!19 (or (not W) a!20))))
      (a!54 (or Q (and a!52 (or (not R) a!53)))))
(let ((a!23 (or Q (and a!21 (or (not V) a!22)))))
(let ((a!25 (or P (and a!23 (or (not Q) a!24)))))
(let ((a!27 (or G (and a!25 (or (not P) a!26)))))
  (and (= B (>= (+ K1 M1) 2))
       (= C (>= M1 1))
       (= D (>= K1 1))
       (= E a!1)
       (= F (>= L1 1))
       (= G A)
       (= H a!2)
       (= I (>= L1 1))
       (= J (and (= M1 0) (= K1 1)))
       (= K (and (= M1 1) (= K1 0)))
       (= L a!1)
       (= M a!2)
       (= N (>= J1 1))
       (= H1 (>= C1 2))
       (= P1 G1)
       (= Q1 F1)
       (= R1 E1)
       (= S1 C1)
       (= T1 D1)
       (= U1 O)
       (or (not G) (= C1 0))
       (or (not G) (= E1 0))
       (or (not G) (= F1 0))
       (or (not G) (= G1 O))
       a!11
       (or (not G) (and (= D1 0) (= O B1)))
       a!27
       a!35
       a!43
       (or G (and a!54 a!55))
       (not V1)
       (= A O1)))))))))))
      )
      (DRAGON_step P
             Q
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
             Q1
             R1
             S1
             T1
             U1
             V1)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) ) 
    (=>
      (and
        (and (= D true) (= C A))
      )
      (First_reset A B C D)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Int) (E Int) (F Bool) (G Int) (H Bool) ) 
    (=>
      (and
        (and (= A F) (= G D) (or (not B) (= D C)) (or (= D E) B) (not H) (= B A))
      )
      (First_step C D E F G H)
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
        (and (= G D) (= A F) (or B (= D (or E C))) (or (not B) (= D C)) (not H) (= B A))
      )
      (Sofar_step C D E F G H)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) ) 
    (=>
      (and
        (= M
   (or (and (not F)
            (not K)
            (not L)
            (not J)
            (not G)
            (not I)
            (not H)
            (not E)
            (not D)
            (not C)
            (not B)
            (not A))
       (and (not F)
            (not K)
            (not L)
            (not J)
            (not G)
            (not I)
            (not H)
            (not E)
            (not D)
            (not C)
            (not B)
            A)
       (and (not F)
            (not K)
            (not L)
            (not J)
            (not G)
            (not I)
            (not H)
            (not E)
            (not D)
            (not C)
            B
            (not A))
       (and (not F)
            (not K)
            (not L)
            (not J)
            (not G)
            (not I)
            (not H)
            (not E)
            (not D)
            C
            (not B)
            (not A))
       (and (not F)
            (not K)
            (not L)
            (not J)
            (not G)
            (not I)
            (not H)
            (not E)
            D
            (not C)
            (not B)
            (not A))
       (and (not F)
            (not K)
            (not L)
            (not J)
            (not G)
            (not I)
            (not H)
            E
            (not D)
            (not C)
            (not B)
            (not A))
       (and (not F)
            (not K)
            (not L)
            (not J)
            (not G)
            (not I)
            H
            (not E)
            (not D)
            (not C)
            (not B)
            (not A))
       (and (not F)
            (not K)
            (not L)
            (not J)
            (not G)
            I
            (not H)
            (not E)
            (not D)
            (not C)
            (not B)
            (not A))
       (and (not F)
            (not K)
            (not L)
            (not J)
            G
            (not I)
            (not H)
            (not E)
            (not D)
            (not C)
            (not B)
            (not A))
       (and (not F)
            (not K)
            (not L)
            J
            (not G)
            (not I)
            (not H)
            (not E)
            (not D)
            (not C)
            (not B)
            (not A))
       (and (not F)
            (not K)
            L
            (not J)
            (not G)
            (not I)
            (not H)
            (not E)
            (not D)
            (not C)
            (not B)
            (not A))
       (and (not F)
            K
            (not L)
            (not J)
            (not G)
            (not I)
            (not H)
            (not E)
            (not D)
            (not C)
            (not B)
            (not A))
       (and F
            (not K)
            (not L)
            (not J)
            (not G)
            (not I)
            (not H)
            (not E)
            (not D)
            (not C)
            (not B)
            (not A))))
      )
      (excludes12_fun A B C D E F G H I J K L M)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Bool) (J Bool) (K Bool) (L Int) (M Bool) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Bool) (U Bool) (V Bool) ) 
    (=>
      (and
        (First_reset A B L M)
        (Sofar_reset J K U V)
        (DRAGON_reset C D E F G H I N O P Q R S T)
        true
      )
      (top_reset A B C D E F G H I J K L M N O P Q R S T U V)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Int) (F Int) (G Int) (H Int) (I Bool) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Bool) (Q Int) (R Bool) (S Bool) (T Int) (U Int) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Bool) (B1 Bool) (C1 Bool) (D1 Bool) (E1 Bool) (F1 Bool) (G1 Bool) (H1 Int) (I1 Bool) (J1 Int) (K1 Bool) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Bool) (S1 Bool) (T1 Bool) (U1 Int) (V1 Bool) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Bool) (D2 Bool) (E2 Bool) ) 
    (=>
      (and
        (excludes12_fun V W X Y Z A1 B1 C1 D1 E1 F1 G1 B)
        (Sofar_step A S C D D2 E2)
        (DRAGON_step V
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
             E
             F
             G
             T
             H
             I
             J
             K
             L
             M
             N
             O
             P
             W1
             X1
             Y1
             Z1
             A2
             B2
             C2)
        (First_step H1 U Q R U1 V1)
        (let ((a!1 (= A (and B (not (<= H1 0))))))
  (and (= R K1)
       (= I1 (or (not S) (<= T U)))
       (= C S1)
       (= D T1)
       a!1
       (= J L1)
       (= K M1)
       (= L N1)
       (= M O1)
       (= N P1)
       (= O Q1)
       (= Q J1)
       (= P R1)))
      )
      (top_step V
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
          Q1
          R1
          S1
          T1
          U1
          V1
          W1
          X1
          Y1
          Z1
          A2
          B2
          C2
          D2
          E2)
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
  (forall ( (A Int) (B Bool) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Int) (Y Int) (Z Bool) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Bool) (H1 Bool) (I1 Bool) (J1 Int) (K1 Bool) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Bool) (S1 Bool) (T1 Bool) (U1 Bool) ) 
    (=>
      (and
        (top_step L
          M
          N
          O
          P
          Q
          R
          S
          T
          U
          V
          W
          X
          U1
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
          Q1
          R1
          S1
          T1)
        INIT_STATE
        (top_reset A B C D E F G H I J K Y Z A1 B1 C1 D1 E1 F1 G1 H1 I1)
        true
      )
      (MAIN J1 K1 L1 M1 N1 O1 P1 Q1 R1 S1 T1 U1)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Int) (O Int) (P Bool) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Bool) (X Bool) (Y Bool) (Z Int) (A1 Bool) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Bool) (I1 Bool) (J1 Bool) (K1 Bool) ) 
    (=>
      (and
        (top_step B
          C
          D
          E
          F
          G
          H
          I
          J
          K
          L
          M
          N
          K1
          O
          P
          Q
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
          J1)
        (MAIN O P Q R S T U V W X Y A)
        true
      )
      (MAIN Z A1 B1 C1 D1 E1 F1 G1 H1 I1 J1 K1)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Bool) (J Bool) (K Bool) (L Bool) ) 
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
