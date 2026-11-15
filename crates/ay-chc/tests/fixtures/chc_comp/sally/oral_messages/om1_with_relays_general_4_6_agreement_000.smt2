(set-logic HORN)


(declare-fun |invariant| ( Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Real Real Real Real Real Real Real ) Bool)

(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Real) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) (V1 Real) (W1 Bool) (X1 Bool) (Y1 Bool) (Z1 Bool) (A2 Bool) (B2 Bool) (C2 Bool) (D2 Bool) (E2 Bool) (F2 Bool) (G2 Real) (H2 Real) (I2 Real) (J2 Real) (K2 Real) (L2 Real) (M2 Real) ) 
    (=>
      (and
        (and (= K2 0.0)
     (= V1 0.0)
     (= U1 0.0)
     (= T1 0.0)
     (= S1 0.0)
     (= R1 0.0)
     (= Q1 0.0)
     (= P1 0.0)
     (= O1 0.0)
     (= N1 0.0)
     (= M1 0.0)
     (= L1 0.0)
     (= K1 0.0)
     (= J1 0.0)
     (= I1 0.0)
     (= H1 0.0)
     (= G1 0.0)
     (= F1 0.0)
     (= E1 0.0)
     (= D1 0.0)
     (= C1 0.0)
     (= B1 0.0)
     (= A1 0.0)
     (= Z 0.0)
     (= Y 0.0)
     (= X 0.0)
     (= W 0.0)
     (= V 0.0)
     (= U 0.0)
     (= T 0.0)
     (= S 0.0)
     (= R 0.0)
     (= Q 0.0)
     (= P 0.0)
     (= O 0.0)
     (= N 0.0)
     (= M 0.0)
     (= L 0.0)
     (= K 0.0)
     (= J 0.0)
     (= I 0.0)
     (= H 0.0)
     (= G 0.0)
     (= F 0.0)
     (= E 0.0)
     (= D 0.0)
     (= C 0.0)
     (= B 0.0)
     (= A 0.0)
     (or (and (not A2) B2 C2 D2 E2 F2)
         (and A2 (not B2) C2 D2 E2 F2)
         (and A2 B2 (not C2) D2 E2 F2)
         (and A2 B2 C2 (not D2) E2 F2)
         (and A2 B2 C2 D2 (not E2) F2)
         (and A2 B2 C2 D2 E2 (not F2)))
     (or (= L2 1.0) (= L2 2.0) (= L2 3.0) (= L2 4.0))
     (= Z1 true)
     (= Y1 true)
     (= X1 true)
     (= W1 true)
     (not (= M2 0.0)))
      )
      (invariant A
           B
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
           E2
           F2
           G2
           H2
           I2
           J2
           K2
           L2
           M2)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Real) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) (V1 Real) (W1 Real) (X1 Real) (Y1 Real) (Z1 Real) (A2 Real) (B2 Real) (C2 Real) (D2 Real) (E2 Real) (F2 Real) (G2 Real) (H2 Real) (I2 Real) (J2 Real) (K2 Real) (L2 Real) (M2 Real) (N2 Real) (O2 Real) (P2 Real) (Q2 Real) (R2 Real) (S2 Real) (T2 Real) (U2 Real) (V2 Real) (W2 Real) (X2 Real) (Y2 Real) (Z2 Real) (A3 Real) (B3 Real) (C3 Real) (D3 Real) (E3 Real) (F3 Real) (G3 Real) (H3 Real) (I3 Real) (J3 Real) (K3 Real) (L3 Real) (M3 Real) (N3 Real) (O3 Real) (P3 Real) (Q3 Real) (R3 Real) (S3 Bool) (T3 Bool) (U3 Bool) (V3 Bool) (W3 Bool) (X3 Bool) (Y3 Bool) (Z3 Bool) (A4 Bool) (B4 Bool) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Bool) (L4 Bool) (M4 Real) (N4 Real) (O4 Real) (P4 Real) (Q4 Real) (R4 Real) (S4 Real) (T4 Real) (U4 Real) (V4 Real) (W4 Real) (X4 Real) (Y4 Real) (Z4 Real) ) 
    (=>
      (and
        (invariant A
           C
           E
           G
           I
           K
           M
           O
           Q
           S
           U
           W
           Y
           A1
           C1
           E1
           G1
           I1
           K1
           M1
           O1
           Q1
           S1
           U1
           W1
           Y1
           A2
           C2
           E2
           G2
           I2
           K2
           M2
           O2
           Q2
           S2
           U2
           W2
           Y2
           A3
           C3
           E3
           G3
           I3
           K3
           M3
           O3
           Q3
           S3
           U3
           W3
           Y3
           A4
           C4
           E4
           G4
           I4
           K4
           M4
           O4
           Q4
           S4
           U4
           W4
           Y4)
        (let ((a!1 (ite (= W4 4.0) U1 (ite (= W4 3.0) I1 (ite (= W4 2.0) W K))))
      (a!2 (ite (= W4 4.0) K1 (ite (= W4 3.0) Y (ite (= W4 2.0) M A))))
      (a!3 (ite (= W4 4.0) M1 (ite (= W4 3.0) A1 (ite (= W4 2.0) O C))))
      (a!4 (ite (= W4 4.0) O1 (ite (= W4 3.0) C1 (ite (= W4 2.0) Q E))))
      (a!5 (ite (= W4 4.0) Q1 (ite (= W4 3.0) E1 (ite (= W4 2.0) S G))))
      (a!6 (ite (= W4 4.0) S1 (ite (= W4 3.0) G1 (ite (= W4 2.0) U I))))
      (a!7 (and (or (not S3)
                    (and (= B Y4) (= D Y4) (= F Y4) (= H Y4) (= J Y4) (= L Y4))
                    (not (= 1.0 W4)))
                (or (not S3)
                    (= 1.0 W4)
                    (and (= B 0.0)
                         (= D 0.0)
                         (= F 0.0)
                         (= H 0.0)
                         (= J 0.0)
                         (= L 0.0)))
                (or (not U3)
                    (and (= N Y4) (= P Y4) (= R Y4) (= T Y4) (= V Y4) (= X Y4))
                    (not (= 2.0 W4)))
                (or (not U3)
                    (= 2.0 W4)
                    (and (= N 0.0)
                         (= P 0.0)
                         (= R 0.0)
                         (= T 0.0)
                         (= V 0.0)
                         (= X 0.0)))
                (or (not W3)
                    (and (= Z Y4)
                         (= B1 Y4)
                         (= D1 Y4)
                         (= F1 Y4)
                         (= H1 Y4)
                         (= J1 Y4))
                    (not (= 3.0 W4)))
                (or (not W3)
                    (= 3.0 W4)
                    (and (= Z 0.0)
                         (= B1 0.0)
                         (= D1 0.0)
                         (= F1 0.0)
                         (= H1 0.0)
                         (= J1 0.0)))
                (or (not Y3)
                    (and (= L1 Y4)
                         (= N1 Y4)
                         (= P1 Y4)
                         (= R1 Y4)
                         (= T1 Y4)
                         (= V1 Y4))
                    (not (= 4.0 W4)))
                (or (not Y3)
                    (= 4.0 W4)
                    (and (= L1 0.0)
                         (= N1 0.0)
                         (= P1 0.0)
                         (= R1 0.0)
                         (= T1 0.0)
                         (= V1 0.0)))
                (= N2 M2)
                (= P2 O2)
                (= R2 Q2)
                (= T2 S2)
                (= V2 U2)
                (= X2 W2)
                (= Z2 Y2)
                (= B3 A3)
                (= D3 C3)
                (= F3 E3)
                (= H3 G3)
                (= J3 I3)
                (= L3 K3)
                (= N3 M3)
                (= P3 O3)
                (= R3 Q3)
                (= T4 S4)
                (= U4 0.0)
                (= V4 1.0)
                (= X1 W1)
                (= Z1 Y1)
                (= B2 A2)
                (= D2 C2)
                (= F2 E2)
                (= H2 G2)
                (= J2 I2)
                (= L2 K2)
                (= N4 M4)
                (= P4 O4)
                (= R4 Q4)
                (= J4 I4)
                (= L4 K4)
                (= T3 S3)
                (= V3 U3)
                (= X3 W3)
                (= Z3 Y3)
                (= B4 A4)
                (= D4 C4)
                (= F4 E4)
                (= H4 G4)))
      (a!8 (ite (= C2 G2)
                (+ 1 (ite (= E2 G2) 2 0))
                (+ (- 1) (ite (= E2 G2) 2 0))))
      (a!21 (ite (= O2 S2)
                 (+ 1 (ite (= Q2 S2) 2 0))
                 (+ (- 1) (ite (= Q2 S2) 2 0))))
      (a!34 (ite (= A3 E3)
                 (+ 1 (ite (= C3 E3) 2 0))
                 (+ (- 1) (ite (= C3 E3) 2 0))))
      (a!47 (ite (= M3 Q3)
                 (+ 1 (ite (= O3 Q3) 2 0))
                 (+ (- 1) (ite (= O3 Q3) 2 0)))))
(let ((a!9 (ite (= A2 (ite (= E2 G2) G2 C2))
                (+ 1 (ite (= E2 G2) a!8 1))
                (+ (- 1) (ite (= E2 G2) a!8 1))))
      (a!10 (ite (and (= E2 G2) (= a!8 0)) A2 (ite (= E2 G2) G2 C2)))
      (a!22 (ite (= M2 (ite (= Q2 S2) S2 O2))
                 (+ 1 (ite (= Q2 S2) a!21 1))
                 (+ (- 1) (ite (= Q2 S2) a!21 1))))
      (a!23 (ite (and (= Q2 S2) (= a!21 0)) M2 (ite (= Q2 S2) S2 O2)))
      (a!35 (ite (= Y2 (ite (= C3 E3) E3 A3))
                 (+ 1 (ite (= C3 E3) a!34 1))
                 (+ (- 1) (ite (= C3 E3) a!34 1))))
      (a!36 (ite (and (= C3 E3) (= a!34 0)) Y2 (ite (= C3 E3) E3 A3)))
      (a!48 (ite (= K3 (ite (= O3 Q3) Q3 M3))
                 (+ 1 (ite (= O3 Q3) a!47 1))
                 (+ (- 1) (ite (= O3 Q3) a!47 1))))
      (a!49 (ite (and (= O3 Q3) (= a!47 0)) K3 (ite (= O3 Q3) Q3 M3))))
(let ((a!11 (ite (and (= E2 G2) (= a!8 0)) 1 a!9))
      (a!13 (and (or (not (= E2 G2)) (not (= a!8 0))) (= a!9 0)))
      (a!24 (ite (and (= Q2 S2) (= a!21 0)) 1 a!22))
      (a!26 (and (or (not (= Q2 S2)) (not (= a!21 0))) (= a!22 0)))
      (a!37 (ite (and (= C3 E3) (= a!34 0)) 1 a!35))
      (a!39 (and (or (not (= C3 E3)) (not (= a!34 0))) (= a!35 0)))
      (a!50 (ite (and (= O3 Q3) (= a!47 0)) 1 a!48))
      (a!52 (and (or (not (= O3 Q3)) (not (= a!47 0))) (= a!48 0))))
(let ((a!12 (and (or (and (= E2 G2) (= a!8 0)) (not (= a!9 0)))
                 (= (ite (= Y1 a!10) (+ 1 a!11) (+ (- 1) a!11)) 0)))
      (a!25 (and (or (and (= Q2 S2) (= a!21 0)) (not (= a!22 0)))
                 (= (ite (= K2 a!23) (+ 1 a!24) (+ (- 1) a!24)) 0)))
      (a!38 (and (or (and (= C3 E3) (= a!34 0)) (not (= a!35 0)))
                 (= (ite (= W2 a!36) (+ 1 a!37) (+ (- 1) a!37)) 0)))
      (a!51 (and (or (and (= O3 Q3) (= a!47 0)) (not (= a!48 0)))
                 (= (ite (= I3 a!49) (+ 1 a!50) (+ (- 1) a!50)) 0))))
(let ((a!14 (ite (= G2 (ite a!12 W1 (ite a!13 Y1 a!10))) 3 4))
      (a!27 (ite (= S2 (ite a!25 I2 (ite a!26 K2 a!23))) 3 4))
      (a!40 (ite (= E3 (ite a!38 U2 (ite a!39 W2 a!36))) 3 4))
      (a!53 (ite (= Q3 (ite a!51 G3 (ite a!52 I3 a!49))) 3 4)))
(let ((a!15 (ite (= E2 (ite a!12 W1 (ite a!13 Y1 a!10))) (+ (- 1) a!14) a!14))
      (a!28 (ite (= Q2 (ite a!25 I2 (ite a!26 K2 a!23))) (+ (- 1) a!27) a!27))
      (a!41 (ite (= C3 (ite a!38 U2 (ite a!39 W2 a!36))) (+ (- 1) a!40) a!40))
      (a!54 (ite (= O3 (ite a!51 G3 (ite a!52 I3 a!49))) (+ (- 1) a!53) a!53)))
(let ((a!16 (ite (= C2 (ite a!12 W1 (ite a!13 Y1 a!10))) (+ (- 1) a!15) a!15))
      (a!29 (ite (= O2 (ite a!25 I2 (ite a!26 K2 a!23))) (+ (- 1) a!28) a!28))
      (a!42 (ite (= A3 (ite a!38 U2 (ite a!39 W2 a!36))) (+ (- 1) a!41) a!41))
      (a!55 (ite (= M3 (ite a!51 G3 (ite a!52 I3 a!49))) (+ (- 1) a!54) a!54)))
(let ((a!17 (ite (= A2 (ite a!12 W1 (ite a!13 Y1 a!10))) (+ (- 1) a!16) a!16))
      (a!30 (ite (= M2 (ite a!25 I2 (ite a!26 K2 a!23))) (+ (- 1) a!29) a!29))
      (a!43 (ite (= Y2 (ite a!38 U2 (ite a!39 W2 a!36))) (+ (- 1) a!42) a!42))
      (a!56 (ite (= K3 (ite a!51 G3 (ite a!52 I3 a!49))) (+ (- 1) a!55) a!55)))
(let ((a!18 (ite (= Y1 (ite a!12 W1 (ite a!13 Y1 a!10))) (+ (- 1) a!17) a!17))
      (a!31 (ite (= K2 (ite a!25 I2 (ite a!26 K2 a!23))) (+ (- 1) a!30) a!30))
      (a!44 (ite (= W2 (ite a!38 U2 (ite a!39 W2 a!36))) (+ (- 1) a!43) a!43))
      (a!57 (ite (= I3 (ite a!51 G3 (ite a!52 I3 a!49))) (+ (- 1) a!56) a!56)))
(let ((a!19 (ite (= W1 (ite a!12 W1 (ite a!13 Y1 a!10))) (= a!18 1) (= a!18 0)))
      (a!32 (ite (= I2 (ite a!25 I2 (ite a!26 K2 a!23))) (= a!31 1) (= a!31 0)))
      (a!45 (ite (= U2 (ite a!38 U2 (ite a!39 W2 a!36))) (= a!44 1) (= a!44 0)))
      (a!58 (ite (= G3 (ite a!51 G3 (ite a!52 I3 a!49))) (= a!57 1) (= a!57 0))))
(let ((a!20 (= N4
               (ite (or (= a!16 0) (= a!17 0) (= a!18 0) a!19)
                    (ite a!12 W1 (ite a!13 Y1 a!10))
                    0.0)))
      (a!33 (= P4
               (ite (or (= a!29 0) (= a!30 0) (= a!31 0) a!32)
                    (ite a!25 I2 (ite a!26 K2 a!23))
                    0.0)))
      (a!46 (= R4
               (ite (or (= a!42 0) (= a!43 0) (= a!44 0) a!45)
                    (ite a!38 U2 (ite a!39 W2 a!36))
                    0.0)))
      (a!59 (= T4
               (ite (or (= a!55 0) (= a!56 0) (= a!57 0) a!58)
                    (ite a!51 G3 (ite a!52 I3 a!49))
                    0.0))))
(let ((a!60 (or (and (or (not K4) (= T2 a!1))
                     (or (not K4) (= F3 a!1))
                     (or (not K4) (= R3 a!1))
                     (or (not K4) (= H2 a!1))
                     (or (not A4) (= V2 a!2))
                     (or (not A4) (= H3 a!2))
                     (or (not A4) (= X1 a!2))
                     (or (not A4) (= J2 a!2))
                     (or (not C4) (= X2 a!3))
                     (or (not C4) (= J3 a!3))
                     (or (not C4) (= Z1 a!3))
                     (or (not C4) (= L2 a!3))
                     (or (not E4) (= N2 a!4))
                     (or (not E4) (= Z2 a!4))
                     (or (not E4) (= L3 a!4))
                     (or (not E4) (= B2 a!4))
                     (or (not G4) (= P2 a!5))
                     (or (not G4) (= B3 a!5))
                     (or (not G4) (= N3 a!5))
                     (or (not G4) (= D2 a!5))
                     (or (not I4) (= R2 a!6))
                     (or (not I4) (= D3 a!6))
                     (or (not I4) (= P3 a!6))
                     (or (not I4) (= F2 a!6))
                     (= T4 S4)
                     (= U4 1.0)
                     (= V4 2.0)
                     (= B A)
                     (= D C)
                     (= F E)
                     (= H G)
                     (= J I)
                     (= L K)
                     (= N M)
                     (= P O)
                     (= R Q)
                     (= T S)
                     (= V U)
                     (= X W)
                     (= Z Y)
                     (= B1 A1)
                     (= D1 C1)
                     (= F1 E1)
                     (= H1 G1)
                     (= J1 I1)
                     (= L1 K1)
                     (= N1 M1)
                     (= P1 O1)
                     (= R1 Q1)
                     (= T1 S1)
                     (= V1 U1)
                     (= N4 M4)
                     (= P4 O4)
                     (= R4 Q4)
                     (= J4 I4)
                     (= L4 K4)
                     (= T3 S3)
                     (= V3 U3)
                     (= X3 W3)
                     (= Z3 Y3)
                     (= B4 A4)
                     (= D4 C4)
                     (= F4 E4)
                     (= H4 G4))
                (and (= N2 M2)
                     (= P2 O2)
                     (= R2 Q2)
                     (= T2 S2)
                     (= V2 U2)
                     (= X2 W2)
                     (= Z2 Y2)
                     (= B3 A3)
                     (= D3 C3)
                     (= F3 E3)
                     (= H3 G3)
                     (= J3 I3)
                     (= L3 K3)
                     (= N3 M3)
                     (= P3 O3)
                     (= R3 Q3)
                     (= T4 S4)
                     (= U4 3.0)
                     (= V4 U4)
                     (= B A)
                     (= D C)
                     (= F E)
                     (= H G)
                     (= J I)
                     (= L K)
                     (= N M)
                     (= P O)
                     (= R Q)
                     (= T S)
                     (= V U)
                     (= X W)
                     (= Z Y)
                     (= B1 A1)
                     (= D1 C1)
                     (= F1 E1)
                     (= H1 G1)
                     (= J1 I1)
                     (= L1 K1)
                     (= N1 M1)
                     (= P1 O1)
                     (= R1 Q1)
                     (= T1 S1)
                     (= V1 U1)
                     (= X1 W1)
                     (= Z1 Y1)
                     (= B2 A2)
                     (= D2 C2)
                     (= F2 E2)
                     (= H2 G2)
                     (= J2 I2)
                     (= L2 K2)
                     (= N4 M4)
                     (= P4 O4)
                     (= R4 Q4)
                     (= J4 I4)
                     (= L4 K4)
                     (= T3 S3)
                     (= V3 U3)
                     (= X3 W3)
                     (= Z3 Y3)
                     (= B4 A4)
                     (= D4 C4)
                     (= F4 E4)
                     (= H4 G4))
                a!7
                (and (or (not S3) a!20)
                     (or (not U3) a!33)
                     (or (not W3) a!46)
                     (or (not Y3) a!59)
                     (= N2 M2)
                     (= P2 O2)
                     (= R2 Q2)
                     (= T2 S2)
                     (= V2 U2)
                     (= X2 W2)
                     (= Z2 Y2)
                     (= B3 A3)
                     (= D3 C3)
                     (= F3 E3)
                     (= H3 G3)
                     (= J3 I3)
                     (= L3 K3)
                     (= N3 M3)
                     (= P3 O3)
                     (= R3 Q3)
                     (= U4 2.0)
                     (= V4 3.0)
                     (= B A)
                     (= D C)
                     (= F E)
                     (= H G)
                     (= J I)
                     (= L K)
                     (= N M)
                     (= P O)
                     (= R Q)
                     (= T S)
                     (= V U)
                     (= X W)
                     (= Z Y)
                     (= B1 A1)
                     (= D1 C1)
                     (= F1 E1)
                     (= H1 G1)
                     (= J1 I1)
                     (= L1 K1)
                     (= N1 M1)
                     (= P1 O1)
                     (= R1 Q1)
                     (= T1 S1)
                     (= V1 U1)
                     (= X1 W1)
                     (= Z1 Y1)
                     (= B2 A2)
                     (= D2 C2)
                     (= F2 E2)
                     (= H2 G2)
                     (= J2 I2)
                     (= L2 K2)
                     (= J4 I4)
                     (= L4 K4)
                     (= T3 S3)
                     (= V3 U3)
                     (= X3 W3)
                     (= Z3 Y3)
                     (= B4 A4)
                     (= D4 C4)
                     (= F4 E4)
                     (= H4 G4)))))
  (and (= X4 W4) a!60 (= Z4 Y4))))))))))))))
      )
      (invariant B
           D
           F
           H
           J
           L
           N
           P
           R
           T
           V
           X
           Z
           B1
           D1
           F1
           H1
           J1
           L1
           N1
           P1
           R1
           T1
           V1
           X1
           Z1
           B2
           D2
           F2
           H2
           J2
           L2
           N2
           P2
           R2
           T2
           V2
           X2
           Z2
           B3
           D3
           F3
           H3
           J3
           L3
           N3
           P3
           R3
           T3
           V3
           X3
           Z3
           B4
           D4
           F4
           H4
           J4
           L4
           N4
           P4
           R4
           T4
           V4
           X4
           Z4)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Real) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) (V1 Real) (W1 Bool) (X1 Bool) (Y1 Bool) (Z1 Bool) (A2 Bool) (B2 Bool) (C2 Bool) (D2 Bool) (E2 Bool) (F2 Bool) (G2 Real) (H2 Real) (I2 Real) (J2 Real) (K2 Real) (L2 Real) (M2 Real) ) 
    (=>
      (and
        (invariant A
           B
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
           E2
           F2
           G2
           H2
           I2
           J2
           K2
           L2
           M2)
        (let ((a!1 (or (and X1 (not (= G2 H2)))
               (and Y1 (not (= G2 I2)))
               (and Z1 (not (= G2 J2)))))
      (a!2 (or (and W1 (not (= H2 G2)))
               (and Y1 (not (= H2 I2)))
               (and Z1 (not (= H2 J2)))))
      (a!3 (or (and W1 (not (= I2 G2)))
               (and X1 (not (= I2 H2)))
               (and Z1 (not (= I2 J2)))))
      (a!4 (or (and W1 (not (= J2 G2)))
               (and X1 (not (= J2 H2)))
               (and Y1 (not (= J2 I2))))))
  (and (or (and W1 a!1) (and X1 a!2) (and Y1 a!3) (and Z1 a!4)) (<= 3.0 K2)))
      )
      false
    )
  )
)

(check-sat)
(exit)
