(set-logic HORN)


(declare-fun |invariant| ( Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Real Real Real Real Real Real ) Bool)

(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Real) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) (V1 Real) (W1 Real) (X1 Real) (Y1 Real) (Z1 Real) (A2 Real) (B2 Real) (C2 Real) (D2 Real) (E2 Real) (F2 Real) (G2 Real) (H2 Real) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Bool) (P2 Bool) (Q2 Bool) (R2 Bool) (S2 Bool) (T2 Bool) (U2 Bool) (V2 Real) (W2 Real) (X2 Real) (Y2 Real) (Z2 Real) (A3 Real) ) 
    (=>
      (and
        (and (= Y2 0.0)
     (= H2 0.0)
     (= G2 0.0)
     (= F2 0.0)
     (= E2 0.0)
     (= D2 0.0)
     (= C2 0.0)
     (= B2 0.0)
     (= A2 0.0)
     (= Z1 0.0)
     (= Y1 0.0)
     (= X1 0.0)
     (= W1 0.0)
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
     (or (and (not L2) M2 N2 O2 P2 Q2 R2 S2 T2 U2)
         (and L2 (not M2) N2 O2 P2 Q2 R2 S2 T2 U2)
         (and L2 M2 (not N2) O2 P2 Q2 R2 S2 T2 U2)
         (and L2 M2 N2 (not O2) P2 Q2 R2 S2 T2 U2)
         (and L2 M2 N2 O2 (not P2) Q2 R2 S2 T2 U2)
         (and L2 M2 N2 O2 P2 (not Q2) R2 S2 T2 U2)
         (and L2 M2 N2 O2 P2 Q2 (not R2) S2 T2 U2)
         (and L2 M2 N2 O2 P2 Q2 R2 (not S2) T2 U2)
         (and L2 M2 N2 O2 P2 Q2 R2 S2 (not T2) U2)
         (and L2 M2 N2 O2 P2 Q2 R2 S2 T2 (not U2)))
     (or (= Z2 1.0) (= Z2 2.0) (= Z2 3.0))
     (= K2 true)
     (= J2 true)
     (= I2 true)
     (not (= A3 0.0)))
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
           M2
           N2
           O2
           P2
           Q2
           R2
           S2
           T2
           U2
           V2
           W2
           X2
           Y2
           Z2
           A3)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Real) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) (V1 Real) (W1 Real) (X1 Real) (Y1 Real) (Z1 Real) (A2 Real) (B2 Real) (C2 Real) (D2 Real) (E2 Real) (F2 Real) (G2 Real) (H2 Real) (I2 Real) (J2 Real) (K2 Real) (L2 Real) (M2 Real) (N2 Real) (O2 Real) (P2 Real) (Q2 Real) (R2 Real) (S2 Real) (T2 Real) (U2 Real) (V2 Real) (W2 Real) (X2 Real) (Y2 Real) (Z2 Real) (A3 Real) (B3 Real) (C3 Real) (D3 Real) (E3 Real) (F3 Real) (G3 Real) (H3 Real) (I3 Real) (J3 Real) (K3 Real) (L3 Real) (M3 Real) (N3 Real) (O3 Real) (P3 Real) (Q3 Real) (R3 Real) (S3 Real) (T3 Real) (U3 Real) (V3 Real) (W3 Real) (X3 Real) (Y3 Real) (Z3 Real) (A4 Real) (B4 Real) (C4 Real) (D4 Real) (E4 Real) (F4 Real) (G4 Real) (H4 Real) (I4 Real) (J4 Real) (K4 Real) (L4 Real) (M4 Real) (N4 Real) (O4 Real) (P4 Real) (Q4 Bool) (R4 Bool) (S4 Bool) (T4 Bool) (U4 Bool) (V4 Bool) (W4 Bool) (X4 Bool) (Y4 Bool) (Z4 Bool) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Bool) (J5 Bool) (K5 Bool) (L5 Bool) (M5 Bool) (N5 Bool) (O5 Bool) (P5 Bool) (Q5 Real) (R5 Real) (S5 Real) (T5 Real) (U5 Real) (V5 Real) (W5 Real) (X5 Real) (Y5 Real) (Z5 Real) (A6 Real) (B6 Real) ) 
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
           Y4
           A5
           C5
           E5
           G5
           I5
           K5
           M5
           O5
           Q5
           S5
           U5
           W5
           Y5
           A6)
        (let ((a!1 (ite (= Y5 3.0) C2 (ite (= Y5 2.0) I1 O)))
      (a!2 (ite (= Y5 3.0) E2 (ite (= Y5 2.0) K1 Q)))
      (a!3 (ite (= Y5 3.0) G2 (ite (= Y5 2.0) M1 S)))
      (a!4 (ite (= Y5 3.0) O1 (ite (= Y5 2.0) U A)))
      (a!5 (ite (= Y5 3.0) Q1 (ite (= Y5 2.0) W C)))
      (a!6 (ite (= Y5 3.0) S1 (ite (= Y5 2.0) Y E)))
      (a!7 (ite (= Y5 3.0) U1 (ite (= Y5 2.0) A1 G)))
      (a!8 (ite (= Y5 3.0) W1 (ite (= Y5 2.0) C1 I)))
      (a!9 (ite (= Y5 3.0) Y1 (ite (= Y5 2.0) E1 K)))
      (a!10 (ite (= Y5 3.0) A2 (ite (= Y5 2.0) G1 M)))
      (a!11 (and (or (not Q4)
                     (and (= B A6)
                          (= D A6)
                          (= F A6)
                          (= H A6)
                          (= J A6)
                          (= L A6)
                          (= N A6)
                          (= P A6)
                          (= R A6)
                          (= T A6))
                     (not (= 1.0 Y5)))
                 (or (not Q4)
                     (= 1.0 Y5)
                     (and (= B 0.0)
                          (= D 0.0)
                          (= F 0.0)
                          (= H 0.0)
                          (= J 0.0)
                          (= L 0.0)
                          (= N 0.0)
                          (= P 0.0)
                          (= R 0.0)
                          (= T 0.0)))
                 (or (not S4)
                     (and (= V A6)
                          (= X A6)
                          (= Z A6)
                          (= B1 A6)
                          (= D1 A6)
                          (= F1 A6)
                          (= H1 A6)
                          (= J1 A6)
                          (= L1 A6)
                          (= N1 A6))
                     (not (= 2.0 Y5)))
                 (or (not S4)
                     (= 2.0 Y5)
                     (and (= V 0.0)
                          (= X 0.0)
                          (= Z 0.0)
                          (= B1 0.0)
                          (= D1 0.0)
                          (= F1 0.0)
                          (= H1 0.0)
                          (= J1 0.0)
                          (= L1 0.0)
                          (= N1 0.0)))
                 (or (not U4)
                     (and (= P1 A6)
                          (= R1 A6)
                          (= T1 A6)
                          (= V1 A6)
                          (= X1 A6)
                          (= Z1 A6)
                          (= B2 A6)
                          (= D2 A6)
                          (= F2 A6)
                          (= H2 A6))
                     (not (= 3.0 Y5)))
                 (or (not U4)
                     (= 3.0 Y5)
                     (and (= P1 0.0)
                          (= R1 0.0)
                          (= T1 0.0)
                          (= V1 0.0)
                          (= X1 0.0)
                          (= Z1 0.0)
                          (= B2 0.0)
                          (= D2 0.0)
                          (= F2 0.0)
                          (= H2 0.0)))
                 (= B3 A3)
                 (= D3 C3)
                 (= F3 E3)
                 (= H3 G3)
                 (= J3 I3)
                 (= L3 K3)
                 (= N3 M3)
                 (= P3 O3)
                 (= R3 Q3)
                 (= T3 S3)
                 (= V3 U3)
                 (= X3 W3)
                 (= Z3 Y3)
                 (= B4 A4)
                 (= D4 C4)
                 (= F4 E4)
                 (= H4 G4)
                 (= J4 I4)
                 (= L4 K4)
                 (= N4 M4)
                 (= P4 O4)
                 (= W5 0.0)
                 (= X5 1.0)
                 (= J2 I2)
                 (= L2 K2)
                 (= N2 M2)
                 (= P2 O2)
                 (= R2 Q2)
                 (= T2 S2)
                 (= V2 U2)
                 (= X2 W2)
                 (= Z2 Y2)
                 (= R5 Q5)
                 (= T5 S5)
                 (= V5 U5)
                 (= J5 I5)
                 (= L5 K5)
                 (= N5 M5)
                 (= P5 O5)
                 (= R4 Q4)
                 (= T4 S4)
                 (= V4 U4)
                 (= X4 W4)
                 (= Z4 Y4)
                 (= B5 A5)
                 (= D5 C5)
                 (= F5 E5)
                 (= H5 G5)))
      (a!12 (ite (= W2 A3)
                 (+ 1 (ite (= Y2 A3) 2 0))
                 (+ (- 1) (ite (= Y2 A3) 2 0))))
      (a!36 (ite (= Q3 U3)
                 (+ 1 (ite (= S3 U3) 2 0))
                 (+ (- 1) (ite (= S3 U3) 2 0))))
      (a!60 (ite (= K4 O4)
                 (+ 1 (ite (= M4 O4) 2 0))
                 (+ (- 1) (ite (= M4 O4) 2 0)))))
(let ((a!13 (ite (= U2 (ite (= Y2 A3) A3 W2))
                 (+ 1 (ite (= Y2 A3) a!12 1))
                 (+ (- 1) (ite (= Y2 A3) a!12 1))))
      (a!14 (ite (and (= Y2 A3) (= a!12 0)) U2 (ite (= Y2 A3) A3 W2)))
      (a!37 (ite (= O3 (ite (= S3 U3) U3 Q3))
                 (+ 1 (ite (= S3 U3) a!36 1))
                 (+ (- 1) (ite (= S3 U3) a!36 1))))
      (a!38 (ite (and (= S3 U3) (= a!36 0)) O3 (ite (= S3 U3) U3 Q3)))
      (a!61 (ite (= I4 (ite (= M4 O4) O4 K4))
                 (+ 1 (ite (= M4 O4) a!60 1))
                 (+ (- 1) (ite (= M4 O4) a!60 1))))
      (a!62 (ite (and (= M4 O4) (= a!60 0)) I4 (ite (= M4 O4) O4 K4))))
(let ((a!15 (ite (and (= Y2 A3) (= a!12 0)) 1 a!13))
      (a!18 (and (or (not (= Y2 A3)) (not (= a!12 0))) (= a!13 0)))
      (a!39 (ite (and (= S3 U3) (= a!36 0)) 1 a!37))
      (a!42 (and (or (not (= S3 U3)) (not (= a!36 0))) (= a!37 0)))
      (a!63 (ite (and (= M4 O4) (= a!60 0)) 1 a!61))
      (a!66 (and (or (not (= M4 O4)) (not (= a!60 0))) (= a!61 0))))
(let ((a!16 (ite (= S2 a!14) (+ 1 a!15) (+ (- 1) a!15)))
      (a!40 (ite (= M3 a!38) (+ 1 a!39) (+ (- 1) a!39)))
      (a!64 (ite (= G4 a!62) (+ 1 a!63) (+ (- 1) a!63))))
(let ((a!17 (and (or (and (= Y2 A3) (= a!12 0)) (not (= a!13 0))) (= a!16 0)))
      (a!19 (ite (= Q2 (ite a!18 S2 a!14))
                 (+ 1 (ite a!18 1 a!16))
                 (+ (- 1) (ite a!18 1 a!16))))
      (a!41 (and (or (and (= S3 U3) (= a!36 0)) (not (= a!37 0))) (= a!40 0)))
      (a!43 (ite (= K3 (ite a!42 M3 a!38))
                 (+ 1 (ite a!42 1 a!40))
                 (+ (- 1) (ite a!42 1 a!40))))
      (a!65 (and (or (and (= M4 O4) (= a!60 0)) (not (= a!61 0))) (= a!64 0)))
      (a!67 (ite (= E4 (ite a!66 G4 a!62))
                 (+ 1 (ite a!66 1 a!64))
                 (+ (- 1) (ite a!66 1 a!64)))))
(let ((a!20 (ite (= O2 (ite a!17 Q2 (ite a!18 S2 a!14)))
                 (+ 1 (ite a!17 1 a!19))
                 (+ (- 1) (ite a!17 1 a!19))))
      (a!22 (and (or a!18 (not (= a!16 0))) (= a!19 0)))
      (a!44 (ite (= I3 (ite a!41 K3 (ite a!42 M3 a!38)))
                 (+ 1 (ite a!41 1 a!43))
                 (+ (- 1) (ite a!41 1 a!43))))
      (a!46 (and (or a!42 (not (= a!40 0))) (= a!43 0)))
      (a!68 (ite (= C4 (ite a!65 E4 (ite a!66 G4 a!62)))
                 (+ 1 (ite a!65 1 a!67))
                 (+ (- 1) (ite a!65 1 a!67))))
      (a!70 (and (or a!66 (not (= a!64 0))) (= a!67 0))))
(let ((a!21 (and (or a!17 (not (= a!19 0))) (= a!20 0)))
      (a!23 (ite a!22 O2 (ite a!17 Q2 (ite a!18 S2 a!14))))
      (a!45 (and (or a!41 (not (= a!43 0))) (= a!44 0)))
      (a!47 (ite a!46 I3 (ite a!41 K3 (ite a!42 M3 a!38))))
      (a!69 (and (or a!65 (not (= a!67 0))) (= a!68 0)))
      (a!71 (ite a!70 C4 (ite a!65 E4 (ite a!66 G4 a!62)))))
(let ((a!24 (ite (= M2 a!23)
                 (+ 1 (ite a!22 1 a!20))
                 (+ (- 1) (ite a!22 1 a!20))))
      (a!48 (ite (= G3 a!47)
                 (+ 1 (ite a!46 1 a!44))
                 (+ (- 1) (ite a!46 1 a!44))))
      (a!72 (ite (= A4 a!71)
                 (+ 1 (ite a!70 1 a!68))
                 (+ (- 1) (ite a!70 1 a!68)))))
(let ((a!25 (= (ite (= K2 (ite a!21 M2 a!23))
                    (+ 1 (ite a!21 1 a!24))
                    (+ (- 1) (ite a!21 1 a!24)))
               0))
      (a!27 (and (or a!22 (not (= a!20 0))) (= a!24 0)))
      (a!49 (= (ite (= E3 (ite a!45 G3 a!47))
                    (+ 1 (ite a!45 1 a!48))
                    (+ (- 1) (ite a!45 1 a!48)))
               0))
      (a!51 (and (or a!46 (not (= a!44 0))) (= a!48 0)))
      (a!73 (= (ite (= Y3 (ite a!69 A4 a!71))
                    (+ 1 (ite a!69 1 a!72))
                    (+ (- 1) (ite a!69 1 a!72)))
               0))
      (a!75 (and (or a!70 (not (= a!68 0))) (= a!72 0))))
(let ((a!26 (and (or a!21 (not (= a!24 0))) a!25))
      (a!50 (and (or a!45 (not (= a!48 0))) a!49))
      (a!74 (and (or a!69 (not (= a!72 0))) a!73)))
(let ((a!28 (ite a!26 I2 (ite a!27 K2 (ite a!21 M2 a!23))))
      (a!52 (ite a!50 C3 (ite a!51 E3 (ite a!45 G3 a!47))))
      (a!76 (ite a!74 W3 (ite a!75 Y3 (ite a!69 A4 a!71)))))
(let ((a!29 (ite (= Y2 a!28)
                 (+ (- 1) (ite (= A3 a!28) 5 6))
                 (ite (= A3 a!28) 5 6)))
      (a!53 (ite (= S3 a!52)
                 (+ (- 1) (ite (= U3 a!52) 5 6))
                 (ite (= U3 a!52) 5 6)))
      (a!77 (ite (= M4 a!76)
                 (+ (- 1) (ite (= O4 a!76) 5 6))
                 (ite (= O4 a!76) 5 6))))
(let ((a!30 (ite (= U2 a!28)
                 (+ (- 1) (ite (= W2 a!28) (+ (- 1) a!29) a!29))
                 (ite (= W2 a!28) (+ (- 1) a!29) a!29)))
      (a!54 (ite (= O3 a!52)
                 (+ (- 1) (ite (= Q3 a!52) (+ (- 1) a!53) a!53))
                 (ite (= Q3 a!52) (+ (- 1) a!53) a!53)))
      (a!78 (ite (= I4 a!76)
                 (+ (- 1) (ite (= K4 a!76) (+ (- 1) a!77) a!77))
                 (ite (= K4 a!76) (+ (- 1) a!77) a!77))))
(let ((a!31 (ite (= Q2 a!28)
                 (+ (- 1) (ite (= S2 a!28) (+ (- 1) a!30) a!30))
                 (ite (= S2 a!28) (+ (- 1) a!30) a!30)))
      (a!55 (ite (= K3 a!52)
                 (+ (- 1) (ite (= M3 a!52) (+ (- 1) a!54) a!54))
                 (ite (= M3 a!52) (+ (- 1) a!54) a!54)))
      (a!79 (ite (= E4 a!76)
                 (+ (- 1) (ite (= G4 a!76) (+ (- 1) a!78) a!78))
                 (ite (= G4 a!76) (+ (- 1) a!78) a!78))))
(let ((a!32 (ite (= M2 a!28)
                 (+ (- 1) (ite (= O2 a!28) (+ (- 1) a!31) a!31))
                 (ite (= O2 a!28) (+ (- 1) a!31) a!31)))
      (a!56 (ite (= G3 a!52)
                 (+ (- 1) (ite (= I3 a!52) (+ (- 1) a!55) a!55))
                 (ite (= I3 a!52) (+ (- 1) a!55) a!55)))
      (a!80 (ite (= A4 a!76)
                 (+ (- 1) (ite (= C4 a!76) (+ (- 1) a!79) a!79))
                 (ite (= C4 a!76) (+ (- 1) a!79) a!79))))
(let ((a!33 (= (ite (= K2 a!28) (+ (- 1) a!32) a!32) 0))
      (a!57 (= (ite (= E3 a!52) (+ (- 1) a!56) a!56) 0))
      (a!81 (= (ite (= Y3 a!76) (+ (- 1) a!80) a!80) 0)))
(let ((a!34 (ite (= I2 a!28) (= (ite (= K2 a!28) (+ (- 1) a!32) a!32) 1) a!33))
      (a!58 (ite (= C3 a!52) (= (ite (= E3 a!52) (+ (- 1) a!56) a!56) 1) a!57))
      (a!82 (ite (= W3 a!76) (= (ite (= Y3 a!76) (+ (- 1) a!80) a!80) 1) a!81)))
(let ((a!35 (or (= (ite (= W2 a!28) (+ (- 1) a!29) a!29) 0)
                (= a!30 0)
                (= (ite (= S2 a!28) (+ (- 1) a!30) a!30) 0)
                (= a!31 0)
                (= (ite (= O2 a!28) (+ (- 1) a!31) a!31) 0)
                (= a!32 0)
                a!33
                a!34))
      (a!59 (or (= (ite (= Q3 a!52) (+ (- 1) a!53) a!53) 0)
                (= a!54 0)
                (= (ite (= M3 a!52) (+ (- 1) a!54) a!54) 0)
                (= a!55 0)
                (= (ite (= I3 a!52) (+ (- 1) a!55) a!55) 0)
                (= a!56 0)
                a!57
                a!58))
      (a!83 (or (= (ite (= K4 a!76) (+ (- 1) a!77) a!77) 0)
                (= a!78 0)
                (= (ite (= G4 a!76) (+ (- 1) a!78) a!78) 0)
                (= a!79 0)
                (= (ite (= C4 a!76) (+ (- 1) a!79) a!79) 0)
                (= a!80 0)
                a!81
                a!82)))
(let ((a!84 (and (or (not Q4) (= R5 (ite a!35 a!28 0.0)))
                 (or (not S4) (= T5 (ite a!59 a!52 0.0)))
                 (or (not U4) (= V5 (ite a!83 a!76 0.0)))
                 (= B3 A3)
                 (= D3 C3)
                 (= F3 E3)
                 (= H3 G3)
                 (= J3 I3)
                 (= L3 K3)
                 (= N3 M3)
                 (= P3 O3)
                 (= R3 Q3)
                 (= T3 S3)
                 (= V3 U3)
                 (= X3 W3)
                 (= Z3 Y3)
                 (= B4 A4)
                 (= D4 C4)
                 (= F4 E4)
                 (= H4 G4)
                 (= J4 I4)
                 (= L4 K4)
                 (= N4 M4)
                 (= P4 O4)
                 (= W5 2.0)
                 (= X5 3.0)
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
                 (= N2 M2)
                 (= P2 O2)
                 (= R2 Q2)
                 (= T2 S2)
                 (= V2 U2)
                 (= X2 W2)
                 (= Z2 Y2)
                 (= J5 I5)
                 (= L5 K5)
                 (= N5 M5)
                 (= P5 O5)
                 (= R4 Q4)
                 (= T4 S4)
                 (= V4 U4)
                 (= X4 W4)
                 (= Z4 Y4)
                 (= B5 A5)
                 (= D5 C5)
                 (= F5 E5)
                 (= H5 G5))))
(let ((a!85 (or (and (or (not K5) (= R3 a!1))
                     (or (not K5) (= L4 a!1))
                     (or (not K5) (= X2 a!1))
                     (or (not M5) (= T3 a!2))
                     (or (not M5) (= N4 a!2))
                     (or (not M5) (= Z2 a!2))
                     (or (not O5) (= B3 a!3))
                     (or (not O5) (= V3 a!3))
                     (or (not O5) (= P4 a!3))
                     (or (not W4) (= D3 a!4))
                     (or (not W4) (= X3 a!4))
                     (or (not W4) (= J2 a!4))
                     (or (not Y4) (= F3 a!5))
                     (or (not Y4) (= Z3 a!5))
                     (or (not Y4) (= L2 a!5))
                     (or (not A5) (= H3 a!6))
                     (or (not A5) (= B4 a!6))
                     (or (not A5) (= N2 a!6))
                     (or (not C5) (= J3 a!7))
                     (or (not C5) (= D4 a!7))
                     (or (not C5) (= P2 a!7))
                     (or (not E5) (= L3 a!8))
                     (or (not E5) (= F4 a!8))
                     (or (not E5) (= R2 a!8))
                     (or (not G5) (= N3 a!9))
                     (or (not G5) (= H4 a!9))
                     (or (not G5) (= T2 a!9))
                     (or (not I5) (= P3 a!10))
                     (or (not I5) (= J4 a!10))
                     (or (not I5) (= V2 a!10))
                     (= W5 1.0)
                     (= X5 2.0)
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
                     (= R5 Q5)
                     (= T5 S5)
                     (= V5 U5)
                     (= J5 I5)
                     (= L5 K5)
                     (= N5 M5)
                     (= P5 O5)
                     (= R4 Q4)
                     (= T4 S4)
                     (= V4 U4)
                     (= X4 W4)
                     (= Z4 Y4)
                     (= B5 A5)
                     (= D5 C5)
                     (= F5 E5)
                     (= H5 G5))
                (and (= B3 A3)
                     (= D3 C3)
                     (= F3 E3)
                     (= H3 G3)
                     (= J3 I3)
                     (= L3 K3)
                     (= N3 M3)
                     (= P3 O3)
                     (= R3 Q3)
                     (= T3 S3)
                     (= V3 U3)
                     (= X3 W3)
                     (= Z3 Y3)
                     (= B4 A4)
                     (= D4 C4)
                     (= F4 E4)
                     (= H4 G4)
                     (= J4 I4)
                     (= L4 K4)
                     (= N4 M4)
                     (= P4 O4)
                     (= W5 3.0)
                     (= X5 W5)
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
                     (= N2 M2)
                     (= P2 O2)
                     (= R2 Q2)
                     (= T2 S2)
                     (= V2 U2)
                     (= X2 W2)
                     (= Z2 Y2)
                     (= R5 Q5)
                     (= T5 S5)
                     (= V5 U5)
                     (= J5 I5)
                     (= L5 K5)
                     (= N5 M5)
                     (= P5 O5)
                     (= R4 Q4)
                     (= T4 S4)
                     (= V4 U4)
                     (= X4 W4)
                     (= Z4 Y4)
                     (= B5 A5)
                     (= D5 C5)
                     (= F5 E5)
                     (= H5 G5))
                a!11
                a!84)))
  (and (= Z5 Y5) a!85 (= B6 A6))))))))))))))))))))))
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
           Z4
           B5
           D5
           F5
           H5
           J5
           L5
           N5
           P5
           R5
           T5
           V5
           X5
           Z5
           B6)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Real) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) (V1 Real) (W1 Real) (X1 Real) (Y1 Real) (Z1 Real) (A2 Real) (B2 Real) (C2 Real) (D2 Real) (E2 Real) (F2 Real) (G2 Real) (H2 Real) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Bool) (P2 Bool) (Q2 Bool) (R2 Bool) (S2 Bool) (T2 Bool) (U2 Bool) (V2 Real) (W2 Real) (X2 Real) (Y2 Real) (Z2 Real) (A3 Real) ) 
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
           M2
           N2
           O2
           P2
           Q2
           R2
           S2
           T2
           U2
           V2
           W2
           X2
           Y2
           Z2
           A3)
        (let ((a!1 (or (and J2 (not (= V2 W2))) (and K2 (not (= V2 X2)))))
      (a!2 (or (and I2 (not (= W2 V2))) (and K2 (not (= W2 X2)))))
      (a!3 (or (and I2 (not (= X2 V2))) (and J2 (not (= X2 W2))))))
  (and (or (and I2 a!1) (and J2 a!2) (and K2 a!3)) (<= 3.0 Y2)))
      )
      false
    )
  )
)

(check-sat)
(exit)
