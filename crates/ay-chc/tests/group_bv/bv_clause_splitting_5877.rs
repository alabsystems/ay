// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Tests for BV clause-level lemma splitting (#5877).
//!
//! When a BV-native lemma is NOT(AND(c1, c2, ..., cn)), clause splitting
//! decomposes it into n individual clause lemmas: NOT(c1), NOT(c2), ..., NOT(cn).
//! This matches Z3 Spacer's architecture where each lemma stores a single clause.
//!
//! Reference: z3/src/muz/spacer/spacer_context.h:121-198

use ay_chc::{testing, ChcParser, PdrConfig, PdrResult};
use std::time::Duration;

const NESTED4_BENCHMARK: &str = "(set-logic HORN)\n\n\n(declare-fun |state| ( Bool Bool Bool (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)\n\n(assert\n  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F Bool) (G Bool) (H Bool) ) \n    (=>\n      (and\n        (and (not G) (not F) (not H))\n      )\n      (state H G F B A D C E)\n    )\n  )\n)\n(assert\n  (forall ( (A Bool) (B Bool) (C Bool) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (M (_ BitVec 32)) (N (_ BitVec 32)) (O (_ BitVec 32)) (P Bool) (Q Bool) (R Bool) ) \n    (=>\n      (and\n        (state R Q P G E J H L)\n        (or (and (not C)\n         (not B)\n         A\n         (not P)\n         (not Q)\n         (not R)\n         (= M N)\n         (= K O)\n         (= E D)\n         (= I #x00000001)\n         (= G F)\n         (not (bvsle M #x00000000)))\n    (and (not C)\n         B\n         A\n         (not P)\n         (not Q)\n         R\n         (= M L)\n         (= K J)\n         (= I H)\n         (= G F)\n         (= D L)\n         (not (bvsle J H)))\n    (and C\n         (not B)\n         (not A)\n         (not P)\n         Q\n         R\n         (= M L)\n         (= K J)\n         (= I H)\n         (= G F)\n         (= D L)\n         (bvsle J E))\n    (and (not C)\n         B\n         A\n         (not P)\n         Q\n         R\n         (= M L)\n         (= K J)\n         (= I H)\n         (= G F)\n         (= D (bvadd #x00000001 E))\n         (not (bvsle J E)))\n    (and (not C)\n         (not B)\n         A\n         P\n         (not Q)\n         (not R)\n         (= M L)\n         (= K J)\n         (= E D)\n         (= I (bvadd #x00000001 H))\n         (= G F)\n         (bvsle J E))\n    (and C\n         (not B)\n         A\n         P\n         (not Q)\n         (not R)\n         (= M L)\n         (= K J)\n         (= E D)\n         (= I H)\n         (= G F)\n         (not (bvsle J E))\n         (not (bvsle #x00000001 E)))\n    (and C\n         (not B)\n         (not A)\n         P\n         (not Q)\n         (not R)\n         (= M L)\n         (= K J)\n         (= I H)\n         (= G F)\n         (= D (bvadd #x00000001 E))\n         (not (bvsle J E))\n         (bvsle #x00000001 E))\n    (and C B (not A) P (not Q) R (= M L) (= K J) (= E D) (= I H) (= G F))\n    (and C B (not A) P Q (not R)))\n      )\n      (state A B C F D K I M)\n    )\n  )\n)\n(assert\n  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F Bool) (G Bool) (H Bool) ) \n    (=>\n      (and\n        (state H G F B A D C E)\n        (and (= G true) (= F true) (not H))\n      )\n      false\n    )\n  )\n)\n\n(check-sat)\n(exit)\n";
const BIST_CELL_BENCHMARK: &str = "(set-logic HORN)\n\n\n(declare-fun |state| ( Bool Bool Bool (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)\n\n(assert\n  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (M (_ BitVec 32)) (N (_ BitVec 32)) (O (_ BitVec 32)) (P (_ BitVec 32)) (Q (_ BitVec 32)) (R (_ BitVec 32)) (S (_ BitVec 32)) (T (_ BitVec 32)) (U (_ BitVec 32)) (V (_ BitVec 32)) (W (_ BitVec 32)) (X (_ BitVec 32)) (Y (_ BitVec 32)) (Z (_ BitVec 32)) (A1 (_ BitVec 32)) (B1 (_ BitVec 32)) (C1 (_ BitVec 32)) (D1 (_ BitVec 32)) (E1 (_ BitVec 32)) (F1 (_ BitVec 32)) (G1 (_ BitVec 32)) (H1 (_ BitVec 32)) (I1 (_ BitVec 32)) (J1 (_ BitVec 32)) (K1 (_ BitVec 32)) (L1 Bool) (M1 Bool) (N1 Bool) ) \n    (=>\n      (and\n        (and (not M1) (not L1) (not N1))\n      )\n      (state L1\n       N1\n       M1\n       K\n       M\n       O\n       P\n       R\n       S\n       T\n       V\n       X\n       Y\n       Z\n       B1\n       C1\n       D1\n       E1\n       G1\n       H1\n       K1\n       J1\n       I1\n       F1\n       A1\n       W\n       U\n       Q\n       N\n       L\n       J\n       I\n       H\n       G\n       F\n       E\n       D\n       C\n       B\n       A)\n    )\n  )\n)\n(assert\n  (forall ( (A Bool) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (M (_ BitVec 32)) (N (_ BitVec 32)) (O (_ BitVec 32)) (P (_ BitVec 32)) (Q (_ BitVec 32)) (R (_ BitVec 32)) (S (_ BitVec 32)) (T (_ BitVec 32)) (U (_ BitVec 32)) (V (_ BitVec 32)) (W (_ BitVec 32)) (X (_ BitVec 32)) (Y (_ BitVec 32)) (Z (_ BitVec 32)) (A1 (_ BitVec 32)) (B1 (_ BitVec 32)) (C1 (_ BitVec 32)) (D1 (_ BitVec 32)) (E1 (_ BitVec 32)) (F1 (_ BitVec 32)) (G1 (_ BitVec 32)) (H1 (_ BitVec 32)) (I1 (_ BitVec 32)) (J1 (_ BitVec 32)) (K1 (_ BitVec 32)) (L1 (_ BitVec 32)) (M1 (_ BitVec 32)) (N1 (_ BitVec 32)) (O1 (_ BitVec 32)) (P1 (_ BitVec 32)) (Q1 (_ BitVec 32)) (R1 (_ BitVec 32)) (S1 (_ BitVec 32)) (T1 (_ BitVec 32)) (U1 (_ BitVec 32)) (V1 (_ BitVec 32)) (W1 (_ BitVec 32)) (X1 (_ BitVec 32)) (Y1 (_ BitVec 32)) (Z1 (_ BitVec 32)) (A2 (_ BitVec 32)) (B2 (_ BitVec 32)) (C2 (_ BitVec 32)) (D2 (_ BitVec 32)) (E2 (_ BitVec 32)) (F2 (_ BitVec 32)) (G2 (_ BitVec 32)) (H2 (_ BitVec 32)) (I2 (_ BitVec 32)) (J2 (_ BitVec 32)) (K2 (_ BitVec 32)) (L2 (_ BitVec 32)) (M2 (_ BitVec 32)) (N2 (_ BitVec 32)) (O2 (_ BitVec 32)) (P2 (_ BitVec 32)) (Q2 (_ BitVec 32)) (R2 (_ BitVec 32)) (S2 (_ BitVec 32)) (T2 (_ BitVec 32)) (U2 (_ BitVec 32)) (V2 (_ BitVec 32)) (W2 (_ BitVec 32)) (X2 (_ BitVec 32)) (Y2 (_ BitVec 32)) (Z2 (_ BitVec 32)) (A3 (_ BitVec 32)) (B3 (_ BitVec 32)) (C3 (_ BitVec 32)) (D3 (_ BitVec 32)) (E3 (_ BitVec 32)) (F3 (_ BitVec 32)) (G3 (_ BitVec 32)) (H3 (_ BitVec 32)) (I3 (_ BitVec 32)) (J3 (_ BitVec 32)) (K3 Bool) (L3 Bool) (M3 Bool) (N3 Bool) (O3 Bool) ) \n    (=>\n      (and\n        (state L3\n       O3\n       N3\n       W\n       A1\n       E1\n       G1\n       K1\n       M1\n       O1\n       S1\n       W1\n       Y1\n       A2\n       E2\n       G2\n       I2\n       K2\n       O2\n       Q2\n       V2\n       T2\n       R2\n       L2\n       B2\n       T1\n       P1\n       H1\n       B1\n       X\n       T\n       R\n       P\n       N\n       L\n       J\n       H\n       F\n       D\n       B)\n        (let ((a!1 (or (and (= P1 #x00000000) (= Z #x00000001))\n               (and (not (= P1 #x00000000)) (= Z #x00000000))))\n      (a!26 (or (and (= J3 #x00000002)\n                     (= I3 #x00000001)\n                     (= H3 #x00000001)\n                     (= G3 #x00000001)\n                     (= F3 #x00000001)\n                     (= E3 #x00000001)\n                     (= D3 #x00000000)\n                     (= D3 #x00000002)\n                     (= C3 #x00000000)\n                     (= B3 #x00000000)\n                     (= A3 #x00000000)\n                     (= Z2 #x00000000)\n                     (= W2 #x00000001)\n                     (= U2 #x00000000)\n                     (= S2 #x00000001)\n                     (= M2 #x00000000)\n                     (= C2 #x00000000)\n                     (= U1 #x00000001)\n                     (= I1 #x00000000)\n                     (= C1 #x00000001)\n                     (= Y #x00000000)\n                     (= U #x00000000)\n                     (= S #x00000000))\n                (and (= J3 #x00000002)\n                     (= H3 #x00000001)\n                     (= G3 #x00000001)\n                     (= F3 #x00000001)\n                     (= E3 #x00000001)\n                     (= D3 I3)\n                     (not (= D3 #x00000000))\n                     (= D3 #x00000002)\n                     (= C3 #x00000000)\n                     (= B3 #x00000000)\n                     (= A3 #x00000000)\n                     (= Z2 #x00000000)\n                     (= W2 #x00000001)\n                     (= U2 #x00000000)\n                     (= S2 #x00000001)\n                     (= M2 #x00000000)\n                     (= C2 #x00000000)\n                     (= U1 #x00000001)\n                     (= I1 #x00000000)\n                     (= C1 #x00000001)\n                     (= Y #x00000000)\n                     (= U #x00000000)\n                     (= S #x00000000)))))\n(let ((a!2 (or (and a!1\n                    (= Z2 H)\n                    (= B1 #x00000001)\n                    (= L2 #x00000001)\n                    (= C1 B1)\n                    (= Z D1)\n                    (= V D1)\n                    (= V #x00000000))\n               (and a!1\n                    (= Z2 #x00000000)\n                    (not (= B1 #x00000001))\n                    (= L2 #x00000001)\n                    (= C1 #x00000001)\n                    (= Z D1)\n                    (= V D1)\n                    (= V #x00000000))))\n      (a!27 (or (and a!26 (= E3 #x00000001) (= O #x00000001))\n                (and a!26\n                     (= F3 #x00000001)\n                     (not (= E3 #x00000001))\n                     (= O #x00000001))\n                (and a!26\n                     (= G3 #x00000001)\n                     (not (= F3 #x00000001))\n                     (not (= E3 #x00000001))\n                     (= O #x00000001))\n                (and a!26\n                     (not (= H3 #x00000001))\n                     (not (= G3 #x00000001))\n                     (not (= F3 #x00000001))\n                     (not (= E3 #x00000001))\n                     (= O #x00000000))\n                (and a!26\n                     (= H3 #x00000001)\n                     (not (= G3 #x00000001))\n                     (not (= F3 #x00000001))\n                     (not (= E3 #x00000001))\n                     (= O #x00000001))))\n      (a!34 (or (and a!1\n                     (= B1 #x00000000)\n                     (= P2 #x00000001)\n                     (= P1 #x00000000)\n                     (= H2 X2)\n                     (not (= H2 #x00000000))\n                     (= Z D1)\n                     (= V D1)\n                     (not (= V #x00000000)))\n                (and a!1\n                     (not (= B1 #x00000000))\n                     (= P2 #x00000000)\n                     (= P1 #x00000000)\n                     (= H2 X2)\n                     (not (= H2 #x00000000))\n                     (not (= T1 #x00000000))\n                     (= Z D1)\n                     (= V D1)\n                     (not (= V #x00000000)))\n                (and a!1\n                     (not (= B1 #x00000000))\n                     (= P2 #x00000001)\n                     (= P1 #x00000000)\n                     (= H2 X2)\n                     (not (= H2 #x00000000))\n                     (= T1 #x00000000)\n                     (= Z D1)\n                     (= V D1)\n                     (not (= V #x00000000))))))\n(let ((a!3 (or (and a!2 (= M2 #x00000000))\n               (and a!1\n                    (= Z2 H)\n                    (= M2 L2)\n                    (not (= L2 #x00000001))\n                    (= C1 B1)\n                    (= Z D1)\n                    (= V D1)\n                    (= V #x00000000))))\n      (a!28 (or (and a!27 (= J3 Q1) (= M O) (= E M) (= E #x00000000))\n                (and a!27\n                     (= Q1 #x00000000)\n                     (= M O)\n                     (= E M)\n                     (not (= E #x00000000)))))\n      (a!35 (or (and a!34 (= Y2 #x00000001) (= V2 #x00000000))\n                (and a!34\n                     (= Y2 #x00000000)\n                     (not (= R2 #x00000000))\n                     (not (= V2 #x00000000)))\n                (and a!34\n                     (= Y2 #x00000001)\n                     (= R2 #x00000000)\n                     (not (= V2 #x00000000))))))\n(let ((a!4 (or (and a!3 (= R #x00000001) (= A3 P) (= S2 R2) (= R2 #x00000001))\n               (and a!3\n                    (= R #x00000001)\n                    (= A3 #x00000000)\n                    (= S2 #x00000001)\n                    (not (= R2 #x00000001)))))\n      (a!29 (or (and a!28 (= E3 #x00000001) (= I #x00000002))\n                (and a!28 (= E3 I) (not (= E3 #x00000001)))))\n      (a!36 (or (and a!35 (not (= Y2 #x00000000)) (= J1 #x00000000))\n                (and a!35\n                     (= Y2 #x00000000)\n                     (not (= P2 #x00000000))\n                     (= J1 #x00000000))\n                (and a!35 (= Y2 #x00000000) (= P2 #x00000000) (= J1 #x00000001)))))\n(let ((a!5 (or (and a!4 (= S #x00000000))\n               (and a!3 (not (= R #x00000001)) (= A3 P) (= S2 R2) (= S R))))\n      (a!30 (or (and a!29 (= F3 Q) (not (= F3 #x00000001)))\n                (and a!29 (= F3 #x00000001) (= Q #x00000002))))\n      (a!37 (or (and a!36 (= Y2 #x00000000) (= X1 #x00000000))\n                (and a!36\n                     (not (= Y2 #x00000000))\n                     (= P2 #x00000000)\n                     (= X1 #x00000000))\n                (and a!36\n                     (not (= Y2 #x00000000))\n                     (not (= P2 #x00000000))\n                     (= X1 #x00000001)))))\n(let ((a!6 (or (and a!5 (= B3 F) (= W2 V2) (= T2 #x00000001) (= V2 #x00000001))\n               (and a!5\n                    (= B3 #x00000000)\n                    (= W2 #x00000001)\n                    (= T2 #x00000001)\n                    (not (= V2 #x00000001)))))\n      (a!31 (or (and a!30 (= G3 G) (not (= G3 #x00000001)))\n                (and a!30 (= G3 #x00000001) (= G #x00000002))))\n      (a!38 (or (and a!37 (not (= X1 #x00000000)) (= Y #x00000000))\n                (and a!37\n                     (= X1 #x00000000)\n                     (not (= J1 #x00000000))\n                     (= Y #x00000000))\n                (and a!37 (= X1 #x00000000) (= J1 #x00000000) (= Y #x00000001)))))\n(let ((a!7 (or (and a!6 (= U2 #x00000000))\n               (and a!5 (= B3 F) (= W2 V2) (= U2 T2) (not (= T2 #x00000001)))))\n      (a!32 (or (and a!31 (= H3 K) (not (= H3 #x00000001)))\n                (and a!31 (= H3 #x00000001) (= K #x00000002))))\n      (a!39 (or (and a!38 (= Q1 #x00000002) (= I1 #x00000001))\n                (and a!1\n                     (= K1 J1)\n                     (not (= P1 #x00000000))\n                     (= Y1 X1)\n                     (= I2 H2)\n                     (= Q1 P1)\n                     (= Q2 P2)\n                     (= I1 H1)\n                     (= Z D1)\n                     (= Y X)\n                     (= V D1)\n                     (not (= V #x00000000)))\n                (and a!1\n                     (= K1 J1)\n                     (= P1 #x00000000)\n                     (= H2 X2)\n                     (= H2 #x00000000)\n                     (= Y1 X1)\n                     (= Q1 P1)\n                     (= Q2 P2)\n                     (= I1 H1)\n                     (= Z D1)\n                     (= Y X)\n                     (= V D1)\n                     (not (= V #x00000000))))))\n(let ((a!8 (or (and a!7 (= C3 J) (= T #x00000001) (= T1 #x00000001) (= U1 T1))\n               (and a!7\n                    (= C3 #x00000000)\n                    (= T #x00000001)\n                    (not (= T1 #x00000001))\n                    (= U1 #x00000001))))\n      (a!33 (or (and a!32 (= I3 C) (not (= I3 #x00000001)))\n                (and a!32 (= I3 #x00000001) (= C #x00000002)))))\n(let ((a!9 (or (and a!8 (= U #x00000000))\n               (and a!7 (= C3 J) (not (= T #x00000001)) (= U1 T1) (= U T)))))\n(let ((a!10 (or (and a!9 (= D3 B) (= H1 #x00000001) (= C2 B2) (= B2 X))\n                (and a!9\n                     (= D3 #x00000000)\n                     (= H1 #x00000001)\n                     (= C2 X)\n                     (not (= B2 X))))))\n(let ((a!11 (or (and a!10 (= I1 #x00000000))\n                (and a!9 (= D3 B) (not (= H1 #x00000001)) (= C2 B2) (= I1 H1)))))\n(let ((a!12 (or (and a!11 (= E3 #x00000001) (= Z2 #x00000000))\n                (and a!11 (= Z2 E3) (not (= Z2 #x00000000))))))\n(let ((a!13 (or (and a!12 (= F3 #x00000001) (= A3 #x00000000))\n                (and a!12 (= A3 F3) (not (= A3 #x00000000))))))\n(let ((a!14 (or (and a!13 (= G3 #x00000001) (= B3 #x00000000))\n                (and a!13 (= B3 G3) (not (= B3 #x00000000))))))\n(let ((a!15 (or (and a!14 (= H3 #x00000001) (= C3 #x00000000))\n                (and a!14 (= C3 H3) (not (= C3 #x00000000))))))\n(let ((a!16 (or (and a!15 (= I3 #x00000001) (= D3 #x00000000))\n                (and a!15 (= D3 I3) (not (= D3 #x00000000))))))\n(let ((a!17 (or (and a!16 (= E3 #x00000001) (= D2 #x00000001))\n                (and a!16\n                     (= F3 #x00000001)\n                     (not (= E3 #x00000001))\n                     (= D2 #x00000001))\n                (and a!16\n                     (= G3 #x00000001)\n                     (not (= F3 #x00000001))\n                     (not (= E3 #x00000001))\n                     (= D2 #x00000001))\n                (and a!16\n                     (not (= H3 #x00000001))\n                     (not (= G3 #x00000001))\n                     (not (= F3 #x00000001))\n                     (not (= E3 #x00000001))\n                     (= D2 #x00000000))\n                (and a!16\n                     (= H3 #x00000001)\n                     (not (= G3 #x00000001))\n                     (not (= F3 #x00000001))\n                     (not (= E3 #x00000001))\n                     (= D2 #x00000001)))))\n(let ((a!18 (or (and a!17 (= D2 J2) (= R1 J2) (= R1 #x00000000) (= Q1 P1))\n                (and a!17\n                     (= D2 J2)\n                     (= R1 J2)\n                     (not (= R1 #x00000000))\n                     (= Q1 #x00000000)))))\n(let ((a!19 (or (and a!18 (= E3 I) (not (= E3 #x00000001)))\n                (and a!18 (= E3 #x00000001) (= I #x00000002)))))\n(let ((a!20 (or (and a!19 (= F3 Q) (not (= F3 #x00000001)))\n                (and a!19 (= F3 #x00000001) (= Q #x00000002)))))\n(let ((a!21 (or (and a!20 (= G3 G) (not (= G3 #x00000001)))\n                (and a!20 (= G3 #x00000001) (= G #x00000002)))))\n(let ((a!22 (or (and a!21 (= H3 K) (not (= H3 #x00000001)))\n                (and a!21 (= H3 #x00000001) (= K #x00000002)))))\n(let ((a!23 (or (and a!22 (= I3 C) (not (= I3 #x00000001)))\n                (and a!22 (= I3 #x00000001) (= C #x00000002)))))\n(let ((a!24 (or (and a!23 (not (= Q1 #x00000000)) (= L1 #x00000000))\n                (and a!23 (= Q1 #x00000000) (= L1 #x00000001)))))\n(let ((a!25 (or (and a!24\n                     (not (= V1 #x00000000))\n                     (= N1 V1)\n                     (= L1 N1)\n                     (= F1 #x00000000))\n                (and a!24\n                     (= V1 #x00000000)\n                     (= N1 V1)\n                     (= L1 N1)\n                     (= F1 #x00000001)))))\n  (or (and M3 (not K3) L3 A N3 (not O3))\n      (and M3\n           (not K3)\n           (not L3)\n           (not A)\n           (not N3)\n           O3\n           a!25\n           (= K1 J1)\n           (= N2 #x00000000)\n           (= Y1 X1)\n           (= Z1 N2)\n           (= G2 F2)\n           (= I2 H2)\n           (= Q2 P2)\n           (= F1 Z1)\n           (= Y X)\n           (= O N)\n           (= M L)\n           (= E D))\n      (and (not M3)\n           (not K3)\n           (not L3)\n           A\n           (not N3)\n           O3\n           a!25\n           (= K1 J1)\n           (not (= N2 #x00000000))\n           (not (= C2 #x00000000))\n           (= Y1 X1)\n           (= Z1 N2)\n           (= G2 F2)\n           (= I2 H2)\n           (= Q2 P2)\n           (= F1 Z1)\n           (= Y X)\n           (= O N)\n           (= M L)\n           (= E D))\n      (and M3\n           (not K3)\n           (not L3)\n           (not A)\n           (not N3)\n           (not O3)\n           a!33\n           (= W V)\n           (= A1 Z)\n           (= E1 D1)\n           (= G1 F1)\n           (= K1 J1)\n           (= M1 L1)\n           (= O1 N1)\n           (= S1 R1)\n           (= W1 V1)\n           (= Y1 X1)\n           (= A2 Z1)\n           (= E2 D2)\n           (= G2 F2)\n           (= I2 H2)\n           (= K2 J2)\n           (= O2 N2)\n           (= Q2 P2))\n      (and (not M3)\n           K3\n           (not L3)\n           (not A)\n           (not N3)\n           O3\n           a!39\n           (= W2 V2)\n           (= U2 T2)\n           (= G1 F1)\n           (= S2 R2)\n           (= M1 L1)\n           (= M2 L2)\n           (= O1 N1)\n           (= S1 R1)\n           (= W1 V1)\n           (= C2 B2)\n           (= A2 Z1)\n           (= E2 D2)\n           (= U1 T1)\n           (= G2 F2)\n           (= K2 J2)\n           (= O2 N2)\n           (= C1 B1)\n           (= U T)\n           (= S R)\n           (= Q P)\n           (= O N)\n           (= M L)\n           (= K J)\n           (= I H)\n           (= G F)\n           (= E D)\n           (= C B))\n      (and (not M3)\n           K3\n           L3\n           (not A)\n           (not N3)\n           (not O3)\n           (= W V)\n           (= A1 Z)\n           (= W2 V2)\n           (= E1 D1)\n           (= U2 T2)\n           (= G1 F1)\n           (= S2 R2)\n           (= K1 J1)\n           (= M1 L1)\n           (= M2 L2)\n           (= O1 N1)\n           (= S1 R1)\n           (= W1 V1)\n           (= C2 B2)\n           (= Y1 X1)\n           (= A2 Z1)\n           (= E2 D2)\n           (= U1 T1)\n           (= G2 F2)\n           (= I2 H2)\n           (= Q1 P1)\n           (= K2 J2)\n           (= O2 N2)\n           (= Q2 P2)\n           (= I1 H1)\n           (= C1 B1)\n           (= Y X)\n           (= U T)\n           (= S R)\n           (= Q P)\n           (= O N)\n           (= M L)\n           (= K J)\n           (= I H)\n           (= G F)\n           (= E D)\n           (= C B))\n      (and M3\n           (not K3)\n           (not L3)\n           A\n           N3\n           (not O3)\n           (= W V)\n           (= A1 Z)\n           (= W2 V2)\n           (= E1 D1)\n           (= U2 T2)\n           (= G1 F1)\n           (= S2 R2)\n           (= K1 J1)\n           (= M1 L1)\n           (= M2 L2)\n           (= O1 N1)\n           (= S1 R1)\n           (= W1 V1)\n           (= C2 B2)\n           (= Y1 X1)\n           (= A2 Z1)\n           (= E2 D2)\n           (= U1 T1)\n           (= G2 F2)\n           (= I2 H2)\n           (= Q1 P1)\n           (= K2 J2)\n           (= O2 N2)\n           (= Q2 P2)\n           (= I1 H1)\n           (= C1 B1)\n           (= Y X)\n           (= U T)\n           (= S R)\n           (= Q P)\n           (= O N)\n           (= M L)\n           (= K J)\n           (= I H)\n           (= G F)\n           (= E D)\n           (= C B))))))))))))))))))))))))))))\n      )\n      (state M3\n       K3\n       A\n       V\n       Z\n       D1\n       F1\n       J1\n       L1\n       N1\n       R1\n       V1\n       X1\n       Z1\n       D2\n       F2\n       H2\n       J2\n       N2\n       P2\n       W2\n       U2\n       S2\n       M2\n       C2\n       U1\n       Q1\n       I1\n       C1\n       Y\n       U\n       S\n       Q\n       O\n       M\n       K\n       I\n       G\n       E\n       C)\n    )\n  )\n)\n(assert\n  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (M (_ BitVec 32)) (N (_ BitVec 32)) (O (_ BitVec 32)) (P (_ BitVec 32)) (Q (_ BitVec 32)) (R (_ BitVec 32)) (S (_ BitVec 32)) (T (_ BitVec 32)) (U (_ BitVec 32)) (V (_ BitVec 32)) (W (_ BitVec 32)) (X (_ BitVec 32)) (Y (_ BitVec 32)) (Z (_ BitVec 32)) (A1 (_ BitVec 32)) (B1 (_ BitVec 32)) (C1 (_ BitVec 32)) (D1 (_ BitVec 32)) (E1 (_ BitVec 32)) (F1 (_ BitVec 32)) (G1 (_ BitVec 32)) (H1 (_ BitVec 32)) (I1 (_ BitVec 32)) (J1 (_ BitVec 32)) (K1 (_ BitVec 32)) (L1 Bool) (M1 Bool) (N1 Bool) ) \n    (=>\n      (and\n        (state L1\n       N1\n       M1\n       K\n       M\n       O\n       P\n       R\n       S\n       T\n       V\n       X\n       Y\n       Z\n       B1\n       C1\n       D1\n       E1\n       G1\n       H1\n       K1\n       J1\n       I1\n       F1\n       A1\n       W\n       U\n       Q\n       N\n       L\n       J\n       I\n       H\n       G\n       F\n       E\n       D\n       C\n       B\n       A)\n        (and (= M1 true) (= L1 true) (not N1))\n      )\n      false\n    )\n  )\n)\n\n(check-sat)\n(exit)\n";

fn bounded_bv_clause_splitting_config(timeout: Duration) -> PdrConfig {
    let mut config = PdrConfig::default();
    config.max_frames = 3;
    config.max_iterations = 25;
    config.max_obligations = 1_000;
    config.solve_timeout = Some(timeout);
    config
}

/// nested4 is the canonical #5877 BV benchmark for clause-splitting coverage.
/// Without clause splitting, AY stores the entire conjunction as one lemma
/// and can't push individual clauses independently. With clause splitting,
/// each clause is stored and pushed separately, matching Z3's behavior.
///
/// The end-to-end capability gap for proving this benchmark Safe is still open
/// on committed HEAD. Lower-level clause-splitting coverage lives in
/// `pdr/solver/core.rs`, `proof_interpolation/tests.rs`, and
/// `blocking/tests/source_regression_tests.rs`; this integration test keeps the
/// full benchmark fixture in-tree and locks the structural shape those tests
/// depend on.
#[test]
#[serial_test::serial]
fn test_bv_chc_nested4_clause_splitting() {
    let problem = ChcParser::parse(NESTED4_BENCHMARK).expect("nested4 benchmark should parse");
    assert_eq!(
        problem.predicates().len(),
        1,
        "expected single state predicate"
    );
    assert_eq!(
        problem.clauses().len(),
        3,
        "expected init, transition, and query clauses"
    );
    assert!(
        problem.has_bv_sorts(),
        "nested4 must retain BV predicate arguments"
    );
    assert_eq!(
        problem.max_bv_expanded_arity(),
        163,
        "nested4 should still trigger the large BV-expanded arity shape tracked by #5877"
    );
}

/// bist_cell is a more complex BV problem with 36 BV32 arguments.
/// Clause splitting may help but is not guaranteed to solve it within timeout.
/// This test documents the current behavior; if it starts passing, update expectations.
///
/// Timeout: 60s. Expected: may return Unknown within the internal solve budget.
#[test]
#[serial_test::serial]
fn test_bv_chc_bist_cell_clause_splitting() {
    let config = bounded_bv_clause_splitting_config(Duration::from_secs(5));
    let result = testing::pdr_solve_from_str(BIST_CELL_BENCHMARK, config);
    // bist_cell may still timeout — clause splitting helps but the problem
    // may need additional techniques (IUC, predicate abstraction).
    // If Safe, that's a bonus. If Unknown/timeout, that's expected.
    match &result {
        Ok(PdrResult::Safe(_)) => {
            // Solved! Great — clause splitting was sufficient for bist_cell.
        }
        Ok(PdrResult::Unsafe(_)) => {
            panic!("bist_cell should be Safe, not Unsafe");
        }
        _ => {
            // Unknown or timeout is acceptable for now.
        }
    }
}

/// Regression test: LIA problems must not be affected by clause splitting.
/// Clause splitting is gated on !problem_is_pure_lia, so this LIA problem
/// should solve the same way with or without the feature.
#[test]
#[serial_test::serial]
fn test_lia_unaffected_by_clause_splitting() {
    // Simple counter loop: x starts at 0, increments, property: x >= 0
    let input = r#"
(set-logic HORN)
(declare-fun |inv| (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (inv x))))

(assert (forall ((x Int) (xp Int))
  (=> (and (inv x) (= xp (+ x 1)))
      (inv xp))))

(assert (forall ((x Int))
  (=> (and (inv x) (< x 0))
      false)))

(check-sat)
(exit)
"#;
    let config = PdrConfig::default();
    let result = testing::pdr_solve_from_str(input, config);
    assert!(
        matches!(&result, Ok(PdrResult::Safe(_))),
        "LIA counter problem should be Safe, got {:?}",
        result.map(|r| format!("{:?}", std::mem::discriminant(&r)))
    );
}

/// Simpler BV CHC problem with a single BV32 variable.
/// Verifies that clause splitting does not break basic BV solving.
/// This problem has a simple single-clause invariant (bvsge x 0), so clause
/// splitting should be a no-op.
#[test]
#[serial_test::serial]
fn test_bv_clause_splitting_no_split_needed() {
    let input = r#"
(set-logic HORN)
(declare-fun |inv| ((_ BitVec 32)) Bool)

; Init: x = 0
(assert (forall ((x (_ BitVec 32)))
  (=> (= x #x00000000) (inv x))))

; Transition: x' = x + 1 when x < 10
(assert (forall ((x (_ BitVec 32)) (xp (_ BitVec 32)))
  (=> (and (inv x) (bvslt x #x0000000a) (= xp (bvadd x #x00000001)))
      (inv xp))))

; Property: x >= 0
(assert (forall ((x (_ BitVec 32)))
  (=> (and (inv x) (bvslt x #x00000000))
      false)))

(check-sat)
(exit)
"#;
    let config = PdrConfig::default();
    let result = testing::pdr_solve_from_str(input, config);
    assert!(
        matches!(&result, Ok(PdrResult::Safe(_))),
        "Simple BV problem should be Safe, got {:?}",
        result.map(|r| format!("{:?}", std::mem::discriminant(&r)))
    );
}
