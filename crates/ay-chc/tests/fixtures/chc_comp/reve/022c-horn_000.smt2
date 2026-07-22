(set-logic HORN)


(declare-fun |INV1| ( Int Int Int Int Int Int ) Bool)
(declare-fun |INV3| ( Int Int Int ) Bool)
(declare-fun |INV2| ( Int Int Int Int Int Int ) Bool)
(declare-fun |INV4| ( Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (INV1 F H G A D E)
        (let ((a!1 (not (>= (+ F (* (- 1) G)) 1))))
  (and (= I J)
       (= E (+ (- 1) C))
       (= D (+ 2 B))
       a!1
       (>= (+ A (* (- 1) E)) 1)
       (= K L)))
      )
      (INV3 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) ) 
    (=>
      (and
        (INV1 A B C G I H)
        (INV3 D E F)
        (let ((a!1 (not (>= (+ A (* (- 1) C)) 1))) (a!2 (not (>= (+ F (* (- 1) D)) 1))))
  (and (= J K) a!1 (>= (+ G (* (- 1) H)) 1) a!2 (= L M)))
      )
      (INV1 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) ) 
    (=>
      (and
        (INV1 F J G H K I)
        (INV3 D E C)
        (let ((a!1 (not (>= (+ F (* (- 1) G)) 1))))
  (and (= L M)
       (= E (+ (- 2) B))
       (= D (+ (- 1) A))
       (>= (+ C (* (- 1) D)) 1)
       (>= (+ H (* (- 1) I)) 1)
       a!1
       (= N O)))
      )
      (INV3 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) ) 
    (=>
      (and
        (INV1 A G H D I J)
        (and (= K L)
     (= J (+ (- 1) F))
     (= I (+ 2 E))
     (= H (+ (- 1) C))
     (= G (+ 1 B))
     (>= (+ A (* (- 1) H)) 1)
     (>= (+ D (* (- 1) J)) 1)
     (= M N))
      )
      (INV2 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) ) 
    (=>
      (and
        (INV1 G K H I L J)
        (INV2 A B C D E F)
        (let ((a!1 (not (>= (+ C (* (- 1) A)) 1))) (a!2 (not (>= (+ F (* (- 1) D)) 1))))
  (and (= M N)
       a!1
       (>= (+ I (* (- 1) J)) 1)
       (>= (+ G (* (- 1) H)) 1)
       a!2
       (= O P)))
      )
      (INV1 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) ) 
    (=>
      (and
        (INV1 I M J K N L)
        (INV2 A B C G H F)
        (let ((a!1 (not (>= (+ C (* (- 1) A)) 1))))
  (and (= O P)
       (= H (+ (- 2) E))
       (= G (+ (- 1) D))
       a!1
       (>= (+ F (* (- 1) G)) 1)
       (>= (+ K (* (- 1) L)) 1)
       (>= (+ I (* (- 1) J)) 1)
       (= Q R)))
      )
      (INV2 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) ) 
    (=>
      (and
        (INV1 K O L M P N)
        (INV2 G H C I J F)
        (and (= H (+ (- 1) B))
     (= S T)
     (= Q R)
     (= J (+ (- 2) E))
     (= I (+ (- 1) D))
     (>= (+ C (* (- 1) G)) 1)
     (>= (+ F (* (- 1) I)) 1)
     (>= (+ M (* (- 1) N)) 1)
     (>= (+ K (* (- 1) L)) 1)
     (= G (+ (- 1) A)))
      )
      (INV2 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) ) 
    (=>
      (and
        (INV1 I M J K N L)
        (INV2 G H C D E F)
        (let ((a!1 (not (>= (+ F (* (- 1) D)) 1))))
  (and (= O P)
       (= H (+ (- 1) B))
       (= G (+ (- 1) A))
       (>= (+ C (* (- 1) G)) 1)
       a!1
       (>= (+ K (* (- 1) L)) 1)
       (>= (+ I (* (- 1) J)) 1)
       (= Q R)))
      )
      (INV2 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) ) 
    (=>
      (and
        (INV1 F J G H K I)
        (INV4 D E C)
        (let ((a!1 (not (>= (+ H (* (- 1) I)) 1))))
  (and (= L M)
       (= E (+ (- 1) B))
       (= D (+ (- 1) A))
       (>= (+ C (* (- 1) D)) 1)
       a!1
       (>= (+ F (* (- 1) G)) 1)
       (= N O)))
      )
      (INV4 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) ) 
    (=>
      (and
        (INV1 G I H D E F)
        (INV4 A B C)
        (let ((a!1 (not (>= (+ D (* (- 1) F)) 1))) (a!2 (not (>= (+ C (* (- 1) A)) 1))))
  (and (= J K) (>= (+ G (* (- 1) H)) 1) a!1 a!2 (= L M)))
      )
      (INV1 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (INV1 A D E F H G)
        (let ((a!1 (not (>= (+ F (* (- 1) G)) 1))))
  (and (= I J)
       (= E (+ (- 1) C))
       (= D (+ 1 B))
       a!1
       (>= (+ A (* (- 1) E)) 1)
       (= K L)))
      )
      (INV4 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (and (= C 0) (= B E) (= A D) (= F 0))
      )
      (INV1 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (INV1 C A D E B F)
        (let ((a!1 (not (>= (+ E (* (- 1) F)) 1))) (a!2 (not (>= (+ C (* (- 1) D)) 1))))
  (and (= G H) (not (= A B)) a!1 a!2 (= I J)))
      )
      false
    )
  )
)

(check-sat)
(exit)
