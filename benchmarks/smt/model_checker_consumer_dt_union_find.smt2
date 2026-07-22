; model-checker-consumer-style union-find datatype CHC benchmark.
; Models: A struct with parent pointer and rank, with find/union operations.
; The invariant is that after union, both elements point to the same root.
; This pattern involves nested struct access and conditional mutation.
;
; Expected: sat (safe) - Z3 Spacer proves this
(set-logic HORN)

(declare-datatype Node ((mk-node (parent Int) (rank Int) (value Int))))

(declare-fun Inv (Node Node Int) Bool)

; Init: Two nodes, each is its own root (parent = value), rank = 0
(assert (forall ((a Node) (b Node) (step Int))
  (=> (and (= (parent a) (value a))
           (= (parent b) (value b))
           (= (rank a) 0)
           (= (rank b) 0)
           (= (value a) 0)
           (= (value b) 1)
           (= step 0))
      (Inv a b step))))

; Transition: union operation - make b's root point to a's root
; After union: both have same parent (a's value)
(assert (forall ((a Node) (b Node) (step Int)
                 (a1 Node) (b1 Node) (step1 Int))
  (=> (and (Inv a b step)
           (= step 0)
           (= (parent a1) (parent a))
           (= (rank a1) (rank a))
           (= (value a1) (value a))
           (= (parent b1) (value a))
           (= (rank b1) (rank b))
           (= (value b1) (value b))
           (= step1 1))
      (Inv a1 b1 step1))))

; Safety: after union (step = 1), b's parent should be a's value
(assert (forall ((a Node) (b Node) (step Int))
  (=> (and (Inv a b step)
           (= step 1)
           (not (= (parent b) (value a))))
      false)))

(check-sat)
(exit)
