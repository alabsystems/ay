; CHC with mutually recursive datatypes via declare-datatypes (plural).
; Pattern: Tree/Forest types with structural invariant.
; Invariant: all leaf values in the tree are non-negative.
; Expected: sat (safe) -- init creates a single leaf(42).
(set-logic HORN)

(declare-datatypes ((Tree 0) (Forest 0))
  (((leaf (val Int)) (node (children Forest)))
   ((nil) (cons (head Tree) (tail Forest)))))

(declare-fun |inv| (Tree) Bool)

; Init: t = leaf(42)
(assert
  (forall ((t Tree))
    (=> (= t (leaf 42))
        (inv t))))

; Trans: identity
(assert
  (forall ((t Tree))
    (=> (inv t) (inv t))))

; Bad: is-leaf(t) AND val(t) < 0
(assert
  (forall ((t Tree))
    (=> (and (inv t) (is-leaf t) (< (val t) 0))
        false)))

(check-sat)
(exit)
