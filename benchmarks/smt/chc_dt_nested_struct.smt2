; Nested datatype: Outer contains Inner struct.
; Tests DT flattening with nested struct fields.
; Init: inner.x = 0, outer.tag = 1
; Trans: inner.x' = inner.x + 1
; Safety: inner.x >= 0
; Expected: sat (safe) -- x starts at 0 and only increments.
(set-logic HORN)

(declare-datatype Inner ((mkInner (ix Int))))
(declare-datatype Outer ((mkOuter (tag Int) (payload Inner))))

(declare-fun |inv| (Outer) Bool)

; Init: Outer(1, Inner(0))
(assert
  (forall ((o Outer))
    (=> (and (= (tag o) 1) (= (ix (payload o)) 0))
        (inv o))))

; Trans: increment inner x, keep tag
(assert
  (forall ((o Outer) (o2 Outer))
    (=> (and (inv o)
             (= (tag o2) (tag o))
             (= (ix (payload o2)) (+ (ix (payload o)) 1)))
        (inv o2))))

; Safety: inner x >= 0
(assert
  (forall ((o Outer))
    (=> (and (inv o) (< (ix (payload o)) 0))
        false)))

(check-sat)
(exit)
