; Issue #8717 Phase 2 completeness floor.
; BV+Int Horn loop with `bvshl` state update (Z3 #1634 shape).
; Expected: sat (SAFE) — Z3 solves, AY currently times out.
;
; Init: x = bv0, i = 0
; Trans: i' = i + 1, x' = bvshl(x, 4), guard i < 3
; Query: reaching (i >= 3) with x /= bv0 is false
;        (bvshl bv0 k = bv0 for every k, so x stays bv0 forever)
(set-logic HORN)

(declare-fun Inv ((_ BitVec 32) Int) Bool)

(assert
  (forall ((x (_ BitVec 32)) (i Int))
    (=> (and (= x (_ bv0 32)) (= i 0))
        (Inv x i))))

(assert
  (forall ((x (_ BitVec 32)) (i Int) (xp (_ BitVec 32)) (ip Int))
    (=> (and (Inv x i)
             (< i 3)
             (= ip (+ i 1))
             (= xp (bvshl x (_ bv4 32))))
        (Inv xp ip))))

(assert
  (forall ((x (_ BitVec 32)) (i Int))
    (=> (and (Inv x i) (>= i 3) (not (= x (_ bv0 32))))
        false)))

(check-sat)
