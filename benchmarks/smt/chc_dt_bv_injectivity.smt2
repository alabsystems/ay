; CHC with DT+BV: Tests injectivity reasoning.
; Pattern: two Option(BV16) values that are always equal.
; Init: x = some(#x0000), y = some(#x0000)
; Trans: x' = some(bvadd (val x) 1), y' = some(bvadd (val y) 1)
; Safety: x = y (always)
;
; Injectivity is needed: if some(val_x) = some(val_y) then val_x = val_y.
; The DT axiom generator must produce injectivity axioms (F) for this
; to be provable through the DT-flatten + BV pipeline.
;
; Expected: sat (safe).
(set-logic HORN)

(declare-datatype OptBV16 (
  (none16)
  (some16 (val16 (_ BitVec 16)))))

(declare-fun |inv| (OptBV16 OptBV16) Bool)

; Init: both start at some16(0)
(assert
  (forall ((x OptBV16) (y OptBV16))
    (=> (and (= x (some16 #x0000)) (= y (some16 #x0000)))
        (inv x y))))

; Trans: increment both in lockstep
(assert
  (forall ((x OptBV16) (y OptBV16) (x2 OptBV16) (y2 OptBV16))
    (=> (and (inv x y)
             (is-some16 x) (is-some16 y)
             (= x2 (some16 (bvadd (val16 x) #x0001)))
             (= y2 (some16 (bvadd (val16 y) #x0001))))
        (inv x2 y2))))

; Safety: x and y always have equal values
(assert
  (forall ((x OptBV16) (y OptBV16))
    (=> (and (inv x y) (not (= x y)))
        false)))

(check-sat)
(exit)
