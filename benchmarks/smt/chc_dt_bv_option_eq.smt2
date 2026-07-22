; CHC with DT+BV: Option<BV8> equality comparison.
; Pattern: inv(x, y) where x, y are Option(BV8).
; Init: x = Some(4), y = Some(4).
; Trans: identity (x' = x, y' = y).
; Safety: field_0(x) = field_0(y) when both are Some.
; Expected: sat (safe).
;
; Regression test for #7930: DT+BV problems must not enter the BV dual-lane
; in the adaptive solver. BvToBool/BvToInt preprocessing does not handle DT
; constructor/selector operations, causing combinatorial blowup and timeout.
(set-logic HORN)

(declare-datatype OptionBV8 (
  (None)
  (Some (val (_ BitVec 8)))))

(declare-fun |inv| (OptionBV8 OptionBV8) Bool)

; Init: x = Some(#x04), y = Some(#x04)
(assert
  (forall ((x OptionBV8) (y OptionBV8))
    (=> (and (= x (Some #x04)) (= y (Some #x04)))
        (inv x y))))

; Trans: identity
(assert
  (forall ((x OptionBV8) (y OptionBV8) (x2 OptionBV8) (y2 OptionBV8))
    (=> (and (inv x y) (= x2 x) (= y2 y))
        (inv x2 y2))))

; Safety: if both are Some, their values are equal
(assert
  (forall ((x OptionBV8) (y OptionBV8))
    (=> (and (inv x y) (is-Some x) (is-Some y) (not (= (val x) (val y))))
        false)))

(check-sat)
(exit)
