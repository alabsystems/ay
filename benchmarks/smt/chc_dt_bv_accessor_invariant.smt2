; CHC with DT+BV: Safe invariant requires DT accessor terms.
; Pattern: inv(x, y) where x,y : Option(BV8).
; Init: x = Some(#x00), y = Some(#x00).
; Trans: x' = Some(bvadd (val x) 1), y' = Some(bvadd (val y) 1).
; Safety: when both are Some, val(x) == val(y).
;
; The invariant must mention (val x) and (val y) — DT accessors — to express
; "the BV8 fields of the two Some constructors are always equal."
; This directly tests what model-checker-consumer's workarounds currently avoid.
;
; Unlike chc_dt_bv_option_eq.smt2 which keeps values constant, this one
; INCREMENTS them in lockstep, requiring the solver to discover that
; the values remain synchronized.
;
; Expected: sat (safe). Invariant: val(x) = val(y).
(set-logic HORN)

(declare-datatype OptBV8 (
  (none8)
  (some8 (val8 (_ BitVec 8)))))

(declare-fun |inv| (OptBV8 OptBV8) Bool)

; Init: x = some8(#x00), y = some8(#x00)
(assert
  (forall ((x OptBV8) (y OptBV8))
    (=> (and (= x (some8 #x00)) (= y (some8 #x00)))
        (inv x y))))

; Trans: increment both values in lockstep
(assert
  (forall ((x OptBV8) (y OptBV8) (x2 OptBV8) (y2 OptBV8))
    (=> (and (inv x y)
             (is-some8 x) (is-some8 y)
             (= x2 (some8 (bvadd (val8 x) #x01)))
             (= y2 (some8 (bvadd (val8 y) #x01))))
        (inv x2 y2))))

; Safety: when both Some, values are equal
(assert
  (forall ((x OptBV8) (y OptBV8))
    (=> (and (inv x y) (is-some8 x) (is-some8 y)
             (not (= (val8 x) (val8 y))))
        false)))

(check-sat)
(exit)
