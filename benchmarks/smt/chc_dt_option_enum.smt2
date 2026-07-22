; CHC with multi-constructor DT (Option-like enum).
; Pattern: inv(x) where x is either None or Some(n) with n > 0.
; Invariant: is-None(x) OR val(x) > 0.
; Expected: sat (safe).
(set-logic HORN)

(declare-datatype OptionInt (
  (None)
  (Some (val Int))))

(declare-fun |inv| (OptionInt) Bool)

; Init: x = Some(42)
(assert
  (forall ((x OptionInt))
    (=> (= x (Some 42))
        (inv x))))

; Trans: x can become None
(assert
  (forall ((x OptionInt))
    (=> (inv x)
        (inv (as None OptionInt)))))

; Bad: is-Some(x) AND val(x) <= 0
(assert
  (forall ((x OptionInt))
    (=> (and (inv x) (is-Some x) (<= (val x) 0))
        false)))

(check-sat)
(exit)
