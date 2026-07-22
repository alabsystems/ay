; Enum variant switching with unsafe property.
; Models a Result<Int, Int> that transitions from Ok to Err.
; Init: Ok(42)
; Trans: Ok(n) => Err(n) (any Ok switches to Err)
; Safety: is-Ok(x) (must always be Ok)
; Expected: unsat (unsafe) -- the transition produces Err.
(set-logic HORN)

(declare-datatype Result (
  (Ok (ok_val Int))
  (Err (err_val Int))))

(declare-fun |inv| (Result) Bool)

; Init: Ok(42)
(assert
  (forall ((r Result))
    (=> (and (is-Ok r) (= (ok_val r) 42))
        (inv r))))

; Trans: Ok(n) transitions to Err(n)
(assert
  (forall ((r Result) (r2 Result))
    (=> (and (inv r) (is-Ok r) (is-Err r2) (= (err_val r2) (ok_val r)))
        (inv r2))))

; Safety: must always be Ok
(assert
  (forall ((r Result))
    (=> (and (inv r) (is-Err r))
        false)))

(check-sat)
(exit)
