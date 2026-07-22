; CHC with nested DT+BV: Struct containing enum containing BV fields.
; Pattern from Rust: struct State { tag: Result<u8, u8>, counter: BV8 }
; where Result<u8,u8> = Ok(BV8) | Err(BV8).
;
; Init: state = MkState(Ok(#x00), #x00)
; Trans: increment counter and keep same result tag
; Safety: counter == ok_val when tag is Ok
;
; The invariant must reason about nested DT fields:
;   (ok_val (tag state)) == (counter state)
; This tests the DT flattener + BV dual-lane path on nested DTs.
;
; Expected: sat (safe).
(set-logic HORN)

(declare-datatypes (
  (Result8 0)
  (State 0)
) (
  ((ok (ok_val (_ BitVec 8))) (err (err_val (_ BitVec 8))))
  ((MkState (tag Result8) (counter (_ BitVec 8))))
))

(declare-fun |inv| (State) Bool)

; Init: state = MkState(ok(#x00), #x00)
(assert
  (forall ((s State))
    (=> (= s (MkState (ok #x00) #x00))
        (inv s))))

; Trans: increment counter and ok_val in lockstep
(assert
  (forall ((s State) (s2 State))
    (=> (and (inv s)
             (is-ok (tag s))
             (= s2 (MkState
                      (ok (bvadd (ok_val (tag s)) #x01))
                      (bvadd (counter s) #x01))))
        (inv s2))))

; Safety: when tag is Ok, ok_val == counter
(assert
  (forall ((s State))
    (=> (and (inv s)
             (is-ok (tag s))
             (not (= (ok_val (tag s)) (counter s))))
        false)))

(check-sat)
(exit)
