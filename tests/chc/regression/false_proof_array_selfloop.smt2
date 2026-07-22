; Regression test for #8675: false PROOF on array store/select with self-loop
; The error IS reachable (expected: unsat / Unsafe).
;
; Encodes: store obj_size[0]=64 at init, loop incrementing pc,
; check select(obj_size, 0) != 32 when pc >= 2.
; Since obj_size[0] stays 64 through the loop and 64 != 32,
; the error IS reachable at pc=2.

(set-logic HORN)

(declare-fun Inv ((Array Int Int) Int) Bool)

; Fact: obj_size = store(empty, 0, 64), pc = 0
(assert (forall ((obj_size (Array Int Int)) (pc Int))
  (=> (and (= pc 0)
           (= obj_size (store ((as const (Array Int Int)) 0) 0 64)))
      (Inv obj_size pc))))

; Transition: Inv(obj_size, pc) /\ pc < 5 => Inv(obj_size, pc + 1)
; Array passes through unchanged
(assert (forall ((obj_size (Array Int Int)) (pc Int) (pc2 Int))
  (=> (and (Inv obj_size pc)
           (< pc 5)
           (= pc2 (+ pc 1)))
      (Inv obj_size pc2))))

; Error: Inv(obj_size, pc) /\ pc >= 2 /\ select(obj_size, 0) != 32 => false
; Since obj_size[0] = 64 and 64 != 32, this IS reachable at pc=2 -> UNSAFE
(assert (forall ((obj_size (Array Int Int)) (pc Int))
  (=> (and (Inv obj_size pc)
           (>= pc 2)
           (not (= (select obj_size 0) 32)))
      false)))

(check-sat)
