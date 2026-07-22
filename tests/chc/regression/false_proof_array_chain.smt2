; Regression test for #8675: false PROOF on array store/select through long chain
; The error IS reachable (expected: sat / Unsafe).
;
; Encodes a 6-predicate chain with array passing:
; Init -> P1 -> P2 -> P3 -> P4 -> P5 -> Error
; At Init: store obj_size[id]=64
; At Error: check select(obj_size, id) != 32 (64 != 32, so reachable)
; Each intermediate predicate passes obj_size and id unchanged, plus
; accumulates an extra integer variable (simulating real program state).

(set-logic HORN)

(declare-fun P1 ((Array Int Int) Int Int) Bool)
(declare-fun P2 ((Array Int Int) Int Int) Bool)
(declare-fun P3 ((Array Int Int) Int Int) Bool)
(declare-fun P4 ((Array Int Int) Int Int) Bool)
(declare-fun P5 ((Array Int Int) Int Int) Bool)

; Fact: obj_size = store(empty, 0, 64), id = 0, ctr = 0
(assert (forall ((obj_size (Array Int Int)) (id Int) (ctr Int))
  (=> (and (= id 0)
           (= ctr 0)
           (= obj_size (store ((as const (Array Int Int)) 0) 0 64)))
      (P1 obj_size id ctr))))

; P1 -> P2: pass array through, increment ctr
(assert (forall ((obj_size (Array Int Int)) (id Int) (ctr Int) (ctr2 Int))
  (=> (and (P1 obj_size id ctr) (= ctr2 (+ ctr 1)))
      (P2 obj_size id ctr2))))

; P2 -> P3: pass array through, increment ctr
(assert (forall ((obj_size (Array Int Int)) (id Int) (ctr Int) (ctr2 Int))
  (=> (and (P2 obj_size id ctr) (= ctr2 (+ ctr 1)))
      (P3 obj_size id ctr2))))

; P3 -> P4: pass array through, increment ctr
(assert (forall ((obj_size (Array Int Int)) (id Int) (ctr Int) (ctr2 Int))
  (=> (and (P3 obj_size id ctr) (= ctr2 (+ ctr 1)))
      (P4 obj_size id ctr2))))

; P4 -> P5: pass array through, increment ctr
(assert (forall ((obj_size (Array Int Int)) (id Int) (ctr Int) (ctr2 Int))
  (=> (and (P4 obj_size id ctr) (= ctr2 (+ ctr 1)))
      (P5 obj_size id ctr2))))

; Error: P5(obj_size, id, ctr) /\ select(obj_size, id) != 32 => false
; Since obj_size[0] = 64 and 64 != 32, this IS satisfiable -> UNSAFE
(assert (forall ((obj_size (Array Int Int)) (id Int) (ctr Int))
  (=> (and (P5 obj_size id ctr)
           (not (= (select obj_size id) 32)))
      false)))

(check-sat)
