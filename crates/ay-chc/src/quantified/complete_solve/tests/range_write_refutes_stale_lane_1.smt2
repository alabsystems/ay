;; A run of lanes [1, 3) of `d` takes `s[0..2)`: `memcpy(&d[1], &s[0], 2)` on
;; `[u8; 4]` cells. One fresh array `w` and ONE universal premise define the
;; write, whatever the run's length: the constant-size form model-checker-consumer needs.
(set-logic HORN)
(declare-fun Written ((Array (_ BitVec 64) (_ BitVec 8))) Bool)
(assert (forall ((d (Array (_ BitVec 64) (_ BitVec 8))) (s (Array (_ BitVec 64) (_ BitVec 8))) (w (Array (_ BitVec 64) (_ BitVec 8))))
  (=> (and (= (select d #x0000000000000000) #x07)
           (= (select s #x0000000000000000) #x09)
           (forall ((i (_ BitVec 64)))
             (= (select w i)
                (ite (and (bvule #x0000000000000001 i) (bvult i #x0000000000000003))
                     (select s (bvsub i #x0000000000000001))
                     (select d i)))))
      (Written w))))
(assert (forall ((w (Array (_ BitVec 64) (_ BitVec 8))))
  (=> (and (Written w) (= (select w #x0000000000000001) #x09)) false)))
(check-sat)
