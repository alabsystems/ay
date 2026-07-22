; CHC with wide BV multiplication — exercises delayed internalization in CHC/PDR path
; Expected: unsat (unsafe — counterexample exists)
;
; Models a counter that doubles each step via 16-bit multiplication.
; After enough doublings, 16-bit overflow wraps to 0.
;   init: x = 1
;   trans: x' = bvmul(x, 2)
;   bad: x = 0 (reachable: 1 * 2^16 = 0 mod 2^16)

(set-logic HORN)

(declare-fun Inv ((_ BitVec 16)) Bool)

; Init: x = 1
(assert (forall ((x (_ BitVec 16)))
  (=> (= x #x0001) (Inv x))))

; Trans: x' = x * 2
(assert (forall ((x (_ BitVec 16)) (xp (_ BitVec 16)))
  (=> (and (Inv x) (= xp (bvmul x #x0002))) (Inv xp))))

; Bad: x = 0 (reachable after 16 doublings)
(assert (forall ((x (_ BitVec 16)))
  (=> (and (Inv x) (= x #x0000)) false)))

(check-sat)
