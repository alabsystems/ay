(set-info :status unsat)
(set-logic QF_BV)
; 8-bit unsigned: x + y = 256 is impossible since max is 255
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (bvugt x #x00))
(assert (bvugt y #x00))
; bvadd wraps around modulo 256, so bvadd(x,y) can equal 0 (overflow)
; but we need bvadd(x,y) > x AND bvadd(x,y) > y -- impossible if overflow occurs
; Actually, test a simpler contradiction:
(assert (= x #xFF))
(assert (bvugt (bvadd x #x01) x))
; 0xFF + 1 = 0x00 which is not > 0xFF
(check-sat)
(exit)
