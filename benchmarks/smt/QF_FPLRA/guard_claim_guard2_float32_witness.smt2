; INDEPENDENT SAT WITNESS for `guard_claim_guard2_float32.smt2`.
;
; Pins the concrete binary32 assignment
;   nx = ny = nz = 1.0
;   px = 2^24,  py = 2.0,  pz = 2^-126 (the smallest binary32 NORMAL)
;   d  = 2^48
; under which the six RNE operations evaluate to
;   t1 = 2^24, t2 = 2, t3 = 2^-126,  s1 = s2 = 2^24 + 2,
;   rf = fp.add RNE (2^24+2) 2^48 = 2^48 + 2^25   (the sum rounds UP: the
;        exact value 2^48 + 2^24 + 2 sits just ABOVE the 2^24 midpoint of the
;        2^25-wide binary32 ulp at 2^48)
; so   rf - rreal = 2^25 - 2^24 - 2 - 2^-126 = 16777213.99...  >=  2.
;
; This makes the SATISFIABILITY of the Float32 clone checkable in milliseconds,
; independently of any solver's ability to decide the symbolic version. If a
; forward-error firewall emitter ever fires on the Float32 clone, THIS file is
; the counter-model that refutes it.
(set-info :status sat)
(set-logic QF_FPLRA)
(declare-const nx Float32) (declare-const ny Float32) (declare-const nz Float32)
(declare-const px Float32) (declare-const py Float32) (declare-const pz Float32)
(declare-const d Float32)
(define-fun B () Real 281474976710656.0) ; 2^48
(assert (and (fp.isNormal nx) (<= (fp.to_real (fp.abs nx)) 1.0)))
(assert (and (fp.isNormal ny) (<= (fp.to_real (fp.abs ny)) 1.0)))
(assert (and (fp.isNormal nz) (<= (fp.to_real (fp.abs nz)) 1.0)))
(assert (and (fp.isNormal px) (<= (fp.to_real (fp.abs px)) B)))
(assert (and (fp.isNormal py) (<= (fp.to_real (fp.abs py)) B)))
(assert (and (fp.isNormal pz) (<= (fp.to_real (fp.abs pz)) B)))
(assert (and (fp.isNormal d)  (<= (fp.to_real (fp.abs d))  B)))
; --- the pinned witness -----------------------------------------------------
(assert (= nx ((_ to_fp 8 24) RNE 1.0)))
(assert (= ny ((_ to_fp 8 24) RNE 1.0)))
(assert (= nz ((_ to_fp 8 24) RNE 1.0)))
(assert (= px ((_ to_fp 8 24) RNE 16777216.0)))
(assert (= py ((_ to_fp 8 24) RNE 2.0)))
(assert (= pz (fp #b0 #b00000001 #b00000000000000000000000)))
(assert (= d  ((_ to_fp 8 24) RNE 281474976710656.0)))
; ----------------------------------------------------------------------------
(define-fun t1 () Float32 (fp.mul RNE nx px))
(define-fun t2 () Float32 (fp.mul RNE ny py))
(define-fun t3 () Float32 (fp.mul RNE nz pz))
(define-fun s1 () Float32 (fp.add RNE t1 t2))
(define-fun s2 () Float32 (fp.add RNE s1 t3))
(define-fun rf () Float32 (fp.add RNE s2 d))
(define-fun rreal () Real (+ (* (fp.to_real nx) (fp.to_real px))
                             (* (fp.to_real ny) (fp.to_real py))
                             (* (fp.to_real nz) (fp.to_real pz))
                             (fp.to_real d)))
(assert (>= (- (fp.to_real rf) rreal) 2.0))
(check-sat)
