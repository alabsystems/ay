; geometry_consumer GUARD claim (the development design notes in the geometry_consumer repo):
; one signed-distance evaluation r = nx*px + ny*py + nz*pz + d in f64,
; inputs normal with |n*| <= 1 and |p*|,|d| <= 2^48; claim |r_f64 - r_real| < 0.3.
; Refuted by the FP forward-error tactic: the certified accumulated bound is
; 13/64 = 0.203125 (binade-aware half-ulp model), so asserting error >= 0.3
; is UNSAT. The bit-precise fp.to_real refinement lane alone answers unknown.
(set-info :status unsat)
(set-logic QF_FPLRA)
(declare-const nx Float64) (declare-const ny Float64) (declare-const nz Float64)
(declare-const px Float64) (declare-const py Float64) (declare-const pz Float64)
(declare-const d Float64)
(define-fun B () Real 281474976710656.0) ; 2^48
(assert (and (fp.isNormal nx) (<= (fp.to_real (fp.abs nx)) 1.0)))
(assert (and (fp.isNormal ny) (<= (fp.to_real (fp.abs ny)) 1.0)))
(assert (and (fp.isNormal nz) (<= (fp.to_real (fp.abs nz)) 1.0)))
(assert (and (fp.isNormal px) (<= (fp.to_real (fp.abs px)) B)))
(assert (and (fp.isNormal py) (<= (fp.to_real (fp.abs py)) B)))
(assert (and (fp.isNormal pz) (<= (fp.to_real (fp.abs pz)) B)))
(assert (and (fp.isNormal d)  (<= (fp.to_real (fp.abs d))  B)))
(define-fun t1 () Float64 (fp.mul RNE nx px))
(define-fun t2 () Float64 (fp.mul RNE ny py))
(define-fun t3 () Float64 (fp.mul RNE nz pz))
(define-fun s1 () Float64 (fp.add RNE t1 t2))
(define-fun s2 () Float64 (fp.add RNE s1 t3))
(define-fun rf () Float64 (fp.add RNE s2 d))
(define-fun rreal () Real (+ (* (fp.to_real nx) (fp.to_real px))
                             (* (fp.to_real ny) (fp.to_real py))
                             (* (fp.to_real nz) (fp.to_real pz))
                             (fp.to_real d)))
; Refute: error >= 0.3 (unsat proves the GUARD claim)
(assert (>= (- (fp.to_real rf) rreal) 0.3))
(check-sat)
