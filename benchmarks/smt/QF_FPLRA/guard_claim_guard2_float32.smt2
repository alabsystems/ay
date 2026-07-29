; FORMAT TRAP for the FP dot-product forward-error firewall emitter.
;
; This is a Float32 clone of `guard_claim_guard2.smt2`. Its PARSED ASSERTION
; TERMS are byte-identical to the Float64 original — the only difference is in
; the DECLARATION sorts, which the parsed terms do not carry. The Float64
; original is UNSAT (the binary64 half-ULP forward error of the six-operation
; RNE dot product is at most 17/64 < 2); this Float32 clone is SATISFIABLE,
; because the binary32 half-ULP error at |p| <= 2^48 reaches ~2^24 >> 2.
;
; SAT is established by `guard_claim_guard2_float32_witness.smt2`, which pins a
; concrete binary32 model with forward error 16777214 >= 2 (z3 5.0.0 and ay both
; answer `sat` on it in milliseconds). z3 5.0.0 does NOT decide this symbolic
; version within 900s, and ay answers `unknown`.
;
; An error-bound emitter that classifies by TERM SHAPE ALONE would therefore
; emit a `no_model` certificate for a SATISFIABLE formula. Any such emitter
; MUST read the declared floating-point format and require binary64.
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
