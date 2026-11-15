; Ground binary128 proof regression: high and low fraction bits matter.
; The independent ground checker must validate the original arithmetic.
(set-logic QF_FP)
(define-fun x () (_ FloatingPoint 15 113) (fp #b0 (_ bv16383 15) (_ bv2596148429267413814265248164610049 112)))
(define-fun y () (_ FloatingPoint 15 113) (fp #b0 (_ bv16384 15) (_ bv2596148429267413814265248164610049 112)))
(define-fun wrong () (_ FloatingPoint 15 113) (fp #b0 (_ bv16384 15) (_ bv2596148429267413814265248164610048 112)))
(define-fun next () (_ FloatingPoint 15 113) (fp #b0 (_ bv16383 15) (_ bv2596148429267413814265248164610050 112)))
(define-fun two () (_ FloatingPoint 15 113) (fp #b0 (_ bv16384 15) (_ bv0 112)))
(assert (not (and
  (fp.eq (fp.add RNE x x) y)
  (not (fp.eq (fp.add RNE x x) wrong))
  (fp.lt x next)
  (fp.lt x two)
  (fp.gt (fp.neg x) (fp.neg next)))))
(check-sat)
