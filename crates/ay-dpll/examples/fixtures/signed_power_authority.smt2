(set-logic QF_BV)
(declare-const x (_ BitVec 5))
(assert (= (bvsdiv x (_ bv3 5)) (ite (bvslt x (_ bv0 5)) (bvneg (bvlshr (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5))) (bvlshr (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5)))))
; CASE
(set-logic QF_BV)
(declare-const x (_ BitVec 5))
(assert (= (bvsrem x (_ bv3 5)) (ite (bvslt x (_ bv0 5)) (bvneg (bvand (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5))) (bvand (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5)))))
; CASE
(set-logic QF_BV)
(declare-const x (_ BitVec 5))
(assert (= (bvsmod x (_ bv3 5)) (bvand x (_ bv1 5))))
; CASE
(set-logic QF_BV)
(declare-const x (_ BitVec 5))
(assert (= (bvsdiv x (_ bv29 5)) (bvneg (ite (bvslt x (_ bv0 5)) (bvneg (bvlshr (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5))) (bvlshr (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5))))))
; CASE
(set-logic QF_BV)
(declare-const x (_ BitVec 5))
(assert (= (bvsrem x (_ bv29 5)) (ite (bvslt x (_ bv0 5)) (bvneg (bvand (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5))) (bvand (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5)))))
; CASE
(set-logic QF_BV)
(declare-const x (_ BitVec 5))
(assert (= (bvsmod x (_ bv29 5)) (bvneg (bvand (bvneg x) (_ bv1 5)))))
; CASE
(set-logic QF_BV)
(declare-const x (_ BitVec 5))
(assert (= (bvsdiv x (_ bv5 5)) (ite (bvslt x (_ bv0 5)) (bvneg (bvlshr (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5))) (bvlshr (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5)))))
; CASE
(set-logic QF_BV)
(declare-const x (_ BitVec 5))
(assert (= (bvsrem x (_ bv5 5)) (ite (bvslt x (_ bv0 5)) (bvneg (bvand (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5))) (bvand (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5)))))
; CASE
(set-logic QF_BV)
(declare-const x (_ BitVec 5))
(assert (= (bvsmod x (_ bv5 5)) (bvand x (_ bv1 5))))
; CASE
(set-logic QF_BV)
(declare-const x (_ BitVec 5))
(assert (= (bvsdiv x (_ bv27 5)) (bvneg (ite (bvslt x (_ bv0 5)) (bvneg (bvlshr (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5))) (bvlshr (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5))))))
; CASE
(set-logic QF_BV)
(declare-const x (_ BitVec 5))
(assert (= (bvsrem x (_ bv27 5)) (ite (bvslt x (_ bv0 5)) (bvneg (bvand (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5))) (bvand (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5)))))
; CASE
(set-logic QF_BV)
(declare-const x (_ BitVec 5))
(assert (= (bvsmod x (_ bv27 5)) (bvneg (bvand (bvneg x) (_ bv1 5)))))
; CASE
(set-logic QF_BV)
(declare-const x (_ BitVec 128))
(assert (= (bvsdiv x (_ bv3 128)) (ite (bvslt x (_ bv0 128)) (bvneg (bvlshr (ite (bvslt x (_ bv0 128)) (bvneg x) x) (_ bv1 128))) (bvlshr (ite (bvslt x (_ bv0 128)) (bvneg x) x) (_ bv1 128)))))
; CASE
(set-logic QF_BV)
(declare-const x (_ BitVec 128))
(assert (= (bvsrem x (_ bv3 128)) (ite (bvslt x (_ bv0 128)) (bvneg (bvand (ite (bvslt x (_ bv0 128)) (bvneg x) x) (_ bv1 128))) (bvand (ite (bvslt x (_ bv0 128)) (bvneg x) x) (_ bv1 128)))))
; CASE
(set-logic QF_BV)
(declare-const x (_ BitVec 128))
(assert (= (bvsmod x (_ bv3 128)) (bvand x (_ bv1 128))))
; CASE
(set-logic QF_BV)
(declare-const x (_ BitVec 128))
(assert (= (bvsdiv x (_ bv340282366920938463463374607431768211453 128)) (bvneg (ite (bvslt x (_ bv0 128)) (bvneg (bvlshr (ite (bvslt x (_ bv0 128)) (bvneg x) x) (_ bv1 128))) (bvlshr (ite (bvslt x (_ bv0 128)) (bvneg x) x) (_ bv1 128))))))
; CASE
(set-logic QF_BV)
(declare-const x (_ BitVec 128))
(assert (= (bvsrem x (_ bv340282366920938463463374607431768211453 128)) (ite (bvslt x (_ bv0 128)) (bvneg (bvand (ite (bvslt x (_ bv0 128)) (bvneg x) x) (_ bv1 128))) (bvand (ite (bvslt x (_ bv0 128)) (bvneg x) x) (_ bv1 128)))))
; CASE
(set-logic QF_BV)
(declare-const x (_ BitVec 128))
(assert (= (bvsmod x (_ bv340282366920938463463374607431768211453 128)) (bvneg (bvand (bvneg x) (_ bv1 128)))))
; CASE
(set-logic QF_BV)
(declare-const x (_ BitVec 128))
(assert (= (bvsdiv x (_ bv5 128)) (ite (bvslt x (_ bv0 128)) (bvneg (bvlshr (ite (bvslt x (_ bv0 128)) (bvneg x) x) (_ bv1 128))) (bvlshr (ite (bvslt x (_ bv0 128)) (bvneg x) x) (_ bv1 128)))))
; CASE
(set-logic QF_BV)
(declare-const x (_ BitVec 128))
(assert (= (bvsrem x (_ bv5 128)) (ite (bvslt x (_ bv0 128)) (bvneg (bvand (ite (bvslt x (_ bv0 128)) (bvneg x) x) (_ bv1 128))) (bvand (ite (bvslt x (_ bv0 128)) (bvneg x) x) (_ bv1 128)))))
; CASE
(set-logic QF_BV)
(declare-const x (_ BitVec 128))
(assert (= (bvsmod x (_ bv5 128)) (bvand x (_ bv1 128))))
; CASE
(set-logic QF_BV)
(declare-const x (_ BitVec 128))
(assert (= (bvsdiv x (_ bv340282366920938463463374607431768211451 128)) (bvneg (ite (bvslt x (_ bv0 128)) (bvneg (bvlshr (ite (bvslt x (_ bv0 128)) (bvneg x) x) (_ bv1 128))) (bvlshr (ite (bvslt x (_ bv0 128)) (bvneg x) x) (_ bv1 128))))))
; CASE
(set-logic QF_BV)
(declare-const x (_ BitVec 128))
(assert (= (bvsrem x (_ bv340282366920938463463374607431768211451 128)) (ite (bvslt x (_ bv0 128)) (bvneg (bvand (ite (bvslt x (_ bv0 128)) (bvneg x) x) (_ bv1 128))) (bvand (ite (bvslt x (_ bv0 128)) (bvneg x) x) (_ bv1 128)))))
; CASE
(set-logic QF_BV)
(declare-const x (_ BitVec 128))
(assert (= (bvsmod x (_ bv340282366920938463463374607431768211451 128)) (bvneg (bvand (bvneg x) (_ bv1 128)))))
; CASE
(declare-const x (_ BitVec 5))
(assert (not (= (bvsdiv x (_ bv2 5)) (ite (bvslt x (_ bv0 5)) (bvneg (bvlshr (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5))) (bvlshr (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5))))))
; CASE
(declare-const x (_ BitVec 5))
(assert (not (= (bvsdiv x (_ bv30 5)) (bvneg (ite (bvslt x (_ bv0 5)) (bvneg (bvlshr (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5))) (bvlshr (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5)))))))
; CASE
(declare-const x (_ BitVec 5))
(assert (not (= (bvsrem x (_ bv2 5)) (ite (bvslt x (_ bv0 5)) (bvneg (bvand (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5))) (bvand (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5))))))
; CASE
(declare-const x (_ BitVec 5))
(assert (not (= (bvsrem x (_ bv30 5)) (ite (bvslt x (_ bv0 5)) (bvneg (bvand (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5))) (bvand (ite (bvslt x (_ bv0 5)) (bvneg x) x) (_ bv1 5))))))
; CASE
(declare-const x (_ BitVec 5))
(assert (not (= (bvsmod x (_ bv2 5)) (bvand x (_ bv1 5)))))
; CASE
(declare-const x (_ BitVec 5))
(assert (not (= (bvsmod x (_ bv30 5)) (bvneg (bvand (bvneg x) (_ bv1 5))))))
