; QF_BV incremental scoping regression test for multiple internal BV subterms
; Part of #1454 - tests "cached BV internal term across pop" soundness
;
; This test exercises multiple BV operations (bvadd, bvand, concat) that
; generate their own bitblasting circuits.
;
; Expected: sat, sat, sat, unsat
; Unsound behavior: any check returning wrong result

(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))

; Test 1: bvadd caching
(push 1)
(assert (= (bvadd x #x01) #x05))    ; x + 1 = 5, so x = 4
(check-sat)                         ; expected: sat (x = #x04)
(pop 1)

; Test 2: bvand caching
(push 1)
(assert (= (bvand x #x0f) #x07))    ; x & 0x0f = 7, low nibble is 7
(check-sat)                         ; expected: sat
(pop 1)

; Test 3: concat caching
(push 1)
(assert (= (concat x y) #x1234))    ; x ++ y = 0x1234, so x=0x12, y=0x34
(check-sat)                         ; expected: sat
(pop 1)

; Test 4: Reuse bvadd from test 1 with contradiction
(push 1)
(assert (and (= (bvadd x #x01) #x05) (distinct (bvadd x #x01) #x05)))
(check-sat)                         ; expected: unsat
(pop 1)

(exit)
