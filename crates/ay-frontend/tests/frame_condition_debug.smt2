; Debug version: explicit syntactic distinctness
; This should work because distinct creates an equality literal

(set-logic QF_AUFLIA)

(declare-const A (Array Int Int))
(declare-const i Int)
(declare-const j Int)

; Make i and j syntactically bound to distinct values
; This removes any EUF reasoning dependency
(assert (= i 0))
(assert (= j 1))

; Store at index i=0
(declare-const v Int)
(declare-const A_post (Array Int Int))
(assert (= A_post (store A i v)))

; Read at index j=1
(declare-const before Int)
(declare-const after Int)
(assert (= before (select A j)))
(assert (= after (select A_post j)))

; Verify frame holds
(assert (not (= before after)))

(check-sat)  ; Expect UNSAT
