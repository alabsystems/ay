; Flat test case for ROW2 (Read-Over-Write different index)
; This tests the core frame condition without nesting

(set-logic QF_AUFLIA)

; A single-level array
(declare-const A (Array Int Int))

; Two distinct indices
(declare-const i Int)
(declare-const j Int)
(assert (not (= i j)))  ; i != j

; Store at index i
(declare-const v Int)
(declare-const A_post (Array Int Int))
(assert (= A_post (store A i v)))

; Frame condition: select(A_post, j) should equal select(A, j)
(declare-const before Int)
(declare-const after Int)
(assert (= before (select A j)))
(assert (= after (select A_post j)))

; Verify frame holds
(assert (not (= before after)))

(check-sat)  ; Expect UNSAT (ROW2 should derive before = after)
