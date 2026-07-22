; Minimal csplit-query-like benchmark that should be UNSAT.
; Pattern: many constant-indexed selects on a declared array (trivial reads),
; plus store chains with conflicting constraints.
(set-logic QF_ABV)

; Declare arrays
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 32) (_ BitVec 8)))

; Many trivial constant-indexed selects (padding to push select count high)
(declare-fun x0 () (_ BitVec 8))
(declare-fun x1 () (_ BitVec 8))
(declare-fun x2 () (_ BitVec 8))
(declare-fun x3 () (_ BitVec 8))
(declare-fun x4 () (_ BitVec 8))
(declare-fun x5 () (_ BitVec 8))
(declare-fun x6 () (_ BitVec 8))
(declare-fun x7 () (_ BitVec 8))

(assert (= x0 (select a #x00000000)))
(assert (= x1 (select a #x00000001)))
(assert (= x2 (select a #x00000002)))
(assert (= x3 (select a #x00000003)))
(assert (= x4 (select a #x00000004)))
(assert (= x5 (select a #x00000005)))
(assert (= x6 (select a #x00000006)))
(assert (= x7 (select a #x00000007)))

; Core UNSAT constraint via store chain:
; b = store(a, #x00000000, #xFF)
; Then select(b, #x00000000) must be #xFF
; But we also assert select(b, #x00000000) = #x00
(assert (= b (store a #x00000000 #xFF)))
(assert (= (select b #x00000000) #x00))

(check-sat)
