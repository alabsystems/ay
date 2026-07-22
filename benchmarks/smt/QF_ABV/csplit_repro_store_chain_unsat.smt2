; csplit-like benchmark: store chain with conflicting read constraints.
; Pattern: mem_after = store(store(mem, i, v1), j, v2)
; Then assert select(mem_after, i) != v1 when i != j
; This is UNSAT because store at j doesn't affect index i.
(set-logic QF_ABV)

; Initial memory
(declare-fun mem () (Array (_ BitVec 32) (_ BitVec 8)))

; Many trivial reads from base memory (padding to test threshold gates)
(declare-fun r0 () (_ BitVec 8))
(declare-fun r1 () (_ BitVec 8))
(declare-fun r2 () (_ BitVec 8))
(declare-fun r3 () (_ BitVec 8))
(declare-fun r4 () (_ BitVec 8))
(declare-fun r5 () (_ BitVec 8))
(declare-fun r6 () (_ BitVec 8))
(declare-fun r7 () (_ BitVec 8))
(declare-fun r8 () (_ BitVec 8))
(declare-fun r9 () (_ BitVec 8))
(assert (= r0 (select mem #x00000000)))
(assert (= r1 (select mem #x00000001)))
(assert (= r2 (select mem #x00000002)))
(assert (= r3 (select mem #x00000003)))
(assert (= r4 (select mem #x00000004)))
(assert (= r5 (select mem #x00000005)))
(assert (= r6 (select mem #x00000006)))
(assert (= r7 (select mem #x00000007)))
(assert (= r8 (select mem #x00000008)))
(assert (= r9 (select mem #x00000009)))

; Store chain: write #xAA at index #x00000010, then #xBB at index #x00000020
(declare-fun mem2 () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (= mem2 (store (store mem #x00000010 #xAA) #x00000020 #xBB)))

; Read from the store chain at the first stored index
; select(mem2, #x00000010) should be #xAA (ROW: different from #x00000020, pass through to inner store which has matching index)
; Assert it's NOT #xAA => should be UNSAT
(assert (not (= (select mem2 #x00000010) #xAA)))

(check-sat)
