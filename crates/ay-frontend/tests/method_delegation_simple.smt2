; Minimal reproduction for issue #70: Method delegation postconditions
; Quantifier-free version using arrays for heap encoding

(set-logic QF_AUFLIA)

; Use arrays to model struct fields
; Heap: object -> (field_id -> value)
(declare-fun Heap () (Array Int (Array Int Int)))

; Object and field identifiers
(declare-const self_ref Int)       ; Reference to self
(declare-const inner_field Int)    ; Field id for inner
(declare-const other_field Int)    ; Field id for other_field (should be preserved)

; Fields are distinct
(assert (distinct inner_field other_field))

; Pre-state values
(declare-const inner_pre Int)      ; Value of self.inner before call
(declare-const other_pre Int)      ; Value of self.other_field before call

; Bind pre-state
(assert (= inner_pre (select (select Heap self_ref) inner_field)))
(assert (= other_pre (select (select Heap self_ref) other_field)))

; Method call modifies inner (uninterpreted)
(declare-const inner_post Int)
; inner_post = some_method(inner_pre) - arbitrary new value

; Post-state heap: only inner changed
(declare-fun Heap_post () (Array Int (Array Int Int)))
(assert (= Heap_post
  (store Heap self_ref
    (store (select Heap self_ref) inner_field inner_post))))

; Frame condition: other_field is preserved
; This should follow from array theory: select(store(a,i,v),j) = select(a,j) when i != j

; Postcondition: self.other_field == old(self.other_field)
(declare-const other_post Int)
(assert (= other_post (select (select Heap_post self_ref) other_field)))

; Verify: other_post == other_pre
; If UNSAT, postcondition is violated (would be a bug)
; If SAT, need to negate to prove
(assert (not (= other_post other_pre)))

(check-sat)  ; Expect UNSAT (frame condition should hold)
