; Minimal reproduction for issue #70: Method delegation postconditions
;
; This encodes the verification condition for:
;   struct Outer { inner: Inner, field: Int }
;   fn outer(&mut self) {
;       self.inner.some_method();
;   }
;   #[ensures("self.field == old(self.field)")]
;
; The key insight: we need to prove that field is preserved
; when inner is modified by an uninterpreted method.

(set-logic QF_UF)

; Declare sorts for our structs
(declare-sort Inner 0)
(declare-sort Outer 0)

; Field accessor functions (like Z3's project functions)
; StructGet_ returns the field value from a struct
(declare-fun get_inner (Outer) Inner)
(declare-fun get_field (Outer) Int)

; Constructor function (creates Outer from components)
(declare-fun mk_outer (Inner Int) Outer)

; Constructor axioms (selector-constructor consistency)
(assert (forall ((i Inner) (f Int))
  (= (get_inner (mk_outer i f)) i)))
(assert (forall ((i Inner) (f Int))
  (= (get_field (mk_outer i f)) f)))

; Pre-state
(declare-const self_pre Outer)
(declare-const inner_pre Inner)
(declare-const field_pre Int)

; Bind pre-state fields
(assert (= inner_pre (get_inner self_pre)))
(assert (= field_pre (get_field self_pre)))

; Method call on inner (uninterpreted effect)
(declare-fun inner_method (Inner) Inner)
(declare-const inner_post Inner)
(assert (= inner_post (inner_method inner_pre)))

; Post-state: only inner changed, field preserved (frame condition)
(declare-const self_post Outer)
(assert (= self_post (mk_outer inner_post field_pre)))

; Postcondition: self.field == old(self.field)
; This should be SAT (the postcondition holds)
(declare-const field_post Int)
(assert (= field_post (get_field self_post)))

; Verify: field_post == field_pre
; If UNSAT, postcondition doesn't hold
; If SAT, postcondition may hold (need to negate to prove)
(assert (not (= field_post field_pre)))

(check-sat)  ; Expect UNSAT (postcondition is provable)
