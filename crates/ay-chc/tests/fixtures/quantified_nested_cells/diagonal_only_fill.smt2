; Copyright 2026 Andrew Yates
; SPDX-License-Identifier: Apache-2.0
; AUTHORED METAMORPHIC CONTROL, NOT A COMPILER-EXPORTED HARNESS.
; Record/array vocabulary follows MODEL_CHECKER_CONSUMER 22278991c4d8e73189117c1f601ca1f4a89d6054:
; types.rs::flatten_dt_array_element, vec_fields, collection selector reads.
; Deliberately weaker than full two-index fill: only i=j cells are constrained.
; A ghost encoding that accidentally ties the outer and inner indices together
; cannot distinguish this from full fill. The bad read is at (33,64).
; Expected reference verdict: sat. No claim about AY runtime behavior.
(set-logic ALL)
(declare-datatypes ((Inner 0) (Outer 0))
  (((mk_inner (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
                   (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 8)))))
   ((mk_outer (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
                   (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) Inner))))))
(declare-const result Outer)
; Supply a compact finite-store countermodel: every row is constantly 7 except
; row 33, whose column 64 is 9. This retains all diagonal values as 7 and avoids
; asking the reference solver to discover a quantified array model unaided.
(declare-const ordinary Inner)
(declare-const exceptional Inner)
(assert (= ordinary (mk_inner (_ bv101 64) (_ bv68 64) (_ bv68 64)
  ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07))))
(assert (= exceptional (mk_inner (_ bv102 64) (_ bv68 64) (_ bv68 64)
  (store (fld_data ordinary) (_ bv64 64) #x09))))
(assert (= result (mk_outer (_ bv202 64) (_ bv65 64) (_ bv65 64)
  (store ((as const (Array (_ BitVec 64) Inner)) ordinary) (_ bv33 64) exceptional))))
(assert (= (fld_len result) (_ bv65 64)))
(assert (bvuge (fld_cap result) (fld_len result)))
(assert (forall ((i (_ BitVec 64)))
  (=> (bvult i (fld_len result))
      (and (= (fld_len (select (fld_data result) i)) (_ bv68 64))
           (bvuge (fld_cap (select (fld_data result) i)) (_ bv68 64))))))
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)))
  (=> (and (bvuge i (_ bv2 64)) (bvult i (fld_len result))
           (bvuge j (_ bv2 64))
           (bvult j (fld_len (select (fld_data result) i))) (= i j))
      (= (select (fld_data (select (fld_data result) i)) j) #x07))))
(assert (not (= (select (fld_data (select (fld_data result) (_ bv33 64)))
                       (_ bv64 64)) #x07)))
(check-sat)
