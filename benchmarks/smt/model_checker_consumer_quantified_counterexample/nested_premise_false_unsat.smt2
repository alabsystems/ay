; Copyright 2026 Andrew Yates
; SPDX-License-Identifier: Apache-2.0
;
; Authored standalone original-path obligation corresponding to the nested
; counterexample test fixture, NOT captured output of AY's renderer and NOT
; a retained MODEL_CHECKER_CONSUMER compiler export. No Horn reachability approximation:
; fact/query locals are fresh and linked by the exact predicate argument.
; Expected: unsat. The original grouped premise is false at (33,64), although every low-32 hint holds.
; Outer length 34; only row33 is nonempty (length65). Arrays retain full
; constant/default/store semantics and the entire joint forall is asserted.
(set-logic ALL)

(declare-datatype Inner ((mkInner
  (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
  (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 8))))))
(declare-datatype Outer ((mkOuter
  (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
  (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) Inner)))))

(declare-const fact_outer Outer)
(declare-const query_outer Outer)
(declare-const query_row (_ BitVec 64))
(declare-const query_col (_ BitVec 64))

; Original fact constraint: a fully specified nested Vec value.
(assert
  (= fact_outer
     (let ((cells ((as const (Array (_ BitVec 64) (_ BitVec 8))) (_ bv7 8))))
       (let ((empty (mkInner (_ bv0 64) (_ bv0 64) (_ bv0 64) cells))
             (occupied (mkInner (_ bv0 64) (_ bv65 64) (_ bv65 64)
                                (store cells (_ bv64 64) (_ bv9 8)))))
         (mkOuter (_ bv0 64) (_ bv34 64) (_ bv34 64)
           (store ((as const (Array (_ BitVec 64) Inner)) empty)
                  (_ bv33 64) occupied))))))

; Original fact premise, neither dropped nor replaced by finitely many hints.
(assert
  (forall ((r (_ BitVec 64)) (c (_ BitVec 64)))
    (=> (and (bvult r (fld_len fact_outer))
             (bvult c (fld_len (select (fld_data fact_outer) r))))
        (= (select (fld_data (select (fld_data fact_outer) r)) c)
           (_ bv7 8)))))

; Exact P(fact_outer) -> P(query_outer) argument link between clause scopes.
(assert (= query_outer fact_outer))

; Original query constraint.
(assert (= query_row (_ bv33 64)))
(assert (= query_col (_ bv64 64)))
(assert (bvult query_row (fld_len query_outer)))
(assert (bvult query_col (fld_len (select (fld_data query_outer) query_row))))
(assert (distinct
  (select (fld_data (select (fld_data query_outer) query_row)) query_col)
  (_ bv8 8)))
(check-sat)
