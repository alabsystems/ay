; Authored producer-shaped control, NOT a captured MODEL_CHECKER_CONSUMER compiler export.
; model-checker-consumer 22278991: PbTerm{coeff:i128,lits:Vec<PbLit>}, Vec_bv40 data.
; Distinct source expressions identify one outer cell and one inner key.
(set-logic ALL)
(set-info :status sat)
(declare-datatype Vec_bv40
  ((Vec_bv40_mk (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
    (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 40))))))
(declare-datatype PbTerm
  ((PbTerm_mk (fld_coeff (_ BitVec 128)) (fld_lits Vec_bv40))))
(declare-const a (Array (_ BitVec 64) PbTerm))
(declare-const b (Array (_ BitVec 64) PbTerm))
(assert (= a b))
(assert (= (fld_coeff (select a (_ bv9 64))) (_ bv3 128)))
(assert (= (select (fld_data (fld_lits (select a (_ bv9 64)))) (_ bv64 64))
           (_ bv7 40)))
(assert (= (select (fld_data (fld_lits (select b (bvadd (_ bv8 64) (_ bv1 64)))))
                   (bvadd (_ bv63 64) (_ bv1 64))) (_ bv7 40)))
(assert (= (select (fld_data (fld_lits (select b (_ bv9 64)))) (_ bv65 64))
           (_ bv8 40)))
(check-sat)
(exit)
