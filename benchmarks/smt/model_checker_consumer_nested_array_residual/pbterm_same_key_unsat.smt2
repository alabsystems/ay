; Authored producer-shaped control, NOT a captured MODEL_CHECKER_CONSUMER compiler export.
; Same outer alias cell and semantic inner key require conflicting values.
(set-logic ALL)
(set-info :status unsat)
(declare-datatype Vec_bv40
  ((Vec_bv40_mk (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
    (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 40))))))
(declare-datatype PbTerm
  ((PbTerm_mk (fld_coeff (_ BitVec 128)) (fld_lits Vec_bv40))))
(declare-const a (Array (_ BitVec 64) PbTerm))
(declare-const b (Array (_ BitVec 64) PbTerm))
(assert (= a b))
(assert (= (select (fld_data (fld_lits (select a (_ bv9 64)))) (_ bv64 64))
           (_ bv7 40)))
(assert (= (select (fld_data (fld_lits (select b (bvadd (_ bv8 64) (_ bv1 64)))))
                   (bvadd (_ bv63 64) (_ bv1 64))) (_ bv8 40)))
(check-sat)
(exit)
