; Authored producer-shaped control, NOT a captured MODEL_CHECKER_CONSUMER compiler export.
; An existing parent array's default cannot be overwritten to satisfy a read.
(set-logic ALL)
(set-info :status unsat)
(declare-datatype Vec_bv40
  ((Vec_bv40_mk (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
    (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 40))))))
(declare-datatype PbTerm
  ((PbTerm_mk (fld_coeff (_ BitVec 128)) (fld_lits Vec_bv40))))
(declare-const a (Array (_ BitVec 64) PbTerm))
(assert (= (fld_lits (select a (_ bv9 64)))
  (Vec_bv40_mk (_ bv0 64) (_ bv2 64) (_ bv2 64)
    (store ((as const (Array (_ BitVec 64) (_ BitVec 40))) (_ bv7 40))
           (_ bv64 64) (_ bv9 40)))))
(assert (= (select (fld_data (fld_lits (select a (_ bv9 64)))) (_ bv65 64))
           (_ bv8 40)))
(check-sat)
(exit)
