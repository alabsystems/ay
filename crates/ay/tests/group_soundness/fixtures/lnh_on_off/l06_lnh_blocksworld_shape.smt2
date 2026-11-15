; z3 5.1.0: sat
; LNH compound-domain wrong UNSAT in the blocksworld signature (enum blocks, Tower list, record of towers).
; Domain {(top (left s0)) .. (top (left s4))}; LNH adds blk = (top (left s0)); s0's left tower has top A.
; SAT: blk = B, (left s1) = (stack B empty).
(set-logic QF_DT)
(set-info :status sat)
(declare-datatypes ((Enum_A_B_C_D_E_F 0)) (((A) (B) (C) (D) (E) (F))))
(declare-datatypes ((Tower 0)) (((stack (top Enum_A_B_C_D_E_F) (rest Tower)) (empty))))
(declare-datatypes ((Record_left_center_right 0)) (((Record_left_center_right (left Tower) (center Tower) (right Tower)))))
(declare-fun blk () Enum_A_B_C_D_E_F)
(declare-fun s0 () Record_left_center_right)
(declare-fun s1 () Record_left_center_right)
(declare-fun s2 () Record_left_center_right)
(declare-fun s3 () Record_left_center_right)
(declare-fun s4 () Record_left_center_right)
(assert (or (= blk (top (left s0))) (= blk (top (left s1))) (= blk (top (left s2))) (= blk (top (left s3))) (= blk (top (left s4)))))
(assert (or (= s0 (Record_left_center_right (stack A empty) empty empty))
            (= s0 (Record_left_center_right (stack A (stack B empty)) empty empty))))
(assert (not (= blk A)))
(check-sat)
