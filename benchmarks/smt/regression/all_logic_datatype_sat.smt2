; Author: Andrew Yates <andrewyates.name@gmail.com>
; Repro for Issue #901: AY should accept (set-logic ALL) when datatypes are present.

(set-option :produce-models true)
(set-logic ALL)
(declare-datatype Tuple_bv32_bool ((mk (fld_0 (_ BitVec 32)) (fld_1 Bool))))
(declare-const x Tuple_bv32_bool)
(assert (= x (mk #x00000005 true)))
(check-sat)
