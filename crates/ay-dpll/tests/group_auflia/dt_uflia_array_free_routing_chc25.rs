// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression for the array-free DT+LIA routing (#chc25-dt-uflia).
//!
//! A datatype (enum + list) + uninterpreted-function (catamorphism) + LIA
//! obligation with NO arrays must be discharged. Before the fix, the
//! `DtAuflia` dispatch unconditionally used the array-enabled combiner
//! (`solve_auf_lia`), which fails to share EUF-derived congruence equalities
//! into arithmetic for these enum/list obligations and stalls to `unknown`
//! (a 20s timeout on the real tip-adt-lia catamorphism obligations). The fix
//! routes array-free `DtAuflia`/`Ufdtlia`/`Aufdtlia` problems through the
//! UF+LIA combiner first (`solve_dt_uf_lia`), mirroring the existing
//! `LogicCategory::Auflia` fast path, with a fallback to the array path so the
//! routing is strictly additive. This is the exact reduced shape of the
//! `tip2015_sort_ISortSorts` size obligation that previously timed out.
//!
//! Kill switch: `--dpll-no-dt-uflia` restores the old array-only routing.

use ntest::timeout;

/// The reduced ISortSorts size obligation: v_0 = true, v_1 = nil, with the
/// catamorphism-size recurrences pinned to 1, and the negated goal that all
/// the size equalities hold. UNSAT (the goal is valid), but the array-enabled
/// combiner cannot close it. Must be `unsat` fast via the UF+LIA route.
#[test]
#[timeout(30_000)]
fn test_dt_uflia_array_free_catamorphism_obligation_is_unsat_chc25() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Bool_215 0) (list_149 0) )
          (((false_215)(true_215))
           ((nil_168)(cons_149 (head_298 Int) (tail_298 list_149))) ))
        (declare-fun cata_size@Bool_215 (Bool_215) Int)
        (declare-fun cata_size@list_149 (list_149) Int)
        (declare-const v_0 Bool_215)
        (declare-const v_1 list_149)
        (declare-const __cata0_size Int)
        (declare-const __cata1_size Int)
        (declare-const __cata2_size Int)
        (declare-const __cata3_size Int)
        (assert (and (= v_0 (as true_215 Bool_215)) (= v_1 (as nil_168 list_149))))
        (assert (= __cata0_size (cata_size@Bool_215 v_0)))
        (assert (>= (cata_size@Bool_215 v_0) 1))
        (assert (= __cata1_size (cata_size@list_149 v_1)))
        (assert (>= (cata_size@list_149 v_1) 1))
        (assert (= __cata2_size (cata_size@Bool_215 (as true_215 Bool_215))))
        (assert (>= (cata_size@Bool_215 (as true_215 Bool_215)) 1))
        (assert (= (cata_size@Bool_215 (as true_215 Bool_215)) 1))
        (assert (= __cata3_size (cata_size@list_149 (as nil_168 list_149))))
        (assert (>= (cata_size@list_149 (as nil_168 list_149)) 1))
        (assert (= (cata_size@list_149 (as nil_168 list_149)) 1))
        (assert (not (and (>= __cata0_size 1) (>= __cata1_size 1) (>= __cata2_size 1)
                          (= __cata2_size 1) (= __cata0_size __cata2_size)
                          (>= __cata3_size 1) (= __cata3_size 1) (= __cata1_size __cata3_size))))
        (check-sat)
    "#;
    let output = crate::common::solve_vec(smt);
    assert_eq!(
        output,
        vec!["unsat"],
        "array-free DT+UF+LIA catamorphism obligation must be discharged (routed through the \
         UF+LIA combiner); the array-enabled combiner stalls to unknown on this enum/list shape"
    );
}
