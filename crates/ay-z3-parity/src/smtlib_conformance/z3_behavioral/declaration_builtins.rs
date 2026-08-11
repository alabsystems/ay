// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Closed semantic witnesses for Z3 5.0.0 declaration-plugin builtins.
//!
//! Each predicate below is true under the public semantics and contains the
//! owner spelling it witnesses.  The behavioral validator wraps a predicate
//! `P` as `(assert (not P))`, so a correct implementation returns `unsat`.  Its
//! effect baseline omits the assertion and returns `sat`; merely accepting or
//! cataloging a spelling therefore cannot satisfy the owner row.

/// Public declaration-plugin builtins for which AY has a closed semantic
/// differential witness against the exact Z3 5.0.0 oracle.
///
/// Keep this table sorted by owner. Internal totalization helpers and legacy
/// implementation names (`bvudiv0`, `bvudiv_i`, `bit0`, `mkbv`, and peers) are
/// deliberately absent. The Z3 null-logic aliases and basic sorts/operators
/// that AY does not yet reproduce are likewise absent: recognizing a related
/// public operator is not evidence for those distinct source owners.
const DECLARATION_SEMANTIC_PREDICATES: [(&str, &str); 126] = [
    ("&&", "(&& true true)"),
    ("*", "(= (* 3 4) 12)"),
    ("+", "(= (+ 1 2) 3)"),
    ("+oo", "(fp.isInfinite (_ +oo 3 3))"),
    ("+zero", "(fp.isZero (_ +zero 3 3))"),
    ("-", "(= (- 3 2) 1)"),
    ("-oo", "(fp.isInfinite (_ -oo 3 3))"),
    ("-zero", "(fp.isZero (_ -zero 3 3))"),
    ("/", "(= (/ 6.0 3.0) 2.0)"),
    ("<", "(< 1 2)"),
    ("<=", "(<= 2 2)"),
    ("=", "(= #x2a #x2a)"),
    ("=>", "(=> true true)"),
    (">", "(> 2 1)"),
    (">=", "(>= 2 2)"),
    ("Bool", "(forall ((p Bool)) (= p p))"),
    ("Char", "(= (_ Char 65) (_ Char 65))"),
    ("Int", "(forall ((x Int)) (= x x))"),
    ("NaN", "(fp.isNaN (_ NaN 3 3))"),
    ("Proof", "(forall ((p Proof)) (= p p))"),
    ("Real", "(forall ((x Real)) (= x x))"),
    (
        "Set",
        "(= ((as const (Set Int)) false) ((as const (Set Int)) false))",
    ),
    ("abs", "(= (abs (- 3)) 3)"),
    ("and", "(and true (not false) (= #x01 #x01))"),
    ("at-least", "((_ at-least 2) true true false)"),
    ("at-most", "((_ at-most 1) true false false)"),
    ("bool", "(forall ((p bool)) (= p p))"),
    ("bv2int", "(= (bv2int #xff) 255)"),
    ("bv2nat", "(= (bv2nat #xff) 255)"),
    ("bvadd", "(= (bvadd #x01 #x02) #x03)"),
    ("bvand", "(= (bvand #x0f #xf0) #x00)"),
    ("bvashr", "(= (bvashr #x80 #x01) #xc0)"),
    ("bvcomp", "(= (bvcomp #x01 #x01) #b1)"),
    ("bvlshr", "(= (bvlshr #x80 #x01) #x40)"),
    ("bvmul", "(= (bvmul #x03 #x04) #x0c)"),
    ("bvnand", "(= (bvnand #x0f #xf0) #xff)"),
    ("bvneg", "(= (bvneg #x01) #xff)"),
    ("bvnego", "(bvnego #x80)"),
    ("bvnor", "(= (bvnor #x0f #xf0) #x00)"),
    ("bvnot", "(= (bvnot #x0f) #xf0)"),
    ("bvor", "(= (bvor #x0f #xf0) #xff)"),
    ("bvredand", "(= (bvredand #xff) #b1)"),
    ("bvredor", "(= (bvredor #x01) #b1)"),
    ("bvsaddo", "(bvsaddo #x7f #x01)"),
    ("bvsdiv", "(= (bvsdiv #xfe #x02) #xff)"),
    ("bvsdivo", "(bvsdivo #x80 #xff)"),
    ("bvsge", "(bvsge #xff #x80)"),
    ("bvsgt", "(bvsgt #xff #x80)"),
    ("bvshl", "(= (bvshl #x01 #x03) #x08)"),
    ("bvsle", "(bvsle #x80 #xff)"),
    ("bvslt", "(bvslt #x80 #xff)"),
    ("bvsmod", "(= (bvsmod #xfd #x02) #x01)"),
    ("bvsmulo", "(bvsmulo #x40 #x02)"),
    ("bvsrem", "(= (bvsrem #xfd #x02) #xff)"),
    ("bvssubo", "(bvssubo #x80 #x01)"),
    ("bvsub", "(= (bvsub #x03 #x01) #x02)"),
    ("bvuaddo", "(bvuaddo #xff #x01)"),
    ("bvudiv", "(= (bvudiv #x07 #x02) #x03)"),
    ("bvuge", "(bvuge #xff #x80)"),
    ("bvugt", "(bvugt #xff #x80)"),
    ("bvule", "(bvule #x80 #xff)"),
    ("bvult", "(bvult #x80 #xff)"),
    ("bvumulo", "(bvumulo #x10 #x10)"),
    ("bvurem", "(= (bvurem #x07 #x02) #x01)"),
    ("bvusubo", "(bvusubo #x00 #x01)"),
    ("bvxnor", "(= (bvxnor #x0f #xf0) #x00)"),
    ("bvxor", "(= (bvxor #x0f #xf0) #xff)"),
    ("char.<=", "(char.<= (_ Char 65) (_ Char 66))"),
    ("char.is_digit", "(char.is_digit (_ Char 53))"),
    ("char.to_bv", "(= (char.to_bv (_ Char 65)) (_ bv65 18))"),
    ("char.to_int", "(= (char.to_int (_ Char 65)) 65)"),
    (
        "complement",
        "(not (select (complement (store ((as const (Set Int)) false) 1 true)) 1))",
    ),
    ("concat", "(= (concat #xa #x5) #xa5)"),
    ("distinct", "(distinct #x00 #x01 #x02)"),
    ("div", "(= (div 7 3) 2)"),
    ("divisible", "((_ divisible 3) 6)"),
    ("equals", "(equals #x01 #x01)"),
    ("equiv", "(equiv true true)"),
    ("extract", "(= ((_ extract 7 4) #xab) #xa)"),
    ("false", "(= false (not true))"),
    ("fp.abs", "(= (fp.abs (_ -zero 3 3)) (_ +zero 3 3))"),
    (
        "fp.add",
        "(= (fp.add RNE (_ +zero 3 3) (_ +zero 3 3)) (_ +zero 3 3))",
    ),
    (
        "fp.div",
        "(fp.isNaN (fp.div RNE (_ +zero 3 3) (_ +zero 3 3)))",
    ),
    ("fp.eq", "(fp.eq (_ -zero 3 3) (_ +zero 3 3))"),
    (
        "fp.fma",
        "(= (fp.fma RNE (_ +zero 3 3) (_ +zero 3 3) (_ +zero 3 3)) (_ +zero 3 3))",
    ),
    ("fp.geq", "(fp.geq (_ +oo 3 3) (_ +zero 3 3))"),
    ("fp.gt", "(fp.gt (_ +oo 3 3) (_ +zero 3 3))"),
    ("fp.isInfinite", "(fp.isInfinite (_ +oo 3 3))"),
    ("fp.isNaN", "(fp.isNaN (_ NaN 3 3))"),
    ("fp.isNegative", "(fp.isNegative (_ -zero 3 3))"),
    ("fp.isNormal", "(not (fp.isNormal (_ +zero 3 3)))"),
    ("fp.isPositive", "(fp.isPositive (_ +zero 3 3))"),
    (
        "fp.isSubnormal",
        "(not (fp.isSubnormal (_ +zero 3 3)))",
    ),
    ("fp.isZero", "(fp.isZero (_ +zero 3 3))"),
    ("fp.leq", "(fp.leq (_ -zero 3 3) (_ +zero 3 3))"),
    ("if", "(= (if true #x01 #x02) #x01)"),
    (
        "if_then_else",
        "(= (if_then_else true #x01 #x02) #x01)",
    ),
    ("iff", "(iff true true)"),
    ("implies", "(implies true true)"),
    ("int2bv", "(= ((_ int2bv 8) 257) #x01)"),
    (
        "intersection",
        "(not (select (intersection (store ((as const (Set Int)) false) 1 true) (store ((as const (Set Int)) false) 2 true)) 1))",
    ),
    ("is_int", "(is_int 3.0)"),
    ("ite", "(= (ite false #x01 #x02) #x02)"),
    ("mod", "(= (mod 7 3) 1)"),
    ("not", "(not false)"),
    ("or", "(or false false true)"),
    ("pbeq", "((_ pbeq 0.5 0.25 0.25) true true)"),
    ("pbge", "((_ pbge -0.5 -0.25) true)"),
    ("pble", "((_ pble 0.5 0.25) true)"),
    ("rem", "(= (rem 7 3) 1)"),
    ("repeat", "(= ((_ repeat 2) #b10) #b1010)"),
    ("rotate_left", "(= ((_ rotate_left 1) #b1001) #b0011)"),
    ("rotate_right", "(= ((_ rotate_right 1) #b1001) #b1100)"),
    ("sbv_to_int", "(= (sbv_to_int #xff) (- 1))"),
    (
        "setminus",
        "(select (setminus (store (store ((as const (Set Int)) false) 1 true) 2 true) (store ((as const (Set Int)) false) 2 true)) 1)",
    ),
    ("sign_extend", "(= ((_ sign_extend 4) #x8) #xf8)"),
    (
        "subset",
        "(subset (store ((as const (Set Int)) false) 1 true) (store (store ((as const (Set Int)) false) 1 true) 2 true))",
    ),
    ("to_int", "(= (to_int 3.5) 3)"),
    ("to_real", "(= (to_real 3) 3.0)"),
    ("true", "(= true true)"),
    ("ubv_to_int", "(= (ubv_to_int #xff) 255)"),
    (
        "union",
        "(select (union (store ((as const (Set Int)) false) 1 true) (store ((as const (Set Int)) false) 2 true)) 2)",
    ),
    ("xor", "(xor true false)"),
    ("zero_extend", "(= ((_ zero_extend 4) #x8) #x08)"),
    ("||", r"(|\|\|| false true)"),
    ("~", "(= (~ 3) (- 3))"),
];

const ARITHMETIC_PLUGIN_OWNERS: [&str; 19] = [
    "*",
    "+",
    "-",
    "/",
    "<",
    "<=",
    ">",
    ">=",
    "Int",
    "Real",
    "abs",
    "div",
    "divisible",
    "is_int",
    "mod",
    "rem",
    "to_int",
    "to_real",
    "~",
];

const ARRAY_PLUGIN_OWNERS: [&str; 6] = [
    "Set",
    "complement",
    "intersection",
    "setminus",
    "subset",
    "union",
];

const PB_PLUGIN_OWNERS: [&str; 5] = ["at-least", "at-most", "pbeq", "pbge", "pble"];

const CHAR_PLUGIN_OWNERS: [&str; 5] = [
    "Char",
    "char.<=",
    "char.is_digit",
    "char.to_bv",
    "char.to_int",
];

const FPA_PLUGIN_OWNERS: [&str; 20] = [
    "+oo",
    "+zero",
    "-oo",
    "-zero",
    "NaN",
    "fp.abs",
    "fp.add",
    "fp.div",
    "fp.eq",
    "fp.fma",
    "fp.geq",
    "fp.gt",
    "fp.isInfinite",
    "fp.isNaN",
    "fp.isNegative",
    "fp.isNormal",
    "fp.isPositive",
    "fp.isSubnormal",
    "fp.isZero",
    "fp.leq",
];

const NO_LOGIC_ONLY_BASIC_OWNERS: [&str; 10] = [
    "&&",
    "Proof",
    "bool",
    "equals",
    "equiv",
    "if",
    "if_then_else",
    "iff",
    "implies",
    "||",
];

/// Return the closed true predicate for a declaration-builtin owner, or
/// `None` when this cohort makes no semantic claim for that spelling.
pub(super) fn semantic_predicate(owner: &str) -> Option<&'static str> {
    DECLARATION_SEMANTIC_PREDICATES
        .iter()
        .find_map(|&(name, predicate)| (name == owner).then_some(predicate))
}

pub(super) fn semantic_owner_names() -> impl Iterator<Item = &'static str> {
    DECLARATION_SEMANTIC_PREDICATES
        .iter()
        .map(|&(name, _)| name)
}

/// Whether the owner belongs to Z3 5.0.0's legacy no-logic basic signature.
/// Selecting a logic removes these spellings, except that `if` is also
/// registered unconditionally; its no-logic witness still exercises the exact
/// declaration owner without relying on the duplicate registration path.
pub(super) fn semantic_requires_no_logic(owner: &str) -> bool {
    NO_LOGIC_ONLY_BASIC_OWNERS.contains(&owner)
}

/// Commands required before the declaration registry is populated for an
/// otherwise-public owner. Z3 5.0.0 conditionally registers `divisible` behind
/// its SMT-LIB-compliance option. Enabling print-success as well makes the
/// resulting Z3 and AY transcripts byte-identical instead of hiding commands.
pub(super) fn semantic_prelude(owner: &str) -> &'static str {
    match owner {
        "divisible" => "(set-option :print-success true)\n(set-option :smtlib2_compliant true)\n",
        _ => "",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn declaration_semantic_table_is_closed_sorted_and_unique() {
        assert_eq!(DECLARATION_SEMANTIC_PREDICATES.len(), 126);
        assert!(DECLARATION_SEMANTIC_PREDICATES
            .windows(2)
            .all(|pair| pair[0].0 < pair[1].0));
        assert_eq!(semantic_owner_names().count(), 126);
    }

    #[test]
    fn every_predicate_is_balanced_and_mentions_its_owner() {
        for &(owner, predicate) in &DECLARATION_SEMANTIC_PREDICATES {
            assert!(predicate.starts_with('(') && predicate.ends_with(')'));
            assert_eq!(
                predicate.bytes().filter(|&byte| byte == b'(').count(),
                predicate.bytes().filter(|&byte| byte == b')').count(),
                "unbalanced predicate for {owner}"
            );
            assert!(
                predicate.contains(owner),
                "predicate does not exercise owner {owner}: {predicate}"
            );
            assert_eq!(semantic_predicate(owner), Some(predicate));
        }
    }

    #[test]
    fn basic_plugin_supported_and_unresolved_partitions_are_pinned() {
        let supported = [
            "&&",
            "=",
            "=>",
            "Bool",
            "Proof",
            "and",
            "bool",
            "distinct",
            "equals",
            "equiv",
            "false",
            "if",
            "if_then_else",
            "iff",
            "implies",
            "ite",
            "not",
            "or",
            "true",
            "xor",
            "||",
        ];

        assert!(supported.windows(2).all(|pair| pair[0] < pair[1]));
        for owner in supported {
            assert!(
                semantic_predicate(owner).is_some(),
                "missing basic-plugin witness for {owner}"
            );
        }
        for owner in NO_LOGIC_ONLY_BASIC_OWNERS {
            assert!(semantic_requires_no_logic(owner), "{owner}");
        }
        assert!(!semantic_requires_no_logic("and"));
    }

    #[test]
    fn arithmetic_plugin_cohort_has_closed_semantic_witnesses() {
        assert!(ARITHMETIC_PLUGIN_OWNERS
            .windows(2)
            .all(|pair| pair[0] < pair[1]));
        for owner in ARITHMETIC_PLUGIN_OWNERS {
            assert!(
                semantic_predicate(owner).is_some(),
                "missing arithmetic-plugin witness for {owner}"
            );
            assert!(!semantic_requires_no_logic(owner), "{owner}");
            assert_eq!(
                semantic_prelude(owner).is_empty(),
                owner != "divisible",
                "wrong arithmetic prelude for {owner}"
            );
        }
    }

    #[test]
    fn array_plugin_cohort_has_closed_semantic_witnesses() {
        assert!(ARRAY_PLUGIN_OWNERS.windows(2).all(|pair| pair[0] < pair[1]));
        for owner in ARRAY_PLUGIN_OWNERS {
            assert!(
                semantic_predicate(owner).is_some(),
                "missing array-plugin witness for {owner}"
            );
            assert!(!semantic_requires_no_logic(owner), "{owner}");
            assert!(semantic_prelude(owner).is_empty(), "{owner}");
        }
        for unresolved in [
            "->",
            "Array",
            "array-ext",
            "as-array",
            "choice",
            "const",
            "default",
            "map",
            "select",
            "store",
        ] {
            assert_eq!(semantic_predicate(unresolved), None, "claimed {unresolved}");
        }
    }

    #[test]
    fn pb_plugin_cohort_has_closed_semantic_witnesses() {
        assert!(PB_PLUGIN_OWNERS.windows(2).all(|pair| pair[0] < pair[1]));
        for owner in PB_PLUGIN_OWNERS {
            assert!(
                semantic_predicate(owner).is_some(),
                "missing pseudo-Boolean-plugin witness for {owner}"
            );
            assert!(!semantic_requires_no_logic(owner), "{owner}");
            assert!(semantic_prelude(owner).is_empty(), "{owner}");
        }
    }

    #[test]
    fn char_plugin_cohort_has_closed_semantic_witnesses() {
        assert!(CHAR_PLUGIN_OWNERS.windows(2).all(|pair| pair[0] < pair[1]));
        for owner in CHAR_PLUGIN_OWNERS {
            assert!(
                semantic_predicate(owner).is_some(),
                "missing character-plugin witness for {owner}"
            );
            assert!(!semantic_requires_no_logic(owner), "{owner}");
            assert!(semantic_prelude(owner).is_empty(), "{owner}");
        }
        for unresolved in ["Unicode", "char.from_bv"] {
            assert_eq!(semantic_predicate(unresolved), None, "claimed {unresolved}");
        }
    }

    #[test]
    fn floating_point_plugin_cohort_has_closed_semantic_witnesses() {
        assert!(FPA_PLUGIN_OWNERS.windows(2).all(|pair| pair[0] < pair[1]));
        for owner in FPA_PLUGIN_OWNERS {
            assert!(
                semantic_predicate(owner).is_some(),
                "missing floating-point-plugin witness for {owner}"
            );
            assert!(!semantic_requires_no_logic(owner), "{owner}");
            assert!(semantic_prelude(owner).is_empty(), "{owner}");
        }
        for internal in [
            "fp.max_i",
            "fp.min_i",
            "fp.to_ieee_bv_I",
            "fp.to_real_I",
            "fp.to_sbv_I",
            "fp.to_ubv_I",
        ] {
            assert_eq!(semantic_predicate(internal), None, "claimed {internal}");
        }
    }

    #[test]
    fn internal_and_legacy_bitvector_names_remain_unclaimed() {
        for owner in [
            "bit0",
            "bit1",
            "bit2bool",
            "bv",
            "bvsdiv0",
            "bvsdiv_i",
            "bvsmod0",
            "bvsmod_i",
            "bvsmul_noovfl",
            "bvsmul_noudfl",
            "bvsrem0",
            "bvsrem_i",
            "bvudiv0",
            "bvudiv_i",
            "bvumul_noovfl",
            "bvurem0",
            "bvurem_i",
            "ext_rotate_left",
            "ext_rotate_right",
            "int_to_bv",
            "mkbv",
        ] {
            assert_eq!(semantic_predicate(owner), None, "claimed {owner}");
        }
        assert_eq!(semantic_predicate("BVADD"), None);
        assert_eq!(semantic_predicate(""), None);
    }
}
