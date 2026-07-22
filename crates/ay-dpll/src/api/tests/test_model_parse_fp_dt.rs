// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for FP and Datatype model value parsing (#5843).

use crate::api::model_parse::{parse_dt_value, parse_fp_value, parse_model_str, parse_value_sexp};
use crate::api::types::{FpSpecialKind, ModelValue};
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{DatatypeSort, Sort};
use num_bigint::BigInt;

#[test]
fn test_parse_fp_positive_zero() {
    let sexp = ay_frontend::sexp::parse_sexps("(_ +zero 8 24)").unwrap();
    let result = parse_fp_value(&sexp[0], 8, 24);
    assert_eq!(
        result,
        ModelValue::FloatingPointSpecial {
            kind: FpSpecialKind::PosZero,
            eb: 8,
            sb: 24,
        }
    );
}

#[test]
fn test_parse_fp_negative_infinity() {
    let sexp = ay_frontend::sexp::parse_sexps("(_ -oo 8 24)").unwrap();
    let result = parse_fp_value(&sexp[0], 8, 24);
    assert_eq!(
        result,
        ModelValue::FloatingPointSpecial {
            kind: FpSpecialKind::NegInf,
            eb: 8,
            sb: 24,
        }
    );
}

#[test]
fn test_parse_fp_nan() {
    let sexp = ay_frontend::sexp::parse_sexps("(_ NaN 8 24)").unwrap();
    let result = parse_fp_value(&sexp[0], 8, 24);
    assert_eq!(
        result,
        ModelValue::FloatingPointSpecial {
            kind: FpSpecialKind::NaN,
            eb: 8,
            sb: 24,
        }
    );
}

#[test]
fn test_parse_fp_normal_value() {
    // (fp #b0 #b01111111 #b00000000000000000000000)  = +1.0 in Float32
    let sexp =
        ay_frontend::sexp::parse_sexps("(fp #b0 #b01111111 #b00000000000000000000000)").unwrap();
    let result = parse_fp_value(&sexp[0], 8, 24);
    assert_eq!(
        result,
        ModelValue::FloatingPoint {
            sign: false,
            exponent: 0b01111111,
            significand: 0,
            eb: 8,
            sb: 24,
        }
    );
}

#[test]
fn test_parse_fp_negative_value() {
    // (fp #b1 #b10000000 #b10000000000000000000000)  = -3.0 in Float32
    let sexp =
        ay_frontend::sexp::parse_sexps("(fp #b1 #b10000000 #b10000000000000000000000)").unwrap();
    let result = parse_fp_value(&sexp[0], 8, 24);
    assert_eq!(
        result,
        ModelValue::FloatingPoint {
            sign: true,
            exponent: 0b10000000,
            significand: 0b10000000000000000000000,
            eb: 8,
            sb: 24,
        }
    );
}

#[test]
fn test_parse_dt_nullary_constructor() {
    let sexp = ay_frontend::sexp::parse_sexps("Red").unwrap();
    let sort = Sort::Datatype(DatatypeSort::new("Color", vec![]));
    let result = parse_dt_value(&sexp[0], &sort);
    assert_eq!(
        result,
        ModelValue::Datatype {
            constructor: "Red".to_string(),
            args: Vec::new(),
        }
    );
}

#[test]
fn test_parse_dt_constructor_with_args() {
    let sexp = ay_frontend::sexp::parse_sexps("(Pair 42 true)").unwrap();
    let sort = Sort::Datatype(DatatypeSort::new("IntBoolPair", vec![]));
    let result = parse_dt_value(&sexp[0], &sort);
    assert_eq!(
        result,
        ModelValue::Datatype {
            constructor: "Pair".to_string(),
            args: vec![ModelValue::Int(BigInt::from(42)), ModelValue::Bool(true)],
        }
    );
}

#[test]
fn test_parse_value_sexp_fp_sort() {
    let sexp = ay_frontend::sexp::parse_sexps("(_ +zero 8 24)").unwrap();
    let sort = Sort::FloatingPoint(8, 24);
    let result = parse_value_sexp(&sexp[0], &sort);
    assert_eq!(
        result,
        ModelValue::FloatingPointSpecial {
            kind: FpSpecialKind::PosZero,
            eb: 8,
            sb: 24,
        }
    );
}

#[test]
fn test_parse_value_sexp_dt_sort() {
    let sexp = ay_frontend::sexp::parse_sexps("Nil").unwrap();
    let sort = Sort::Datatype(DatatypeSort::new("List", vec![]));
    let result = parse_value_sexp(&sexp[0], &sort);
    assert_eq!(
        result,
        ModelValue::Datatype {
            constructor: "Nil".to_string(),
            args: Vec::new(),
        }
    );
}

#[test]
fn test_fp_display_roundtrip() {
    let val = ModelValue::FloatingPoint {
        sign: false,
        exponent: 0b01111111,
        significand: 0,
        eb: 8,
        sb: 24,
    };
    let display = format!("{val}");
    assert!(display.starts_with("(fp #b0 #b"));
}

#[test]
fn test_fp_special_display() {
    let val = ModelValue::FloatingPointSpecial {
        kind: FpSpecialKind::NaN,
        eb: 8,
        sb: 24,
    };
    assert_eq!(format!("{val}"), "(_ NaN 8 24)");
}

#[test]
fn test_dt_display_nullary() {
    let val = ModelValue::Datatype {
        constructor: "Nil".to_string(),
        args: Vec::new(),
    };
    assert_eq!(format!("{val}"), "Nil");
}

#[test]
fn test_dt_display_with_args() {
    let val = ModelValue::Datatype {
        constructor: "Cons".to_string(),
        args: vec![
            ModelValue::Int(BigInt::from(1)),
            ModelValue::Uninterpreted("Nil".to_string()),
        ],
    };
    assert_eq!(format!("{val}"), "(Cons 1 Nil)");
}

#[test]
fn test_parse_dt_constructor_with_bv_arg_infers_width() {
    // BV literal #xFF inside a datatype constructor should infer width=8
    let sexp = ay_frontend::sexp::parse_sexps("(Wrap #xFF)").unwrap();
    let sort = Sort::Datatype(DatatypeSort::new("BvBox", vec![]));
    let result = parse_dt_value(&sexp[0], &sort);
    assert_eq!(
        result,
        ModelValue::Datatype {
            constructor: "Wrap".to_string(),
            args: vec![ModelValue::BitVec {
                value: BigInt::from(255),
                width: 8,
            }],
        }
    );
}

#[test]
fn test_parse_dt_constructor_with_binary_bv_arg() {
    // BV literal #b1010 inside a datatype constructor should infer width=4
    let sexp = ay_frontend::sexp::parse_sexps("(Tag #b1010)").unwrap();
    let sort = Sort::Datatype(DatatypeSort::new("Tagged", vec![]));
    let result = parse_dt_value(&sexp[0], &sort);
    assert_eq!(
        result,
        ModelValue::Datatype {
            constructor: "Tag".to_string(),
            args: vec![ModelValue::BitVec {
                value: BigInt::from(0b1010),
                width: 4,
            }],
        }
    );
}

// --- Array parsing tests (#5847) ---

#[test]
fn test_parse_array_const_int() {
    use crate::api::model_parse::parse_array_value;
    // ((as const (Array Int Int)) 0)
    let sexp = ay_frontend::sexp::parse_sexps("((as const (Array Int Int)) 0)").unwrap();
    let result = parse_array_value(&sexp[0], &Sort::Int);
    assert_eq!(
        result,
        ModelValue::Array {
            default: Box::new(ModelValue::Int(BigInt::from(0))),
            stores: vec![],
        }
    );
}

#[test]
fn test_parse_array_store_chain() {
    use crate::api::model_parse::parse_array_value;
    // (store ((as const (Array Int Int)) 0) 1 42)
    let sexp =
        ay_frontend::sexp::parse_sexps("(store ((as const (Array Int Int)) 0) 1 42)").unwrap();
    let result = parse_array_value(&sexp[0], &Sort::Int);
    assert_eq!(
        result,
        ModelValue::Array {
            default: Box::new(ModelValue::Int(BigInt::from(0))),
            stores: vec![(
                ModelValue::Int(BigInt::from(1)),
                ModelValue::Int(BigInt::from(42))
            )],
        }
    );
}

#[test]
fn test_parse_array_nested_stores() {
    use crate::api::model_parse::parse_array_value;
    // (store (store ((as const (Array Int Int)) 0) 1 10) 2 20)
    let sexp =
        ay_frontend::sexp::parse_sexps("(store (store ((as const (Array Int Int)) 0) 1 10) 2 20)")
            .unwrap();
    let result = parse_array_value(&sexp[0], &Sort::Int);
    assert_eq!(
        result,
        ModelValue::Array {
            default: Box::new(ModelValue::Int(BigInt::from(0))),
            stores: vec![
                (
                    ModelValue::Int(BigInt::from(1)),
                    ModelValue::Int(BigInt::from(10))
                ),
                (
                    ModelValue::Int(BigInt::from(2)),
                    ModelValue::Int(BigInt::from(20))
                ),
            ],
        }
    );
}

#[test]
fn test_parse_array_bool_element() {
    use crate::api::model_parse::parse_array_value;
    // (store ((as const (Array Int Bool)) false) 5 true)
    let sexp = ay_frontend::sexp::parse_sexps("(store ((as const (Array Int Bool)) false) 5 true)")
        .unwrap();
    let result = parse_array_value(&sexp[0], &Sort::Bool);
    assert_eq!(
        result,
        ModelValue::Array {
            default: Box::new(ModelValue::Bool(false)),
            stores: vec![(ModelValue::Int(BigInt::from(5)), ModelValue::Bool(true))],
        }
    );
}

#[test]
fn test_parse_array_display_roundtrip() {
    let val = ModelValue::Array {
        default: Box::new(ModelValue::Int(BigInt::from(0))),
        stores: vec![
            (
                ModelValue::Int(BigInt::from(1)),
                ModelValue::Int(BigInt::from(42)),
            ),
            (
                ModelValue::Int(BigInt::from(2)),
                ModelValue::Int(BigInt::from(99)),
            ),
        ],
    };
    let display = format!("{val}");
    assert_eq!(display, "(store (store 0 1 42) 2 99)");
}

#[test]
fn test_parse_array_via_parse_value_sexp() {
    use ay_core::ArraySort;
    // End-to-end: parse_value_sexp dispatches to parse_array_value for Array sort
    let sexp = ay_frontend::sexp::parse_sexps("((as const (Array Int Int)) 7)").unwrap();
    let sort = Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)));
    let result = parse_value_sexp(&sexp[0], &sort);
    assert_eq!(
        result,
        ModelValue::Array {
            default: Box::new(ModelValue::Int(BigInt::from(7))),
            stores: vec![],
        }
    );
}

#[test]
fn test_parse_array_fallback_unparseable() {
    use crate::api::model_parse::parse_array_value;
    // Unparseable array expression falls back to ArraySmtlib
    let sexp = ay_frontend::sexp::parse_sexps("(lambda ((x Int)) x)").unwrap();
    let result = parse_array_value(&sexp[0], &Sort::Int);
    assert!(matches!(result, ModelValue::ArraySmtlib(_)));
}

#[test]
fn test_model_iter_all_names_and_iter_include_structured_array() {
    let model_str = r#"(model
  (define-fun b () Bool true)
  (define-fun i () Int 3)
  (define-fun a () (Array Int Int)
    (store ((as const (Array Int Int)) 0) 2 9))
)"#;
    let model = parse_model_str(model_str);

    let entries: HashMap<_, _> = model
        .iter_all()
        .map(|(name, value)| (name.to_string(), value))
        .collect();
    assert_eq!(entries.get("b"), Some(&ModelValue::Bool(true)));
    assert_eq!(entries.get("i"), Some(&ModelValue::Int(BigInt::from(3))));
    assert_eq!(
        entries.get("a"),
        Some(&ModelValue::Array {
            default: Box::new(ModelValue::Int(BigInt::from(0))),
            stores: vec![(
                ModelValue::Int(BigInt::from(2)),
                ModelValue::Int(BigInt::from(9))
            )],
        })
    );

    let (default, stores) = model.array_val("a").unwrap().try_array().unwrap();
    assert_eq!(default, &ModelValue::Int(BigInt::from(0)));
    assert_eq!(
        stores,
        &[(
            ModelValue::Int(BigInt::from(2)),
            ModelValue::Int(BigInt::from(9))
        )]
    );

    let mut names: Vec<_> = model.names().collect();
    names.sort_unstable();
    assert_eq!(names, vec!["a", "b", "i"]);

    let mut iter_names: Vec<_> = model.iter().map(|(name, _)| name).collect();
    iter_names.sort_unstable();
    assert_eq!(iter_names, names);
}

// --- Improved DT arg parsing tests (#5847) ---

#[test]
fn test_parse_dt_nested_constructor() {
    // (Cons 1 (Cons 2 Nil))
    let sexp = ay_frontend::sexp::parse_sexps("(Cons 1 (Cons 2 Nil))").unwrap();
    let sort = Sort::Datatype(DatatypeSort::new("IntList", vec![]));
    let result = parse_dt_value(&sexp[0], &sort);
    assert_eq!(
        result,
        ModelValue::Datatype {
            constructor: "Cons".to_string(),
            args: vec![
                ModelValue::Int(BigInt::from(1)),
                ModelValue::Datatype {
                    constructor: "Cons".to_string(),
                    args: vec![
                        ModelValue::Int(BigInt::from(2)),
                        ModelValue::Uninterpreted("Nil".to_string()),
                    ],
                },
            ],
        }
    );
}

#[test]
fn test_parse_dt_with_negative_int_arg() {
    // (Wrap (- 5))
    let sexp = ay_frontend::sexp::parse_sexps("(Wrap (- 5))").unwrap();
    let sort = Sort::Datatype(DatatypeSort::new("IntBox", vec![]));
    let result = parse_dt_value(&sexp[0], &sort);
    assert_eq!(
        result,
        ModelValue::Datatype {
            constructor: "Wrap".to_string(),
            args: vec![ModelValue::Int(BigInt::from(-5))],
        }
    );
}

#[test]
fn test_parse_dt_with_real_arg() {
    // (Pair (/ 1 3) true)
    let sexp = ay_frontend::sexp::parse_sexps("(Pair (/ 1 3) true)").unwrap();
    let sort = Sort::Datatype(DatatypeSort::new("RealBoolPair", vec![]));
    let result = parse_dt_value(&sexp[0], &sort);
    use num_rational::BigRational;
    assert_eq!(
        result,
        ModelValue::Datatype {
            constructor: "Pair".to_string(),
            args: vec![
                ModelValue::Real(BigRational::new(BigInt::from(1), BigInt::from(3))),
                ModelValue::Bool(true),
            ],
        }
    );
}

#[test]
fn test_parse_dt_with_string_arg() {
    // (Label "hello")
    let sexp = ay_frontend::sexp::parse_sexps(r#"(Label "hello")"#).unwrap();
    let sort = Sort::Datatype(DatatypeSort::new("StringBox", vec![]));
    let result = parse_dt_value(&sexp[0], &sort);
    assert_eq!(
        result,
        ModelValue::Datatype {
            constructor: "Label".to_string(),
            args: vec![ModelValue::String("hello".to_string())],
        }
    );
}

// --- Model struct String/FP/Seq field tests (#6008) ---

#[test]
fn test_parse_model_str_string_value() {
    use crate::api::model_parse::parse_model_str;
    let model_str = r#"(model
  (define-fun x () String "hello world")
)"#;
    let model = parse_model_str(model_str);
    assert_eq!(model.get_string("x"), Some("hello world"));
    assert_eq!(model.len(), 1);
}

#[test]
fn test_parse_model_str_ascribed_uninterpreted_elements() {
    let model_str = r#"
      (model
        (define-fun u () S (as @S!0 S))
        (define-fun q () |foo::S| (as |@foo::S!1| |foo::S|)))
    "#;
    let model = parse_model_str(model_str);

    assert_eq!(model.uninterpreted_val("u"), Some("@S!0"));
    assert_eq!(model.uninterpreted_val("q"), Some("@foo::S!1"));
    assert!(model.datatype_val("u").is_none());
    assert!(model.datatype_val("q").is_none());
}

#[test]
fn test_parse_model_str_fp_value() {
    use crate::api::model_parse::parse_model_str;
    // Float32: (fp #b0 #b01111111 #b00000000000000000000000) = +1.0
    let model_str = r#"(model
  (define-fun y () (_ FloatingPoint 8 24) (fp #b0 #b01111111 #b00000000000000000000000))
)"#;
    let model = parse_model_str(model_str);
    let fp = model.fp_val("y").expect("FP value should be parsed");
    assert_eq!(
        *fp,
        ModelValue::FloatingPoint {
            sign: false,
            exponent: 0b01111111,
            significand: 0,
            eb: 8,
            sb: 24,
        }
    );
    assert_eq!(model.len(), 1);
}

#[test]
fn test_parse_model_str_fp_special_value() {
    use crate::api::model_parse::parse_model_str;
    let model_str = r#"(model
  (define-fun z () (_ FloatingPoint 8 24) (_ NaN 8 24))
)"#;
    let model = parse_model_str(model_str);
    let fp = model
        .fp_val("z")
        .expect("FP special value should be parsed");
    assert_eq!(
        *fp,
        ModelValue::FloatingPointSpecial {
            kind: FpSpecialKind::NaN,
            eb: 8,
            sb: 24,
        }
    );
}

#[test]
fn test_parse_model_str_seq_empty() {
    use crate::api::model_parse::parse_model_str;
    let model_str = r#"(model
  (define-fun s () (Seq Int) (as seq.empty (Seq Int)))
)"#;
    let model = parse_model_str(model_str);
    let seq = model.seq_val("s").expect("Seq value should be parsed");
    assert_eq!(*seq, ModelValue::Seq(vec![]));
}

#[test]
fn test_parse_model_str_seq_unit() {
    use crate::api::model_parse::parse_model_str;
    let model_str = r#"(model
  (define-fun s () (Seq Int) (seq.unit 42))
)"#;
    let model = parse_model_str(model_str);
    let seq = model.seq_val("s").expect("Seq value should be parsed");
    assert_eq!(
        *seq,
        ModelValue::Seq(vec![ModelValue::Int(BigInt::from(42))])
    );
}

#[test]
fn test_parse_model_str_mixed_sorts() {
    use crate::api::model_parse::parse_model_str;
    let model_str = r#"(model
  (define-fun a () Int 42)
  (define-fun b () String "test")
  (define-fun c () Bool true)
  (define-fun d () (_ FloatingPoint 8 24) (_ +zero 8 24))
)"#;
    let model = parse_model_str(model_str);
    assert_eq!(model.int_val_i64("a"), Some(42));
    assert_eq!(model.get_string("b"), Some("test"));
    assert_eq!(model.bool_val("c"), Some(true));
    assert!(model.fp_val("d").is_some());
    assert_eq!(model.len(), 4);
    assert!(!model.is_empty());
}

#[test]
fn test_model_iter_strings() {
    use crate::api::model_parse::parse_model_str;
    let model_str = r#"(model
  (define-fun s1 () String "alpha")
  (define-fun s2 () String "beta")
)"#;
    let model = parse_model_str(model_str);
    let strings: Vec<_> = model.iter_strings().collect();
    assert_eq!(strings.len(), 2);
}

#[test]
fn test_model_iter_fps() {
    use crate::api::model_parse::parse_model_str;
    let model_str = r#"(model
  (define-fun f () (_ FloatingPoint 8 24) (_ +zero 8 24))
)"#;
    let model = parse_model_str(model_str);
    let fps: Vec<_> = model.iter_fps().collect();
    assert_eq!(fps.len(), 1);
}

#[test]
fn test_model_iter_seqs() {
    use crate::api::model_parse::parse_model_str;
    let model_str = r#"(model
  (define-fun s () (Seq Int) (seq.unit 1))
)"#;
    let model = parse_model_str(model_str);
    let seqs: Vec<_> = model.iter_seqs().collect();
    assert_eq!(seqs.len(), 1);
}
