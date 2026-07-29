// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the datatype-distinctness verified-firewall Lean emitter.

use super::*;
use ay_core::{Sort, Symbol, TermId, TermStore};

fn ctor(terms: &mut TermStore, name: &str, dt: &str) -> TermId {
    terms.mk_app(
        Symbol::named(name),
        Vec::<TermId>::new(),
        Sort::Uninterpreted(dt.to_string()),
    )
}

fn neq(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    let e = terms.mk_app(Symbol::named("="), vec![a, b], Sort::Bool);
    terms.mk_not(e)
}

fn color_decls() -> Vec<(String, Vec<String>)> {
    vec![(
        "Color".to_string(),
        vec!["red".to_string(), "green".to_string(), "blue".to_string()],
    )]
}

#[test]
fn emits_firewall_lean_for_binary_distinctness() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Uninterpreted("Color".to_string()));
    let red = ctor(&mut terms, "red", "Color");
    let green = ctor(&mut terms, "green", "Color");
    let l0 = neq(&mut terms, c, red);
    let l1 = neq(&mut terms, c, green);
    let decls = color_decls();

    let lean = emit_datatype_distinct_firewall_lean(&terms, &decls, &[l0, l1])
        .expect("binary distinctness lemma should emit");

    // Print so the generator's output can be lake-verified out of band.
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");

    for needle in [
        "import AySoundness.Firewall",
        "import AySoundness.Datatype",
        "namespace AySoundness.Emitted.s_436f6c6f72",
        "inductive T where",
        "  | s_726564",
        "  | s_677265656e",
        "  | s_626c7565",
        "decide (c = T.s_726564)",
        "decide (c = T.s_677265656e)",
        "firewall_combined_unsat",
        "theorem no_model",
    ] {
        assert!(lean.contains(needle), "emitted Lean missing: {needle}");
    }
}

#[test]
fn datatype_names_cannot_escape_generated_lean_comments_or_identifiers() {
    const PAYLOAD: &str = "victim-/\n#eval IO.println \"injected\"\n/-";
    const OTHER: &str = "other-/\r\n#check unsafeCast\n/-";
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Uninterpreted(PAYLOAD.to_string()));
    let first = ctor(&mut terms, PAYLOAD, PAYLOAD);
    let second = ctor(&mut terms, OTHER, PAYLOAD);
    let l0 = neq(&mut terms, c, first);
    let l1 = neq(&mut terms, c, second);
    let decls = vec![(
        PAYLOAD.to_string(),
        vec![PAYLOAD.to_string(), OTHER.to_string()],
    )];

    let lean = emit_datatype_distinct_firewall_lean(&terms, &decls, &[l0, l1])
        .expect("malicious but valid SMT names should emit through safe encoding");

    for forbidden in [PAYLOAD, OTHER, "#eval", "IO.println", "unsafeCast"] {
        assert!(
            !lean.contains(forbidden),
            "untrusted SMT text escaped into generated Lean source: {forbidden:?}"
        );
    }
    assert!(lean.contains("namespace AySoundness.Emitted.s_"));
    assert!(lean.contains("firewall_combined_unsat"));
}

#[test]
fn datatype_name_encoding_is_keyword_safe_and_injective() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Uninterpreted("namespace".to_string()));
    let keyword = ctor(&mut terms, "end", "namespace");
    let formerly_colliding = ctor(&mut terms, "c_2d", "namespace");
    let l0 = neq(&mut terms, c, keyword);
    let l1 = neq(&mut terms, c, formerly_colliding);
    let decls = vec![(
        "namespace".to_string(),
        vec!["end".to_string(), "c_2d".to_string(), "-".to_string()],
    )];

    let lean = emit_datatype_distinct_firewall_lean(&terms, &decls, &[l0, l1])
        .expect("keyword-like names should emit through safe encoding");
    for encoded in ["s_6e616d657370616365", "s_656e64", "s_635f3264", "s_2d"] {
        assert!(lean.contains(encoded), "missing encoded name {encoded}");
    }
    assert_ne!("s_635f3264", "s_2d");
    assert!(!lean.contains("  | end\n"));
    assert!(!lean.contains("namespace AySoundness.Emitted.namespace"));
}

#[test]
fn rejects_same_constructor() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Uninterpreted("Color".to_string()));
    let red = ctor(&mut terms, "red", "Color");
    let l0 = neq(&mut terms, c, red);
    let l1 = neq(&mut terms, c, red);
    let decls = color_decls();

    assert!(emit_datatype_distinct_firewall_lean(&terms, &decls, &[l0, l1]).is_none());
}

#[test]
fn rejects_non_constructor() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Uninterpreted("Color".to_string()));
    let red = ctor(&mut terms, "red", "Color");
    let other = terms.mk_var("other", Sort::Uninterpreted("Color".to_string()));
    let l0 = neq(&mut terms, c, red);
    let l1 = neq(&mut terms, c, other);
    let decls = color_decls();

    // `other` is a variable, not a registered constructor.
    assert!(emit_datatype_distinct_firewall_lean(&terms, &decls, &[l0, l1]).is_none());
}

#[test]
fn emits_seq_len_concat_from_parsed_assertions() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let seq_len = |s: &str| PTerm::App("seq.len".to_string(), vec![PTerm::Symbol(s.to_string())]);
    // (= (seq.len (seq.++ s t)) (+ (seq.len s) (seq.len t) 1)) → unsat (offset 1).
    let concat = PTerm::App(
        "seq.++".to_string(),
        vec![
            PTerm::Symbol("s".to_string()),
            PTerm::Symbol("t".to_string()),
        ],
    );
    let parsed = vec![PTerm::App(
        "=".to_string(),
        vec![
            PTerm::App("seq.len".to_string(), vec![concat]),
            PTerm::App(
                "+".to_string(),
                vec![
                    seq_len("s"),
                    seq_len("t"),
                    PTerm::Const(PConst::Numeral("1".to_string())),
                ],
            ),
        ],
    )];
    let lean = emit_seq_len_concat_firewall_lean_from_parsed(&parsed)
        .expect("parsed seq len-concat conflict should emit");
    assert!(lean.contains("import AySoundness.SeqThy"));
    assert!(lean.contains("SeqThy.len_concat"));
    assert!(lean.contains("+ 1)"));
    assert!(lean.contains("firewall_combined_unsat"));

    // A zero/negative offset is NOT a conflict (satisfiable) — must decline.
    let concat2 = PTerm::App(
        "seq.++".to_string(),
        vec![
            PTerm::Symbol("s".to_string()),
            PTerm::Symbol("t".to_string()),
        ],
    );
    let sat_parsed = vec![PTerm::App(
        "=".to_string(),
        vec![
            PTerm::App("seq.len".to_string(), vec![concat2]),
            PTerm::App("+".to_string(), vec![seq_len("s"), seq_len("t")]),
        ],
    )];
    assert!(emit_seq_len_concat_firewall_lean_from_parsed(&sat_parsed).is_none());
}

#[test]
fn emits_str_len_concat_from_parsed_assertions() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let str_len = |s: &str| PTerm::App("str.len".to_string(), vec![PTerm::Symbol(s.to_string())]);
    // (= (str.len (str.++ x y)) (+ (str.len x) (str.len y) 1)) → unsat (offset 1).
    let concat = PTerm::App(
        "str.++".to_string(),
        vec![
            PTerm::Symbol("x".to_string()),
            PTerm::Symbol("y".to_string()),
        ],
    );
    let parsed = vec![PTerm::App(
        "=".to_string(),
        vec![
            PTerm::App("str.len".to_string(), vec![concat]),
            PTerm::App(
                "+".to_string(),
                vec![
                    str_len("x"),
                    str_len("y"),
                    PTerm::Const(PConst::Numeral("1".to_string())),
                ],
            ),
        ],
    )];
    let lean = emit_str_len_concat_firewall_lean_from_parsed(&parsed)
        .expect("parsed str len-concat conflict should emit");
    assert!(lean.contains("import AySoundness.StringThy"));
    assert!(lean.contains("StringThy.len_cat"));
    assert!(lean.contains("+ 1)"));
    assert!(lean.contains("firewall_combined_unsat"));

    // A zero/negative offset is NOT a conflict (satisfiable) — must decline.
    let concat2 = PTerm::App(
        "str.++".to_string(),
        vec![
            PTerm::Symbol("x".to_string()),
            PTerm::Symbol("y".to_string()),
        ],
    );
    let sat_parsed = vec![PTerm::App(
        "=".to_string(),
        vec![
            PTerm::App("str.len".to_string(), vec![concat2]),
            PTerm::App("+".to_string(), vec![str_len("x"), str_len("y")]),
        ],
    )];
    assert!(emit_str_len_concat_firewall_lean_from_parsed(&sat_parsed).is_none());
}

#[test]
fn emits_str_len_zero_from_parsed_assertions() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    // (= (str.len s) 0) ∧ (not (= s "")) → unsat (len 0 ⟹ s = ε).
    let len_zero = PTerm::App(
        "=".to_string(),
        vec![
            PTerm::App("str.len".to_string(), vec![PTerm::Symbol("s".to_string())]),
            PTerm::Const(PConst::Numeral("0".to_string())),
        ],
    );
    let nonempty = PTerm::App(
        "not".to_string(),
        vec![PTerm::App(
            "=".to_string(),
            vec![
                PTerm::Symbol("s".to_string()),
                PTerm::Const(PConst::String(String::new())),
            ],
        )],
    );
    let parsed = vec![len_zero, nonempty];
    let lean = emit_str_len_zero_firewall_lean_from_parsed(&parsed)
        .expect("parsed str len-zero conflict should emit");
    assert!(lean.contains("import AySoundness.StringThy"));
    assert!(lean.contains("StringThy.len_zero_iff"));
    assert!(lean.contains("firewall_combined_unsat"));

    // A DIFFERENT non-empty symbol is not a conflict (no shared symbol) — decline.
    let other_nonempty = PTerm::App(
        "not".to_string(),
        vec![PTerm::App(
            "=".to_string(),
            vec![
                PTerm::Symbol("t".to_string()),
                PTerm::Const(PConst::String(String::new())),
            ],
        )],
    );
    let len_zero2 = PTerm::App(
        "=".to_string(),
        vec![
            PTerm::App("str.len".to_string(), vec![PTerm::Symbol("s".to_string())]),
            PTerm::Const(PConst::Numeral("0".to_string())),
        ],
    );
    assert!(emit_str_len_zero_firewall_lean_from_parsed(&[len_zero2, other_nonempty]).is_none());
}

#[test]
fn emits_string_length_from_parsed_assertions() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    // (= s "") and (= (str.len s) 3) → |""|=0 ≠ 3.
    let parsed = vec![
        PTerm::App(
            "=".to_string(),
            vec![
                PTerm::Symbol("s".to_string()),
                PTerm::Const(PConst::String(String::new())),
            ],
        ),
        PTerm::App(
            "=".to_string(),
            vec![
                PTerm::App("str.len".to_string(), vec![PTerm::Symbol("s".to_string())]),
                PTerm::Const(PConst::Numeral("3".to_string())),
            ],
        ),
    ];
    let lean = emit_string_length_firewall_lean_from_parsed(&parsed)
        .expect("parsed string conflict should emit");
    assert!(lean.contains("abbrev Val := String"));
    assert!(lean.contains("decide (m = \"\")"));
    assert!(lean.contains("decide (m.length = 3)"));
    assert!(lean.contains("firewall_combined_unsat"));
}

#[test]
fn emits_bv_firewall_from_parsed() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    // (= (bvand x y) #xF) and (not (= x #xF)) over BitVec 4.
    let band = PTerm::App(
        "bvand".to_string(),
        vec![
            PTerm::Symbol("x".to_string()),
            PTerm::Symbol("y".to_string()),
        ],
    );
    let parsed = vec![
        PTerm::App(
            "=".to_string(),
            vec![band, PTerm::Const(PConst::Hexadecimal("F".to_string()))],
        ),
        PTerm::App(
            "not".to_string(),
            vec![PTerm::App(
                "=".to_string(),
                vec![
                    PTerm::Symbol("x".to_string()),
                    PTerm::Const(PConst::Hexadecimal("F".to_string())),
                ],
            )],
        ),
    ];
    let lean = emit_bv_firewall_lean_from_parsed(&parsed).expect("BV conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("abbrev Val := BitVec 4 × BitVec 4"));
    assert!(lean.contains("(m.1 &&& m.2)"));
    assert!(lean.contains("(0xF#4)"));
    assert!(lean.contains("obtain ⟨v0, v1⟩ := m"));
    assert!(lean.contains("firewall_combined_unsat"));
}

#[test]
fn emits_bv_with_constant_pinned_var() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    // (= (bvmul x y) #x07) ∧ (= x #x02) over BitVec 8. Two free 8-bit vars =
    // 65536 cases (over the decide gate), but `x` is pinned to a constant, so
    // substituting x→2 leaves only `y` free (256 cases) — now emits.
    let hex8 = |s: &str| PTerm::Const(PConst::Hexadecimal(s.to_string()));
    let bmul = PTerm::App(
        "bvmul".to_string(),
        vec![
            PTerm::Symbol("x".to_string()),
            PTerm::Symbol("y".to_string()),
        ],
    );
    let parsed = vec![
        PTerm::App("=".to_string(), vec![bmul, hex8("07")]),
        PTerm::App(
            "=".to_string(),
            vec![PTerm::Symbol("x".to_string()), hex8("02")],
        ),
    ];
    let lean = emit_bv_firewall_lean_from_parsed(&parsed)
        .expect("BV-mul with a pinned variable should emit (substituting the constant)");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    // x is substituted by its constant; only y remains free (single-var model).
    assert!(lean.contains("abbrev Val := BitVec 8"));
    assert!(!lean.contains("BitVec 8 × BitVec 8"));
    assert!(lean.contains("(0x02#8)"));
    assert!(lean.contains("firewall_combined_unsat"));
}

#[test]
fn emits_dt_selector_congruence_from_parsed() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    // (= (fst p) 1) ∧ (= p q) ∧ (not (= (fst q) 1)) — selector congruence.
    let one = PTerm::Const(PConst::Numeral("1".to_string()));
    let fst_p = PTerm::App("fst".to_string(), vec![PTerm::Symbol("p".to_string())]);
    let fst_q = PTerm::App("fst".to_string(), vec![PTerm::Symbol("q".to_string())]);
    let pos = PTerm::App("=".to_string(), vec![fst_p, one.clone()]);
    let sub = PTerm::App(
        "=".to_string(),
        vec![
            PTerm::Symbol("p".to_string()),
            PTerm::Symbol("q".to_string()),
        ],
    );
    let neg = PTerm::App(
        "not".to_string(),
        vec![PTerm::App("=".to_string(), vec![fst_q, one])],
    );
    let parsed = vec![pos, sub, neg];

    let lean = emit_dt_selector_firewall_lean_from_parsed(&parsed)
        .expect("selector congruence conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("structure Val"));
    assert!(lean.contains("sel : Nat -> Int"));
    assert!(lean.contains(":= by rw [← h2]; exact h1") || lean.contains("rw [← h2]"));
    assert!(lean.contains("firewall_combined_unsat"));
}

#[test]
fn dt_selector_declines_without_substitution() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    // (= (fst p) 1) ∧ (not (= (fst q) 1)) but NO (= p q): genuinely SAT, must
    // not emit a (false) refutation.
    let one = PTerm::Const(PConst::Numeral("1".to_string()));
    let fst_p = PTerm::App("fst".to_string(), vec![PTerm::Symbol("p".to_string())]);
    let fst_q = PTerm::App("fst".to_string(), vec![PTerm::Symbol("q".to_string())]);
    let pos = PTerm::App("=".to_string(), vec![fst_p, one.clone()]);
    let neg = PTerm::App(
        "not".to_string(),
        vec![PTerm::App("=".to_string(), vec![fst_q, one])],
    );
    let parsed = vec![pos, neg];
    assert!(emit_dt_selector_firewall_lean_from_parsed(&parsed).is_none());
}

#[test]
fn emits_dt_injective_from_parsed() {
    use ay_frontend::command::Term as PTerm;
    // (= (mk a b) (mk c d)) ∧ (not (= a c)) — constructor injectivity.
    let mk_ab = PTerm::App(
        "mk".to_string(),
        vec![
            PTerm::Symbol("a".to_string()),
            PTerm::Symbol("b".to_string()),
        ],
    );
    let mk_cd = PTerm::App(
        "mk".to_string(),
        vec![
            PTerm::Symbol("c".to_string()),
            PTerm::Symbol("d".to_string()),
        ],
    );
    let eqc = PTerm::App("=".to_string(), vec![mk_ab, mk_cd]);
    let neg = PTerm::App(
        "not".to_string(),
        vec![PTerm::App(
            "=".to_string(),
            vec![
                PTerm::Symbol("a".to_string()),
                PTerm::Symbol("c".to_string()),
            ],
        )],
    );
    let parsed = vec![eqc, neg];
    let ctors = vec!["mk".to_string()];

    let lean = emit_dt_injective_firewall_lean_from_parsed(&parsed, &ctors)
        .expect("constructor injectivity should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("inductive Pr"));
    assert!(lean.contains("Pr.mk.inj"));
    assert!(lean.contains("firewall_combined_unsat"));
}

#[test]
fn dt_injective_declines_non_constructor() {
    use ay_frontend::command::Term as PTerm;
    // Same shape but `g` is NOT a constructor — injectivity is FALSE for an
    // arbitrary function, so the emitter must decline (soundness).
    let g_ab = PTerm::App(
        "g".to_string(),
        vec![
            PTerm::Symbol("a".to_string()),
            PTerm::Symbol("b".to_string()),
        ],
    );
    let g_cd = PTerm::App(
        "g".to_string(),
        vec![
            PTerm::Symbol("c".to_string()),
            PTerm::Symbol("d".to_string()),
        ],
    );
    let eqc = PTerm::App("=".to_string(), vec![g_ab, g_cd]);
    let neg = PTerm::App(
        "not".to_string(),
        vec![PTerm::App(
            "=".to_string(),
            vec![
                PTerm::Symbol("a".to_string()),
                PTerm::Symbol("c".to_string()),
            ],
        )],
    );
    let parsed = vec![eqc, neg];
    // `mk` is a constructor but `g` is not → no emit.
    let ctors = vec!["mk".to_string()];
    assert!(emit_dt_injective_firewall_lean_from_parsed(&parsed, &ctors).is_none());
}

#[test]
fn emits_nia_linear_after_pinning_from_parsed() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    // (= (* x y) 7) ∧ (= x 2): nonlinear, but x pinned ⟹ linear `2*y=7` (no
    // integer solution), grounded by omega.
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let mul = PTerm::App(
        "*".to_string(),
        vec![
            PTerm::Symbol("x".to_string()),
            PTerm::Symbol("y".to_string()),
        ],
    );
    let parsed = vec![
        PTerm::App("=".to_string(), vec![mul, num("7")]),
        PTerm::App(
            "=".to_string(),
            vec![PTerm::Symbol("x".to_string()), num("2")],
        ),
    ];
    let lean = emit_nia_linear_firewall_lean_from_parsed(&parsed)
        .expect("NIA conflict linear after pinning should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("structure Val"));
    assert!(lean.contains("(2 : Int)"));
    assert!(lean.contains("v.m"));
    assert!(lean.contains("by omega"));
    assert!(lean.contains("firewall_combined_unsat"));
}

#[test]
fn nia_linear_declines_genuinely_nonlinear() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    // (= (* x x) 2): genuinely nonlinear (no pinned var) ⟹ decline.
    let mul = PTerm::App(
        "*".to_string(),
        vec![
            PTerm::Symbol("x".to_string()),
            PTerm::Symbol("x".to_string()),
        ],
    );
    let parsed = vec![PTerm::App(
        "=".to_string(),
        vec![mul, PTerm::Const(PConst::Numeral("2".to_string()))],
    )];
    assert!(emit_nia_linear_firewall_lean_from_parsed(&parsed).is_none());
}

#[test]
fn emits_set_subset_transitivity_from_parsed() {
    use ay_frontend::command::Term as PTerm;
    // (set.subset A B) ∧ (set.subset B C) ∧ (not (set.subset A C)) — transitivity.
    let sub = |x: &str, y: &str| {
        PTerm::App(
            "set.subset".to_string(),
            vec![PTerm::Symbol(x.to_string()), PTerm::Symbol(y.to_string())],
        )
    };
    let neg = PTerm::App("not".to_string(), vec![sub("A", "C")]);
    let parsed = vec![sub("A", "B"), sub("B", "C"), neg];

    let lean = emit_set_subset_transitivity_firewall_lean_from_parsed(&parsed)
        .expect("subset transitivity should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("def sub"));
    assert!(lean.contains("fun e hae => h2 e (h1 e hae)"));
    assert!(lean.contains("firewall_combined_unsat"));
}

#[test]
fn set_subset_transitivity_declines_without_chain() {
    use ay_frontend::command::Term as PTerm;
    // (set.subset A B) ∧ (not (set.subset A C)) but NO (set.subset B C): no chain.
    let sub = |x: &str, y: &str| {
        PTerm::App(
            "set.subset".to_string(),
            vec![PTerm::Symbol(x.to_string()), PTerm::Symbol(y.to_string())],
        )
    };
    let neg = PTerm::App("not".to_string(), vec![sub("A", "C")]);
    let parsed = vec![sub("A", "B"), neg];
    assert!(emit_set_subset_transitivity_firewall_lean_from_parsed(&parsed).is_none());
}

#[test]
fn emits_euf_cong_trans_from_parsed() {
    use ay_frontend::command::Term as PTerm;
    // (= a b) ∧ (= b c) ∧ (not (= (f a) (f c))) — congruence over a transitive chain.
    let ab = PTerm::App(
        "=".to_string(),
        vec![
            PTerm::Symbol("a".to_string()),
            PTerm::Symbol("b".to_string()),
        ],
    );
    let bc = PTerm::App(
        "=".to_string(),
        vec![
            PTerm::Symbol("b".to_string()),
            PTerm::Symbol("c".to_string()),
        ],
    );
    let fa = PTerm::App("f".to_string(), vec![PTerm::Symbol("a".to_string())]);
    let fc = PTerm::App("f".to_string(), vec![PTerm::Symbol("c".to_string())]);
    let neg = PTerm::App(
        "not".to_string(),
        vec![PTerm::App("=".to_string(), vec![fa, fc])],
    );
    let parsed = vec![ab, bc, neg];

    let lean = emit_euf_cong_trans_firewall_lean_from_parsed(&parsed)
        .expect("congruence-over-transitivity should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("structure Val"));
    assert!(lean.contains("h1.trans h2"));
    assert!(lean.contains("firewall_combined_unsat"));
}

#[test]
fn euf_cong_trans_declines_without_chain() {
    use ay_frontend::command::Term as PTerm;
    // (= a b) ∧ (not (= (f a) (f c))) but NO chain to c: not the cong+trans shape.
    let ab = PTerm::App(
        "=".to_string(),
        vec![
            PTerm::Symbol("a".to_string()),
            PTerm::Symbol("b".to_string()),
        ],
    );
    let fa = PTerm::App("f".to_string(), vec![PTerm::Symbol("a".to_string())]);
    let fc = PTerm::App("f".to_string(), vec![PTerm::Symbol("c".to_string())]);
    let neg = PTerm::App(
        "not".to_string(),
        vec![PTerm::App("=".to_string(), vec![fa, fc])],
    );
    let parsed = vec![ab, neg];
    assert!(emit_euf_cong_trans_firewall_lean_from_parsed(&parsed).is_none());
}

#[test]
fn emits_array_row1_from_parsed() {
    use ay_frontend::command::Term as PTerm;
    // (not (= (select (store a i v) i) v)) — direct ROW-same conflict.
    let store = PTerm::App(
        "store".to_string(),
        vec![
            PTerm::Symbol("a".to_string()),
            PTerm::Symbol("i".to_string()),
            PTerm::Symbol("v".to_string()),
        ],
    );
    let sel = PTerm::App(
        "select".to_string(),
        vec![store, PTerm::Symbol("i".to_string())],
    );
    let eqn = PTerm::App("=".to_string(), vec![sel, PTerm::Symbol("v".to_string())]);
    let parsed = vec![PTerm::App("not".to_string(), vec![eqn])];

    let lean =
        emit_array_row1_firewall_lean_from_parsed(&parsed).expect("ROW-same conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("abbrev Val := (Nat → Nat) × (Nat → Nat)"));
    assert!(lean.contains("if (m.2 0) = (m.2 0) then (m.2 1) else"));
    assert!(lean.contains("firewall_combined_unsat"));
}

#[test]
fn emits_set_subset_ground_witness_from_parsed() {
    use ay_frontend::command::Term as PTerm;
    // (set.member x s) ∧ (not (set.member x t)) ∧ (set.subset s t) — the subset
    // definition at the ground witness x refutes it.
    let mem_xs = PTerm::App(
        "set.member".to_string(),
        vec![
            PTerm::Symbol("x".to_string()),
            PTerm::Symbol("s".to_string()),
        ],
    );
    let mem_xt = PTerm::App(
        "set.member".to_string(),
        vec![
            PTerm::Symbol("x".to_string()),
            PTerm::Symbol("t".to_string()),
        ],
    );
    let not_mem_xt = PTerm::App("not".to_string(), vec![mem_xt]);
    let subset_st = PTerm::App(
        "set.subset".to_string(),
        vec![
            PTerm::Symbol("s".to_string()),
            PTerm::Symbol("t".to_string()),
        ],
    );
    let parsed = vec![mem_xs, not_mem_xt, subset_st];

    let lean = emit_set_subset_firewall_lean_from_parsed(&parsed)
        .expect("ground-witness subset conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("structure Val"));
    assert!(lean.contains("decide (∀ e, m.s e = true → m.t e = true)"));
    assert!(lean.contains("[(4, [-3, -1, 2])]"));
    assert!(lean.contains("firewall_combined_unsat"));
}

#[test]
fn set_subset_declines_without_negated_member() {
    use ay_frontend::command::Term as PTerm;
    // Only (set.member x s) ∧ (set.subset s t): no `x ∉ t`, so no ground-witness
    // refutation — this is genuinely SAT, must NOT emit a (false) refutation.
    let mem_xs = PTerm::App(
        "set.member".to_string(),
        vec![
            PTerm::Symbol("x".to_string()),
            PTerm::Symbol("s".to_string()),
        ],
    );
    let subset_st = PTerm::App(
        "set.subset".to_string(),
        vec![
            PTerm::Symbol("s".to_string()),
            PTerm::Symbol("t".to_string()),
        ],
    );
    let parsed = vec![mem_xs, subset_st];
    assert!(emit_set_subset_firewall_lean_from_parsed(&parsed).is_none());
}

#[test]
fn set_subset_declines_reflexive() {
    use ay_frontend::command::Term as PTerm;
    // (set.subset s s) with a (not (set.member x s)) is reflexive — not the
    // ground-witness LHS≠RHS pattern; decline (avoid a spurious witness build).
    let subset_ss = PTerm::App(
        "set.subset".to_string(),
        vec![
            PTerm::Symbol("s".to_string()),
            PTerm::Symbol("s".to_string()),
        ],
    );
    let mem_xs = PTerm::App(
        "set.member".to_string(),
        vec![
            PTerm::Symbol("x".to_string()),
            PTerm::Symbol("s".to_string()),
        ],
    );
    let parsed = vec![subset_ss, mem_xs];
    assert!(emit_set_subset_firewall_lean_from_parsed(&parsed).is_none());
}

#[test]
fn array_row1_declines_index_mismatch() {
    use ay_frontend::command::Term as PTerm;
    // (not (= (select (store a i v) j) v)) — read index ≠ store index → NOT
    // ROW-same (that is ROW2 territory); decline.
    let store = PTerm::App(
        "store".to_string(),
        vec![
            PTerm::Symbol("a".to_string()),
            PTerm::Symbol("i".to_string()),
            PTerm::Symbol("v".to_string()),
        ],
    );
    let sel = PTerm::App(
        "select".to_string(),
        vec![store, PTerm::Symbol("j".to_string())],
    );
    let eqn = PTerm::App("=".to_string(), vec![sel, PTerm::Symbol("v".to_string())]);
    let parsed = vec![PTerm::App("not".to_string(), vec![eqn])];
    assert!(emit_array_row1_firewall_lean_from_parsed(&parsed).is_none());
}

#[test]
fn emits_array_nested_store_row_from_parsed() {
    use ay_frontend::command::Term as PTerm;
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let store = |a: PTerm, i: PTerm, v: PTerm| PTerm::App("store".to_string(), vec![a, i, v]);
    let select = |a: PTerm, i: PTerm| PTerm::App("select".to_string(), vec![a, i]);
    // write_write_overwrite: i ≠ j ∧
    //   select (store (store a i v1) i v2) j ≠ select (store a i v2) j.
    // Both sides reduce (j ≠ i) to select a j, so it is UNSAT.
    let diseq = PTerm::App(
        "not".to_string(),
        vec![PTerm::App("=".to_string(), vec![sym("i"), sym("j")])],
    );
    let lhs = select(
        store(store(sym("a"), sym("i"), sym("v1")), sym("i"), sym("v2")),
        sym("j"),
    );
    let rhs = select(store(sym("a"), sym("i"), sym("v2")), sym("j"));
    let main = PTerm::App(
        "not".to_string(),
        vec![PTerm::App("=".to_string(), vec![lhs, rhs])],
    );
    let parsed = vec![diseq, main.clone()];

    let lean = emit_array_nested_store_row_firewall_lean_from_parsed(&parsed)
        .expect("nested-store read-over-write conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("abbrev Val := (Nat → Nat) × (Nat → Nat)"));
    // The nested if-update unfolding of the outer/inner store layers: the read
    // index `j` is registered first (valuation 0), the store index `i` second
    // (valuation 1), and both store layers unfold to the same `if`-condition.
    assert!(lean.contains("(if (m.2 0) = (m.2 1) then (m.2 2) else (if (m.2 0) = (m.2 1) then"));
    assert!(lean.contains("by_cases h2 : (m.2 0) = (m.2 1)"));
    assert!(lean.contains("firewall_combined_unsat"));

    // Without the guard `i ≠ j`, this particular instance remains
    // UNCONDITIONALLY valid — both stores are at `i`, so the outer overwrite makes
    // `select (store (store a i v1) i v2) j = select (store a i v2) j` hold for all
    // `j` (the guarded and all-distinct branches both close). The relaxed emitter
    // recognizes that and grounds the unconditional `row_eq` lemma.
    let uncond = emit_array_nested_store_row_firewall_lean_from_parsed(&[main])
        .expect("unconditional store-overwrite identity should emit even without the guard");
    assert!(uncond.contains("namespace AySoundness.Emitted.ArrUncond_"));
    assert!(uncond.contains("firewall_combined_unsat"));

    // Genuine fail-closed: a ROW-OTHER read `select (store a i v) j` vs
    // `select a j` WITHOUT `i ≠ j` is SATISFIABLE (take `j = i`: the sides are `v`
    // and `a j`, which may differ), and the two if-trees DISAGREE on the `j = i`
    // branch, so the unconditional check declines — emitting would be UNSOUND.
    let sat_lhs = select(store(sym("a"), sym("i"), sym("v")), sym("j"));
    let sat_main = PTerm::App(
        "not".to_string(),
        vec![PTerm::App(
            "=".to_string(),
            vec![sat_lhs, select(sym("a"), sym("j"))],
        )],
    );
    assert!(emit_array_nested_store_row_firewall_lean_from_parsed(&[sat_main]).is_none());
}

#[test]
fn array_nested_store_declines_literal_symbol_identity_collisions() {
    use ay_frontend::command::{Constant as PConst, Index as PIndex, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let store = |a: PTerm, i: PTerm, v: PTerm| PTerm::App("store".to_string(), vec![a, i, v]);
    let select = |a: PTerm, i: PTerm| PTerm::App("select".to_string(), vec![a, i]);

    let assert_declines = |literal: PTerm, colliding_symbol: &str| {
        // This formula is SAT: choose r != i and interpret the quoted symbol
        // independently from the literal. The nested read equals the literal,
        // not the same-spelled symbol.
        let guard = PTerm::App(
            "not".to_string(),
            vec![PTerm::App("=".to_string(), vec![sym("r"), sym("i")])],
        );
        let lhs = select(
            store(store(sym("a"), sym("r"), literal), sym("i"), sym("v")),
            sym("r"),
        );
        let main = PTerm::App(
            "not".to_string(),
            vec![PTerm::App(
                "=".to_string(),
                vec![lhs, sym(colliding_symbol)],
            )],
        );

        assert!(emit_array_nested_store_row_firewall_lean_from_parsed(&[guard, main]).is_none());
    };

    let constants = [
        PConst::True,
        PConst::False,
        PConst::Numeral("0".to_string()),
        PConst::Decimal("0.0".to_string()),
        PConst::Hexadecimal("#x00".to_string()),
        PConst::Binary("#b0".to_string()),
        PConst::String("s".to_string()),
    ];
    for constant in constants {
        let colliding_symbol = format!("{constant:?}");
        assert_declines(PTerm::Const(constant), &colliding_symbol);
    }

    for (name, indices) in [
        ("bv0", vec![PIndex::Numeral("8".to_string())]),
        ("Char", vec![PIndex::Numeral("65".to_string())]),
        ("char", vec![PIndex::Hexadecimal("#x41".to_string())]),
        (
            "+zero",
            vec![
                PIndex::Numeral("8".to_string()),
                PIndex::Numeral("24".to_string()),
            ],
        ),
        (
            "-zero",
            vec![
                PIndex::Numeral("8".to_string()),
                PIndex::Numeral("24".to_string()),
            ],
        ),
        (
            "+oo",
            vec![
                PIndex::Numeral("8".to_string()),
                PIndex::Numeral("24".to_string()),
            ],
        ),
        (
            "-oo",
            vec![
                PIndex::Numeral("8".to_string()),
                PIndex::Numeral("24".to_string()),
            ],
        ),
        (
            "NaN",
            vec![
                PIndex::Numeral("8".to_string()),
                PIndex::Numeral("24".to_string()),
            ],
        ),
    ] {
        let colliding_symbol = format!(
            "(_ {name} {})",
            indices
                .iter()
                .map(PIndex::text)
                .collect::<Vec<_>>()
                .join(" ")
        );
        assert_declines(
            PTerm::IndexedApp(name.to_string(), indices, Vec::new()),
            &colliding_symbol,
        );
    }
}

#[test]
fn emits_bv_comparison_conflict_from_parsed() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    // (bvult x #x5) ∧ (bvule #x5 x) over BitVec 4 → unsat (x <ᵤ 5 ∧ 5 ≤ᵤ x).
    // Width 4 inferred from the literal; one variable.
    let five = || PTerm::Const(PConst::Hexadecimal("#x5".to_string()));
    let ult = PTerm::App(
        "bvult".to_string(),
        vec![PTerm::Symbol("x".to_string()), five()],
    );
    let ule = PTerm::App(
        "bvule".to_string(),
        vec![five(), PTerm::Symbol("x".to_string())],
    );
    let lean =
        emit_bv_firewall_lean_from_parsed(&[ult, ule]).expect("BV comparison conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains(".ult"));
    assert!(lean.contains(".ule"));
    assert!(lean.contains("(0x5#4)"));
    assert!(lean.contains("firewall_combined_unsat"));
}

#[test]
fn bv_declines_large_width() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    // 2 vars × 16-bit = 2^32 cases > gate → decline.
    let band = PTerm::App(
        "bvand".to_string(),
        vec![
            PTerm::Symbol("x".to_string()),
            PTerm::Symbol("y".to_string()),
        ],
    );
    let big = PConst::Hexadecimal("FFFF".to_string()); // 16-bit
    let parsed = vec![PTerm::App("=".to_string(), vec![band, PTerm::Const(big)])];
    assert!(emit_bv_firewall_lean_from_parsed(&parsed).is_none());
}

#[test]
fn parsed_string_no_conflict_when_lengths_agree() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    // (= s "abc") and (= (str.len s) 3): |"abc"|=3 = 3, no conflict.
    let parsed = vec![
        PTerm::App(
            "=".to_string(),
            vec![
                PTerm::Symbol("s".to_string()),
                PTerm::Const(PConst::String("abc".to_string())),
            ],
        ),
        PTerm::App(
            "=".to_string(),
            vec![
                PTerm::App("str.len".to_string(), vec![PTerm::Symbol("s".to_string())]),
                PTerm::Const(PConst::Numeral("3".to_string())),
            ],
        ),
    ];
    assert!(emit_string_length_firewall_lean_from_parsed(&parsed).is_none());
}

fn cmp(terms: &mut TermStore, op: &str, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named(op), vec![a, b], Sort::Bool)
}

#[test]
fn emits_firewall_lean_for_lia_bound_conflict() {
    // ¬(x ≤ 1) ∨ ¬(x ≥ 2): jointly unsatisfiable bound conflict.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(num_bigint::BigInt::from(1));
    let two = terms.mk_int(num_bigint::BigInt::from(2));
    let le = cmp(&mut terms, "<=", x, one);
    let ge = cmp(&mut terms, ">=", x, two);
    let l0 = terms.mk_not(le);
    let l1 = terms.mk_not(ge);

    let lean = emit_lia_firewall_lean(&terms, &[l0, l1]).expect("lia bound conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");

    for needle in [
        "import AySoundness.Firewall",
        "abbrev Val := Nat → Int",
        "(m 0) ≤ (1 : Int)",
        "(m 0) ≥ (2 : Int)",
        "omega",
        "firewall_combined_unsat",
        "theorem no_model",
    ] {
        assert!(lean.contains(needle), "emitted LIA Lean missing: {needle}");
    }
}

#[test]
fn lia_accepts_mixed_polarity_antisymmetry() {
    // ¬(x ≤ y) ∨ ¬(y ≤ x) ∨ (x = y): antisymmetry — a mixed-polarity LIA lemma
    // (positive equality literal). The emitter now supports mixed polarity.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let xy = cmp(&mut terms, "<=", x, y);
    let yx = cmp(&mut terms, "<=", y, x);
    let eqxy = cmp(&mut terms, "=", x, y);
    let l0 = terms.mk_not(xy);
    let l1 = terms.mk_not(yx);
    // l2 = (x = y) POSITIVE.
    let lean = emit_lia_firewall_lean(&terms, &[l0, l1, eqxy])
        .expect("mixed-polarity antisymmetry lemma should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("abbrev Val := Nat → Int"));
    assert!(lean.contains("omega"));
    // Mixed polarity: lemma clause carries +3 for the positive (x = y).
    assert!(
        lean.contains("[-1, -2, 3]"),
        "expected signed mixed-polarity clause"
    );
}

#[test]
fn lia_rejects_non_comparison_literal() {
    // A clause literal that is not a comparison (a bare Bool var) is rejected.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(num_bigint::BigInt::from(1));
    let le = cmp(&mut terms, "<=", x, one);
    let l0 = terms.mk_not(le);
    let p = terms.mk_var("p", Sort::Bool);
    assert!(emit_lia_firewall_lean(&terms, &[l0, p]).is_none());
}

fn eq(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![a, b], Sort::Bool)
}

#[test]
fn emits_firewall_lean_for_euf_transitivity() {
    // (not (= a b)) (not (= b c)) (= a c): equality transitivity, mixed polarity.
    let mut terms = TermStore::new();
    let u = |t: &mut TermStore, n: &str| t.mk_var(n, Sort::Uninterpreted("U".to_string()));
    let a = u(&mut terms, "a");
    let b = u(&mut terms, "b");
    let c = u(&mut terms, "c");
    let ab = eq(&mut terms, a, b);
    let bc = eq(&mut terms, b, c);
    let ac = eq(&mut terms, a, c);
    let l0 = terms.mk_not(ab);
    let l1 = terms.mk_not(bc);
    // l2 = (= a c) positive.
    let lean = emit_euf_firewall_lean(&terms, &[l0, l1, ac]).expect("euf transitivity emits");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");

    for needle in [
        "import AySoundness.Firewall",
        "abbrev Val := Nat → Nat",
        "(m 0) = (m 1)",
        "(m 1) = (m 2)",
        "(m 0) = (m 2)",
        "omega",
        "firewall_combined_unsat",
        // Mixed polarity: lemma clause has +3 for the positive (= a c).
        "[-1, -2, 3]",
    ] {
        assert!(lean.contains(needle), "emitted EUF Lean missing: {needle}");
    }
}

#[test]
fn emits_firewall_lean_for_euf_congruence() {
    // (not (= a b)) (= (f a) (f b)): congruence, single unary function.
    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = terms.mk_var("a", u.clone());
    let b = terms.mk_var("b", u.clone());
    let fa = terms.mk_app(Symbol::named("f"), vec![a], u.clone());
    let fb = terms.mk_app(Symbol::named("f"), vec![b], u.clone());
    let ab = eq(&mut terms, a, b);
    let fab = eq(&mut terms, fa, fb);
    let neg = terms.mk_not(ab);

    let lean =
        emit_euf_congruence_firewall_lean(&terms, &[neg, fab]).expect("euf congruence should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");

    for needle in [
        "abbrev Val := (Nat → Nat) × (Nat → Nat)",
        "(m.1 0) = (m.1 1)",
        "(m.2 (m.1 0)) = (m.2 (m.1 1))",
        "by_cases h1",
        "firewall_combined_unsat",
        "[-1, 2]",
    ] {
        assert!(
            lean.contains(needle),
            "emitted congruence Lean missing: {needle}"
        );
    }
}

#[test]
fn emits_firewall_lean_for_pred_congruence() {
    // (not (= a b)) (not (P a)) (P b): predicate congruence.
    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = terms.mk_var("a", u.clone());
    let b = terms.mk_var("b", u.clone());
    let pa = terms.mk_app(Symbol::named("P"), vec![a], Sort::Bool);
    let pb = terms.mk_app(Symbol::named("P"), vec![b], Sort::Bool);
    let ab = eq(&mut terms, a, b);
    let neg_ab = terms.mk_not(ab);
    let neg_pa = terms.mk_not(pa);
    // literals: ¬(a=b), ¬(P a), (P b)
    let lean = emit_euf_pred_congruence_firewall_lean(&terms, &[neg_ab, neg_pa, pb])
        .expect("predicate congruence should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");

    for needle in [
        "abbrev Val := (Nat → Nat) × (Nat → Bool)",
        "decide ((m.1 0) = (m.1 1))",
        "(m.2 (m.1 0))",
        "(m.2 (m.1 1))",
        "firewall_combined_unsat",
    ] {
        assert!(
            lean.contains(needle),
            "emitted pred-cong Lean missing: {needle}"
        );
    }
}

#[test]
fn emits_firewall_lean_for_array_row2() {
    // (i = j) OR (= (select (store a i v) j) (select a j)) — the
    // self-contained read-over-write-neg theorem.
    let mut terms = TermStore::new();
    let idx = Sort::Uninterpreted("Idx".to_string());
    let elem = Sort::Uninterpreted("Elem".to_string());
    let arr = Sort::array(idx.clone(), elem.clone());
    let a = terms.mk_var("a", arr.clone());
    let i = terms.mk_var("i", idx.clone());
    let j = terms.mk_var("j", idx.clone());
    let v = terms.mk_var("v", elem.clone());
    let store = terms.mk_app(Symbol::named("store"), vec![a, i, v], arr.clone());
    let sel_store = terms.mk_app(Symbol::named("select"), vec![store, j], elem.clone());
    let sel_a = terms.mk_app(Symbol::named("select"), vec![a, j], elem.clone());
    let eqn = eq(&mut terms, sel_store, sel_a);
    let guard = eq(&mut terms, i, j);

    let lean = emit_array_row2_firewall_lean(&terms, &[guard, eqn])
        .expect("guarded array ROW2 should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");

    for needle in [
        "abbrev Val := (Nat → Nat) × (Nat → Nat)",
        "if (m.2 1) = (m.2 0) then (m.2 2) else (m.1 (m.2 1))",
        "by_cases h : m.2 0 = m.2 1",
        "firewall_combined_unsat",
        "theorem no_model",
    ] {
        assert!(
            lean.contains(needle),
            "emitted array Lean missing: {needle}"
        );
    }
}

#[test]
fn array_row2_firewall_rejects_contextual_unit_without_guard() {
    let mut terms = TermStore::new();
    let idx = Sort::Uninterpreted("Idx".to_string());
    let elem = Sort::Uninterpreted("Elem".to_string());
    let arr = Sort::array(idx.clone(), elem.clone());
    let a = terms.mk_var("a", arr.clone());
    let i = terms.mk_var("i", idx.clone());
    let j = terms.mk_var("j", idx.clone());
    let v = terms.mk_var("v", elem.clone());
    let store = terms.mk_app(Symbol::named("store"), vec![a, i, v], arr);
    let sel_store = terms.mk_app(Symbol::named("select"), vec![store, j], elem.clone());
    let sel_a = terms.mk_app(Symbol::named("select"), vec![a, j], elem);
    let eqn = eq(&mut terms, sel_store, sel_a);

    assert!(
        emit_array_row2_firewall_lean(&terms, &[eqn]).is_none(),
        "a guard-less ROW2 equality is contextual, not a theorem"
    );
}

#[test]
fn array_row2_firewall_rejects_weakened_or_ill_typed_attribution() {
    let mut terms = TermStore::new();
    let idx = Sort::Uninterpreted("Idx".to_string());
    let elem = Sort::Uninterpreted("Elem".to_string());
    let arr = Sort::array(idx.clone(), elem.clone());
    let a = terms.mk_var("a", arr.clone());
    let i = terms.mk_var("i", idx.clone());
    let j = terms.mk_var("j", idx);
    let v = terms.mk_var("v", elem.clone());
    let store = terms.mk_app(Symbol::named("store"), vec![a, i, v], arr);
    let sel_store = terms.mk_app(Symbol::named("select"), vec![store, j], elem.clone());
    let sel_a = terms.mk_app(Symbol::named("select"), vec![a, j], elem);
    let row_eq = eq(&mut terms, sel_store, sel_a);
    let guard = eq(&mut terms, i, j);
    let p = terms.mk_var("p", Sort::Int);
    let q = terms.mk_var("q", Sort::Int);
    let pq_eq = eq(&mut terms, p, q);
    let extra = terms.mk_not(pq_eq);
    assert!(emit_array_row2_firewall_lean(&terms, &[guard, row_eq, extra]).is_none());

    let mut malformed = TermStore::new();
    let a = malformed.mk_var("a", Sort::Int);
    let i = malformed.mk_var("i", Sort::Int);
    let j = malformed.mk_var("j", Sort::Int);
    let v = malformed.mk_var("v", Sort::Int);
    let store = malformed.mk_app(Symbol::named("store"), vec![a, i, v], Sort::Int);
    let sel_store = malformed.mk_app(Symbol::named("select"), vec![store, j], Sort::Int);
    let sel_a = malformed.mk_app(Symbol::named("select"), vec![a, j], Sort::Int);
    let row_eq = eq(&mut malformed, sel_store, sel_a);
    let guard = eq(&mut malformed, i, j);
    assert!(emit_array_row2_firewall_lean(&malformed, &[guard, row_eq]).is_none());
}

#[test]
fn array_rejects_non_row2_shape() {
    // A plain equality of two selects (no store) is not the ROW2 structure.
    let mut terms = TermStore::new();
    let idx = Sort::Uninterpreted("Idx".to_string());
    let elem = Sort::Uninterpreted("Elem".to_string());
    let arr = Sort::array(idx.clone(), elem.clone());
    let a = terms.mk_var("a", arr.clone());
    let i = terms.mk_var("i", idx.clone());
    let j = terms.mk_var("j", idx.clone());
    let sa = terms.mk_app(Symbol::named("select"), vec![a, i], elem.clone());
    let sb = terms.mk_app(Symbol::named("select"), vec![a, j], elem.clone());
    let eqn = eq(&mut terms, sa, sb);
    assert!(emit_array_row2_firewall_lean(&terms, &[eqn]).is_none());
}

#[test]
fn emits_firewall_lean_for_binary_congruence() {
    // (not (= a c)) (not (= b d)) (= (f a b) (f c d)): binary congruence.
    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let mk = |t: &mut TermStore, n: &str| t.mk_var(n, u.clone());
    let a = mk(&mut terms, "a");
    let b = mk(&mut terms, "b");
    let c = mk(&mut terms, "c");
    let d = mk(&mut terms, "d");
    let fab = terms.mk_app(Symbol::named("f"), vec![a, b], u.clone());
    let fcd = terms.mk_app(Symbol::named("f"), vec![c, d], u.clone());
    let ac = eq(&mut terms, a, c);
    let bd = eq(&mut terms, b, d);
    let fabcd = eq(&mut terms, fab, fcd);
    let nac = terms.mk_not(ac);
    let nbd = terms.mk_not(bd);
    // literals: ¬(a=c), ¬(b=d), (f a b = f c d)
    let lean = emit_euf_congruence_firewall_lean(&terms, &[nac, nbd, fabcd])
        .expect("binary congruence should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(
        lean.contains("(Nat → Nat) × (Nat → Nat → Nat)"),
        "binary function model"
    );
    // f(a,b) with a→idx0, b→idx2 (c→1, d→3 in appearance order): m.2 (m.1 0) (m.1 2).
    assert!(
        lean.contains("(m.2 (m.1 0) (m.1 2))"),
        "binary application f(a,b)"
    );
    assert!(lean.contains("firewall_combined_unsat"));
    // Two argument by_cases (a=c, b=d).
    assert!(lean.contains("by_cases h1") && lean.contains("by_cases h2"));
}

#[test]
fn cong_rejects_two_functions() {
    // (not (= a b)) (= (f a) (g b)): two distinct functions — not modelable by a
    // single function component.
    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = terms.mk_var("a", u.clone());
    let b = terms.mk_var("b", u.clone());
    let fa = terms.mk_app(Symbol::named("f"), vec![a], u.clone());
    let gb = terms.mk_app(Symbol::named("g"), vec![b], u.clone());
    let ab = eq(&mut terms, a, b);
    let fagb = eq(&mut terms, fa, gb);
    let neg = terms.mk_not(ab);
    assert!(emit_euf_congruence_firewall_lean(&terms, &[neg, fagb]).is_none());
}

#[test]
fn euf_rejects_function_application() {
    // (not (= (f a) b)): a function application can't be modeled by a plain
    // valuation — emitter declines.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Uninterpreted("U".to_string()));
    let b = terms.mk_var("b", Sort::Uninterpreted("U".to_string()));
    let fa = terms.mk_app(
        Symbol::named("f"),
        vec![a],
        Sort::Uninterpreted("U".to_string()),
    );
    let fa_eq_b = eq(&mut terms, fa, b);
    let ab = eq(&mut terms, a, b);
    let l0 = terms.mk_not(fa_eq_b);
    let l1 = terms.mk_not(ab);
    assert!(emit_euf_firewall_lean(&terms, &[l0, l1]).is_none());
}

#[test]
fn rejects_cross_datatype() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Uninterpreted("X".to_string()));
    let red = ctor(&mut terms, "red", "Color");
    let on = ctor(&mut terms, "on", "Light");
    let l0 = neq(&mut terms, c, red);
    let l1 = neq(&mut terms, c, on);
    let decls = vec![
        (
            "Color".to_string(),
            vec!["red".to_string(), "green".to_string()],
        ),
        (
            "Light".to_string(),
            vec!["on".to_string(), "off".to_string()],
        ),
    ];

    assert!(emit_datatype_distinct_firewall_lean(&terms, &decls, &[l0, l1]).is_none());
}

#[test]
fn emits_fp_classification_from_parsed() {
    use ay_frontend::command::Term as PTerm;
    // (fp.isInfinite x) and (fp.isNaN x) — no float is both inf and NaN.
    let parsed = vec![
        PTerm::App(
            "fp.isInfinite".to_string(),
            vec![PTerm::Symbol("x".to_string())],
        ),
        PTerm::App("fp.isNaN".to_string(), vec![PTerm::Symbol("x".to_string())]),
    ];
    let lean = emit_fp_classification_firewall_lean_from_parsed(&parsed)
        .expect("FP inf∧nan conflict should emit");
    assert!(lean.contains("import AySoundness.FpThy"));
    assert!(lean.contains("@FpThy.isInfBits 2 2 x"));
    assert!(lean.contains("@FpThy.isNaNBits 2 2 x"));
    // exclusivity discharged inline by `decide` over the width-5 carrier.
    assert!(lean.contains(":= by decide"));
    assert!(lean.contains("firewall_combined_unsat"));
    assert!(!lean.contains("sorry"));
    assert!(!lean.contains("native_decide"));
}

#[test]
fn emits_fp_classification_conjunction_form() {
    use ay_frontend::command::Term as PTerm;
    // (and (fp.isZero x) (fp.isInfinite x)) — flattened; zero and inf are exclusive.
    let parsed = vec![PTerm::App(
        "and".to_string(),
        vec![
            PTerm::App(
                "fp.isZero".to_string(),
                vec![PTerm::Symbol("x".to_string())],
            ),
            PTerm::App(
                "fp.isInfinite".to_string(),
                vec![PTerm::Symbol("x".to_string())],
            ),
        ],
    )];
    let lean = emit_fp_classification_firewall_lean_from_parsed(&parsed)
        .expect("FP zero∧inf conjunction should emit");
    assert!(lean.contains("@FpThy.isZeroBits 2 2 x"));
    assert!(lean.contains("@FpThy.isInfBits 2 2 x"));
}

#[test]
fn emits_fp_subnormal_normal_pair() {
    use ay_frontend::command::Term as PTerm;
    // (fp.isSubnormal x) and (fp.isNormal x) — distinct classes, now covered.
    let parsed = vec![
        PTerm::App(
            "fp.isSubnormal".to_string(),
            vec![PTerm::Symbol("x".to_string())],
        ),
        PTerm::App(
            "fp.isNormal".to_string(),
            vec![PTerm::Symbol("x".to_string())],
        ),
    ];
    let lean = emit_fp_classification_firewall_lean_from_parsed(&parsed)
        .expect("FP subnormal∧normal conflict should emit");
    assert!(lean.contains("@FpThy.isNormalBits 2 2 x"));
    assert!(lean.contains("@FpThy.isSubnormalBits 2 2 x"));
    assert!(lean.contains(":= by decide"));
}

#[test]
fn declines_fp_non_conflict() {
    use ay_frontend::command::Term as PTerm;
    // Same class twice (no conflict), and a conflict pair on DIFFERENT variables.
    let parsed = vec![
        PTerm::App(
            "fp.isInfinite".to_string(),
            vec![PTerm::Symbol("x".to_string())],
        ),
        PTerm::App("fp.isNaN".to_string(), vec![PTerm::Symbol("y".to_string())]),
    ];
    assert!(emit_fp_classification_firewall_lean_from_parsed(&parsed).is_none());
}

/// Parse a single SMT-LIB assertion body into a frontend `Term` (the real
/// parser, so `IndexedApp` / `Const(Binary "#b…")` structure is exactly as ay
/// sees it at runtime).
fn parse_assertion(s: &str) -> ay_frontend::command::Term {
    use ay_frontend::command::Term as PTerm;
    let sexp = ay_frontend::sexp::parse_sexp(s).expect("sexp parse");
    PTerm::from_sexp(&sexp).expect("term parse")
}

#[test]
fn emits_fp_tofp_narrow_subnormal_underflow_from_parsed() {
    // benchmarks/.../fp_tofp_narrow_subnormal_underflow.smt2:
    //   (assert (fp.isInfinite ((_ to_fp 3 5) RTN (fp #b1 #b00000 #b0010000))))
    // Source (fp #b1 #b00000 #b0010000) is a NEGATIVE subnormal in format (eb=5,
    // sb=8); its magnitude 2^-17 is far below maxFinite(3,5)=15.5, so the RTN
    // narrowing floors to a finite (subnormal) value — NOT infinite. UNSAT.
    let parsed = vec![parse_assertion(
        "(fp.isInfinite ((_ to_fp 3 5) RTN (fp #b1 #b00000 #b0010000)))",
    )];
    let lean = emit_fp_tofp_underflow_firewall_lean_from_parsed(&parsed)
        .expect("fp.isInfinite to_fp underflow conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    for needle in [
        "import AySoundness.FpUnderflow",
        "open AySoundness.FpUnderflow",
        // exact IEEE decode: sign=true (neg), expf=0 (subnormal), sigf=16.
        "def src : Dy := decodeFin 5 8 true 0 16",
        "isInf (classifyRTN 3 5 src)",
        "firewall_combined_unsat",
        "#print axioms no_model",
    ] {
        assert!(lean.contains(needle), "emitted Lean missing: {needle}");
    }
    assert!(!lean.contains("sorry"));
    assert!(!lean.contains("native_decide"));
}

#[test]
fn emits_fp_tofp_narrow_signed_exponent_from_parsed() {
    // benchmarks/.../fp_tofp_narrow_signed_exponent.smt2:
    //   (assert (fp.isNormal ((_ to_fp 4 4) RTN
    //             (fp #b0 #b01000110 #b10100000111101000011111))))
    // Source is a POSITIVE single-precision normal (eb=8, sb=24) with magnitude
    // ≈2^-57, far below minNormal(4,4)=2^-6 (indeed below subQ), so the RTN
    // narrowing underflows to +0 — NOT normal. UNSAT.
    let parsed = vec![parse_assertion(
        "(fp.isNormal ((_ to_fp 4 4) RTN (fp #b0 #b01000110 #b10100000111101000011111)))",
    )];
    let lean = emit_fp_tofp_underflow_firewall_lean_from_parsed(&parsed)
        .expect("fp.isNormal to_fp underflow conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    for needle in [
        "import AySoundness.FpUnderflow",
        // exact IEEE decode: sign=false (pos), expf=70, sigf=5274143.
        "def src : Dy := decodeFin 8 24 false 70 5274143",
        "isNorm (classifyRTN 4 4 src)",
        "firewall_combined_unsat",
        "#print axioms no_model",
    ] {
        assert!(lean.contains(needle), "emitted Lean missing: {needle}");
    }
    assert!(!lean.contains("sorry"));
    assert!(!lean.contains("native_decide"));
}

#[test]
fn declines_fp_tofp_non_concrete_or_symbolic() {
    use ay_frontend::command::Term as PTerm;
    // Symbolic float argument (not a ground `(fp …)` literal) — decline.
    let symbolic = vec![parse_assertion("(fp.isInfinite ((_ to_fp 3 5) RTN x))")];
    assert!(emit_fp_tofp_underflow_firewall_lean_from_parsed(&symbolic).is_none());

    // Non-RTN rounding mode (the model only covers round-toward-negative) — decline.
    let rne = vec![parse_assertion(
        "(fp.isInfinite ((_ to_fp 3 5) RNE (fp #b1 #b00000 #b0010000)))",
    )];
    assert!(emit_fp_tofp_underflow_firewall_lean_from_parsed(&rne).is_none());

    // A class predicate NOT over a `to_fp` conversion (bare float variable) —
    // outside this emitter's shape (the classification emitter handles those).
    let bare = vec![PTerm::App(
        "fp.isInfinite".to_string(),
        vec![PTerm::Symbol("x".to_string())],
    )];
    assert!(emit_fp_tofp_underflow_firewall_lean_from_parsed(&bare).is_none());

    // `fp.isZero` over a concrete conversion — the model exposes `isInf`/`isNorm`
    // only, so a different class predicate is out of scope — decline.
    let zero = vec![parse_assertion(
        "(fp.isZero ((_ to_fp 3 5) RTN (fp #b1 #b00000 #b0010000)))",
    )];
    assert!(emit_fp_tofp_underflow_firewall_lean_from_parsed(&zero).is_none());
}

#[test]
fn emits_fp_rem_not_negative_rank6_from_parsed() {
    // benchmarks/smt/regression/soundness_fuzz_round2/rank6_qf_fp_false_SAT.smt2:
    //   (assert (fp.isNegative
    //     (fp.rem (fp #b1 #b11110 #b1111100110) (fp #b1 #b00000 #b1001101111))))
    // Both operands are format (eb=5, sb=11). a = −64704 (negative normal),
    // b = −623·2^−24 (negative subnormal). The exact round-to-nearest-even
    // remainder is 263·2^−24 > 0 — NOT negative. So the assertion is UNSAT.
    let parsed = vec![parse_assertion(
        "(fp.isNegative (fp.rem (fp #b1 #b11110 #b1111100110) (fp #b1 #b00000 #b1001101111)))",
    )];
    let lean = emit_fp_rem_not_negative_firewall_lean_from_parsed(&parsed)
        .expect("fp.rem sign conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    for needle in [
        "import AySoundness.FpUnderflow",
        "open AySoundness.FpUnderflow",
        // exact IEEE decode of dividend a: sign=true (neg), expf=30, sigf=998.
        "def a : Dy := decodeFin 5 11 true 30 998",
        // exact IEEE decode of divisor b: sign=true (neg), expf=0, sigf=623.
        "def b : Dy := decodeFin 5 11 true 0 623",
        // the asserted atom threads the dividend's sign bit (true).
        "remIsNegative true a b",
        "firewall_combined_unsat",
        "#print axioms no_model",
    ] {
        assert!(lean.contains(needle), "emitted Lean missing: {needle}");
    }
    assert!(!lean.contains("sorry"));
    assert!(!lean.contains("native_decide"));
}

#[test]
fn declines_fp_rem_non_concrete_or_mismatched() {
    use ay_frontend::command::Term as PTerm;
    // Symbolic operand (not a ground `(fp …)` literal) — decline.
    let symbolic = vec![parse_assertion(
        "(fp.isNegative (fp.rem x (fp #b1 #b00000 #b1001101111)))",
    )];
    assert!(emit_fp_rem_not_negative_firewall_lean_from_parsed(&symbolic).is_none());

    // Mismatched operand formats (different exponent widths) — decline.
    let mismatched = vec![parse_assertion(
        "(fp.isNegative (fp.rem (fp #b1 #b11110 #b1111100110) (fp #b1 #b0000 #b1001101111)))",
    )];
    assert!(emit_fp_rem_not_negative_firewall_lean_from_parsed(&mismatched).is_none());

    // A different sign predicate over the concrete remainder — out of scope.
    let positive = vec![parse_assertion(
        "(fp.isPositive (fp.rem (fp #b1 #b11110 #b1111100110) (fp #b1 #b00000 #b1001101111)))",
    )];
    assert!(emit_fp_rem_not_negative_firewall_lean_from_parsed(&positive).is_none());

    // `fp.isNegative` over a bare symbol (not an `fp.rem`) — decline.
    let bare = vec![PTerm::App(
        "fp.isNegative".to_string(),
        vec![PTerm::Symbol("x".to_string())],
    )];
    assert!(emit_fp_rem_not_negative_firewall_lean_from_parsed(&bare).is_none());
}

// ----------------------------------------------------------------------------
// RNE dot-product forward-error firewall (`guard_claim` shape).
// ----------------------------------------------------------------------------

/// The declared-format table a `guard_claim` script produces: the seven inputs
/// and the six named intermediates are `Float64`, `B`/`rreal` are `Real`.
fn fp_formats_of(fmt: (u32, u32)) -> Vec<(String, Option<(u32, u32)>)> {
    let mut out: Vec<(String, Option<(u32, u32)>)> = [
        "nx", "ny", "nz", "px", "py", "pz", "d", "t1", "t2", "t3", "s1", "s2", "rf",
    ]
    .iter()
    .map(|n| ((*n).to_string(), Some(fmt)))
    .collect();
    out.push(("B".to_string(), None));
    out.push(("rreal".to_string(), None));
    out
}

/// The binary64 (`Float64`) declared-format table.
fn f64_formats() -> Vec<(String, Option<(u32, u32)>)> {
    fp_formats_of((11, 53))
}

/// The seven magnitude/normality constraints of the `guard_claim` shape:
/// `|nᵢ| ≤ 1` for the direction, `|pᵢ|,|d| ≤ 2⁴⁸` for the position/offset.
fn guard_mag_constraints(pbound: &str) -> Vec<ay_frontend::command::Term> {
    let mk = |v: &str, b: &str| {
        parse_assertion(&format!(
            "(and (fp.isNormal {v}) (<= (fp.to_real (fp.abs {v})) {b}))"
        ))
    };
    vec![
        mk("nx", "1.0"),
        mk("ny", "1.0"),
        mk("nz", "1.0"),
        mk("px", pbound),
        mk("py", pbound),
        mk("pz", pbound),
        mk("d", pbound),
    ]
}

/// The fully-INLINED threshold assertion of `guard_claim_guard2` (no define-fun
/// indirection): `(>= (- (fp.to_real rf) rreal) THRESHOLD)` with `rf`/`rreal`
/// expanded to their bodies.
fn guard_threshold_inlined(threshold: &str) -> ay_frontend::command::Term {
    parse_assertion(&format!(
        "(>= (- (fp.to_real \
            (fp.add RNE (fp.add RNE (fp.add RNE (fp.mul RNE nx px) (fp.mul RNE ny py)) \
              (fp.mul RNE nz pz)) d)) \
            (+ (* (fp.to_real nx) (fp.to_real px)) (* (fp.to_real ny) (fp.to_real py)) \
               (* (fp.to_real nz) (fp.to_real pz)) (fp.to_real d))) {threshold})"
    ))
}

// ----------------------------------------------------------------------------
// The FORMAT prerequisite: `Float64` vs its byte-identical `Float32` clone.
// ----------------------------------------------------------------------------

/// The full parsed shape of `benchmarks/smt/QF_FPLRA/guard_claim_guard2.smt2`
/// and of `guard_claim_guard2_float32.smt2` — they are the SAME terms.
fn guard2_parsed_and_defined() -> (
    Vec<ay_frontend::command::Term>,
    Vec<(String, ay_frontend::command::Term)>,
) {
    let d = |n: &str, body: &str| (n.to_string(), parse_assertion(body));
    let defined = vec![
        d("B", "281474976710656.0"),
        d("t1", "(fp.mul RNE nx px)"),
        d("t2", "(fp.mul RNE ny py)"),
        d("t3", "(fp.mul RNE nz pz)"),
        d("s1", "(fp.add RNE t1 t2)"),
        d("s2", "(fp.add RNE s1 t3)"),
        d("rf", "(fp.add RNE s2 d)"),
        d(
            "rreal",
            "(+ (* (fp.to_real nx) (fp.to_real px)) (* (fp.to_real ny) (fp.to_real py)) \
               (* (fp.to_real nz) (fp.to_real pz)) (fp.to_real d))",
        ),
    ];
    let mut parsed = guard_mag_constraints("B");
    parsed.push(parse_assertion("(>= (- (fp.to_real rf) rreal) 2.0)"));
    (parsed, defined)
}

#[test]
fn guard2_float32_clone_has_identical_parsed_terms() {
    // The premise of the whole format prerequisite: the ONLY thing separating
    // the UNSAT Float64 benchmark from its SATISFIABLE Float32 clone is the
    // declaration sorts, which the parsed terms do not carry. If this ever
    // stops holding, the format gate below is no longer the thing standing
    // between the emitter and a wrong `unsat`.
    let (parsed_a, defined_a) = guard2_parsed_and_defined();
    let (parsed_b, defined_b) = guard2_parsed_and_defined();
    assert_eq!(parsed_a, parsed_b);
    assert_eq!(defined_a, defined_b);
    assert_ne!(f64_formats(), fp_formats_of((8, 24)));
}

#[test]
fn fp_vocabulary_binary64_gate_accepts_float64_and_rejects_every_other_format() {
    let (parsed, defined) = guard2_parsed_and_defined();

    // Float64 (11, 53): the gate passes — it is the only thing that does.
    assert!(parsed_fp_vocabulary_is_binary64(
        &parsed,
        &defined,
        &f64_formats()
    ));

    // Float16 (5, 11), Float32 (8, 24), Float128 (15, 113) and a bespoke
    // `(_ FloatingPoint 11 54)` must all be refused. The Float32 case is the
    // live wrong-`unsat` hazard: `guard_claim_guard2_float32.smt2` is SAT, and
    // `guard_claim_guard2_float32_witness.smt2` pins a model with error
    // 16777214 >= 2.
    for fmt in [(5u32, 11u32), (8, 24), (15, 113), (11, 54), (12, 53)] {
        assert!(
            !parsed_fp_vocabulary_is_binary64(&parsed, &defined, &fp_formats_of(fmt)),
            "format {fmt:?} must be refused"
        );
    }
}

#[test]
fn fp_vocabulary_binary64_gate_is_fail_closed_on_unknown_and_mixed_vocabulary() {
    let (parsed, defined) = guard2_parsed_and_defined();

    // An EMPTY table: every operand's sort is unknown. Unknown is not binary64.
    assert!(!parsed_fp_vocabulary_is_binary64(&parsed, &defined, &[]));

    // One operand missing from the table (e.g. dropped as ambiguous/overloaded)
    // is enough to decline — the gate never fills a gap with a guess.
    for missing in ["nx", "px", "d", "t1", "s2", "rf"] {
        let mut table = f64_formats();
        table.retain(|(n, _)| n != missing);
        assert!(
            !parsed_fp_vocabulary_is_binary64(&parsed, &defined, &table),
            "missing declaration for {missing} must decline"
        );
    }

    // One operand declared with a NON-floating-point sort is also a decline:
    // `Some(None)` means "declared, not FP", which cannot be binary64 either.
    let mut mixed = f64_formats();
    for entry in &mut mixed {
        if entry.0 == "pz" {
            entry.1 = None;
        }
    }
    assert!(!parsed_fp_vocabulary_is_binary64(&parsed, &defined, &mixed));

    // A SINGLE Float32 operand among twelve Float64 ones still declines.
    let mut one_f32 = f64_formats();
    for entry in &mut one_f32 {
        if entry.0 == "py" {
            entry.1 = Some((8, 24));
        }
    }
    assert!(!parsed_fp_vocabulary_is_binary64(
        &parsed, &defined, &one_f32
    ));
}

#[test]
fn fp_vocabulary_binary64_gate_declines_when_there_is_no_fp_vocabulary() {
    // No `fp.*` application at all: nothing was checked, so nothing is
    // certified. Declining here is what makes "the gate passed" meaningful.
    let parsed = vec![parse_assertion("(>= (- x y) 2.0)")];
    let defined: Vec<(String, ay_frontend::command::Term)> = Vec::new();
    assert!(!parsed_fp_vocabulary_is_binary64(
        &parsed,
        &defined,
        &f64_formats()
    ));
}

#[test]
fn fp_vocabulary_binary64_gate_never_classifies_a_symbol_by_prefix() {
    // `RNE` is a rounding mode; `RNEx`, `RN`, `rne`, `roundy`, `fpx` are all
    // legal user-declarable SMT-LIB simple symbols and NOT rounding modes.
    // Each must be treated as a real floating-point operand, so an absent or
    // wrong-format declaration for it must decline.
    for name in ["RNEx", "RN", "rne", "roundy", "fpx", "RNE2"] {
        let parsed = vec![parse_assertion(&format!("(fp.isNormal {name})"))];
        let defined: Vec<(String, ay_frontend::command::Term)> = Vec::new();
        assert!(
            !parsed_fp_vocabulary_is_binary64(&parsed, &defined, &[]),
            "{name} must be treated as an operand needing a declaration"
        );
        assert!(
            parsed_fp_vocabulary_is_binary64(
                &parsed,
                &defined,
                &[(name.to_string(), Some((11, 53)))]
            ),
            "{name} declared Float64 must pass"
        );
        assert!(
            !parsed_fp_vocabulary_is_binary64(
                &parsed,
                &defined,
                &[(name.to_string(), Some((8, 24)))]
            ),
            "{name} declared Float32 must decline"
        );
    }

    // The real rounding mode is skipped, so `RNE` needs no declaration.
    let rne = vec![parse_assertion("(fp.isNormal (fp.mul RNE nx px))")];
    let defined: Vec<(String, ay_frontend::command::Term)> = Vec::new();
    assert!(parsed_fp_vocabulary_is_binary64(
        &rne,
        &defined,
        &[
            ("nx".to_string(), Some((11, 53))),
            ("px".to_string(), Some((11, 53))),
        ]
    ));
}

#[test]
fn fp_vocabulary_binary64_gate_declines_binding_forms() {
    // A `let`-bound name is NOT the declared symbol of that name, so looking it
    // up in the declaration table would read the wrong sort. Refuse the term.
    let bound = vec![parse_assertion(
        "(let ((nx (fp.mul RNE py pz))) (fp.isNormal nx))",
    )];
    let defined: Vec<(String, ay_frontend::command::Term)> = Vec::new();
    assert!(!parsed_fp_vocabulary_is_binary64(
        &bound,
        &defined,
        &f64_formats()
    ));

    // Same for a `let` hidden inside a macro body rather than an assertion.
    let (parsed, _) = guard2_parsed_and_defined();
    let shadowing_defined = vec![(
        "t1".to_string(),
        parse_assertion("(let ((px pz)) (fp.mul RNE nx px))"),
    )];
    assert!(!parsed_fp_vocabulary_is_binary64(
        &parsed,
        &shadowing_defined,
        &f64_formats()
    ));
}

#[test]
fn fp_dot_error_bound_declines_the_satisfiable_float32_clone() {
    // THE PREREQUISITE, end to end. Identical parsed terms, two declaration
    // tables. Both must decline today (the semantic-bridge authority gate is
    // still closed), but the Float32 one must decline for the FORMAT reason —
    // which is checked directly by the gate assertions below, so that if the
    // authority gate is ever opened the Float32 clone stays refused.
    let (parsed, defined) = guard2_parsed_and_defined();

    assert!(parsed_fp_vocabulary_is_binary64(
        &parsed,
        &defined,
        &f64_formats()
    ));
    assert!(!parsed_fp_vocabulary_is_binary64(
        &parsed,
        &defined,
        &fp_formats_of((8, 24))
    ));

    assert!(emit_fp_dot_error_bound_firewall_lean_from_parsed(
        &parsed,
        &defined,
        &fp_formats_of((8, 24))
    )
    .is_none());
    assert!(
        emit_fp_dot_error_bound_firewall_lean_from_parsed(&parsed, &defined, &f64_formats())
            .is_none()
    );
}

#[test]
fn declines_fp_dot_error_bound_guard2_inlined_from_parsed() {
    // benchmarks/smt/QF_FPLRA/guard_claim_guard2.smt2 (define-funs inlined):
    // seven Float64 inputs, |n*|<=1, |p*|,|d|<=2^48, and the six-op RNE
    // signed-distance evaluation asserted to differ from the exact real dot by
    // >= 2.0. The qround lemma alone does not connect this IEEE formula to its
    // fixed-spacing model, so proof emission must decline.
    let mut parsed = guard_mag_constraints("281474976710656.0");
    parsed.push(guard_threshold_inlined("2.0"));
    let defined: Vec<(String, ay_frontend::command::Term)> = Vec::new();
    assert!(
        emit_fp_dot_error_bound_firewall_lean_from_parsed(&parsed, &defined, &f64_formats())
            .is_none()
    );
}

#[test]
fn declines_fp_dot_error_bound_guard2_with_define_fun_resolution() {
    // The REAL benchmark shape: rf/rreal/B/t1../s2 are parameter-less define-fun
    // macros and the assertion references them by name. This remains fail-closed
    // until an IEEE-to-qround theorem exists.
    let d = |n: &str, body: &str| (n.to_string(), parse_assertion(body));
    let defined = vec![
        d("B", "281474976710656.0"),
        d("t1", "(fp.mul RNE nx px)"),
        d("t2", "(fp.mul RNE ny py)"),
        d("t3", "(fp.mul RNE nz pz)"),
        d("s1", "(fp.add RNE t1 t2)"),
        d("s2", "(fp.add RNE s1 t3)"),
        d("rf", "(fp.add RNE s2 d)"),
        d(
            "rreal",
            "(+ (* (fp.to_real nx) (fp.to_real px)) (* (fp.to_real ny) (fp.to_real py)) \
               (* (fp.to_real nz) (fp.to_real pz)) (fp.to_real d))",
        ),
    ];
    let mut parsed = guard_mag_constraints("B");
    parsed.push(parse_assertion("(>= (- (fp.to_real rf) rreal) 2.0)"));
    assert!(
        emit_fp_dot_error_bound_firewall_lean_from_parsed(&parsed, &defined, &f64_formats())
            .is_none()
    );
}

#[test]
fn declines_fp_dot_error_bound_higher_threshold_without_ieee_bridge() {
    // A larger threshold does not repair the missing semantic bridge.
    let mut parsed = guard_mag_constraints("281474976710656.0");
    parsed.push(guard_threshold_inlined("4.0"));
    let defined: Vec<(String, ay_frontend::command::Term)> = Vec::new();
    assert!(
        emit_fp_dot_error_bound_firewall_lean_from_parsed(&parsed, &defined, &f64_formats())
            .is_none()
    );
}

#[test]
fn fp_dot_error_bound_threshold_authority_is_fail_closed_at_boundaries() {
    let defined: Vec<(String, ay_frontend::command::Term)> = Vec::new();

    // The binade-refined qround theorem is promising research, but it lacks a
    // proved bridge from these IEEE-754 operations and magnitude hypotheses.
    // Both sides of 0.3 therefore remain non-authoritative.
    for threshold in ["0.299999999999999999", "0.3"] {
        let mut parsed = guard_mag_constraints("281474976710656.0");
        parsed.push(guard_threshold_inlined(threshold));
        assert!(
            emit_fp_dot_error_bound_firewall_lean_from_parsed(&parsed, &defined, &f64_formats())
                .is_none(),
            "sub-2.0 threshold {threshold} must decline"
        );
    }

    // The coarse model also lacks an IEEE bridge, on both sides of 2.0.
    let mut below_two = guard_mag_constraints("281474976710656.0");
    below_two.push(guard_threshold_inlined("1.999999999999999999"));
    assert!(
        emit_fp_dot_error_bound_firewall_lean_from_parsed(&below_two, &defined, &f64_formats())
            .is_none(),
        "threshold immediately below 2.0 must decline"
    );

    let mut at_two = guard_mag_constraints("281474976710656.0");
    at_two.push(guard_threshold_inlined("2.0"));
    assert!(
        emit_fp_dot_error_bound_firewall_lean_from_parsed(&at_two, &defined, &f64_formats())
            .is_none(),
        "threshold 2.0 must decline without an IEEE-to-qround bridge"
    );
}

#[test]
fn fp_dot_error_bound_oversized_rationals_decline_without_panicking() {
    let defined: Vec<(String, ay_frontend::command::Term)> = Vec::new();

    // These exercise i128::MAX, one beyond MAX, textual MIN, a 10^38
    // denominator, and an arbitrarily larger numeral. None may reach bounded
    // scaling/cross-product arithmetic while the authority gate is closed.
    for threshold in [
        "170141183460469231731687303715884105727",
        "170141183460469231731687303715884105728",
        "-170141183460469231731687303715884105728",
        "0.00000000000000000000000000000000000001",
        "9999999999999999999999999999999999999999999999999999999999999999",
    ] {
        let mut parsed = guard_mag_constraints("281474976710656.0");
        parsed.push(guard_threshold_inlined(threshold));
        assert!(
            emit_fp_dot_error_bound_firewall_lean_from_parsed(&parsed, &defined, &f64_formats())
                .is_none(),
            "oversized threshold {threshold} must decline"
        );
    }
}

#[test]
fn declines_fp_dot_error_bound_subthreshold_and_malformed() {
    let defined: Vec<(String, ay_frontend::command::Term)> = Vec::new();

    // guard_claim_tight_1e7: threshold 1e-7, and the problem is genuinely SAT —
    // emitting UNSAT would be UNSOUND. Decline.
    let mut tight = guard_mag_constraints("281474976710656.0");
    tight.push(guard_threshold_inlined("0.0000001"));
    assert!(
        emit_fp_dot_error_bound_firewall_lean_from_parsed(&tight, &defined, &f64_formats())
            .is_none()
    );

    // Missing magnitude constraints (only the threshold assertion) — the scaling
    // model's spacing is unjustified, so fail-closed. Decline.
    let bare = vec![guard_threshold_inlined("2.0")];
    assert!(
        emit_fp_dot_error_bound_firewall_lean_from_parsed(&bare, &defined, &f64_formats())
            .is_none()
    );

    // Wrong position magnitude bound (2^49 instead of 2^48) — the modeled
    // spacing would UNDER-approximate the true ulp. Decline.
    let mut wrongb = guard_mag_constraints("562949953421312.0"); // 2^49
    wrongb.push(guard_threshold_inlined("2.0"));
    assert!(
        emit_fp_dot_error_bound_firewall_lean_from_parsed(&wrongb, &defined, &f64_formats())
            .is_none()
    );

    // Any non-RNE operation is outside the half-ULP theorem's scope.
    let mut wrong_rm = guard_mag_constraints("281474976710656.0");
    wrong_rm.push(parse_assertion(
        "(>= (- (fp.to_real \
            (fp.add RTZ (fp.add RNE (fp.add RNE (fp.mul RNE nx px) (fp.mul RNE ny py)) \
              (fp.mul RNE nz pz)) d)) \
            (+ (* (fp.to_real nx) (fp.to_real px)) (* (fp.to_real ny) (fp.to_real py)) \
               (* (fp.to_real nz) (fp.to_real pz)) (fp.to_real d))) 2.0)",
    ));
    assert!(
        emit_fp_dot_error_bound_firewall_lean_from_parsed(&wrong_rm, &defined, &f64_formats())
            .is_none()
    );

    // Reassociated accumulator (d added first) — not the certified association.
    let mut reassoc = guard_mag_constraints("281474976710656.0");
    reassoc.push(parse_assertion(
        "(>= (- (fp.to_real \
            (fp.add RNE d (fp.add RNE (fp.add RNE (fp.mul RNE nx px) (fp.mul RNE ny py)) \
              (fp.mul RNE nz pz)))) \
            (+ (* (fp.to_real nx) (fp.to_real px)) (* (fp.to_real ny) (fp.to_real py)) \
               (* (fp.to_real nz) (fp.to_real pz)) (fp.to_real d))) 2.0)",
    ));
    assert!(
        emit_fp_dot_error_bound_firewall_lean_from_parsed(&reassoc, &defined, &f64_formats())
            .is_none()
    );
}

#[test]
fn emits_bool_tautology_firewall_from_parsed() {
    use ay_frontend::command::Term as PTerm;
    // (not (= (not (not p)) p)) — double-negation, a propositional contradiction.
    let p = || PTerm::Symbol("p".to_string());
    let nnp = PTerm::App(
        "not".to_string(),
        vec![PTerm::App("not".to_string(), vec![p()])],
    );
    let parsed = vec![PTerm::App(
        "not".to_string(),
        vec![PTerm::App("=".to_string(), vec![nnp, p()])],
    )];
    let lean = emit_bool_tautology_firewall_lean_from_parsed(&parsed)
        .expect("propositional contradiction should emit");
    // The emitted Lean lake-builds with axioms ⊆ {propext, Quot.sound} (verified
    // out-of-band, like the other firewall emitters); here assert its structure.
    assert!(lean.contains("abbrev Val := Bool"));
    assert!(lean.contains("((!(!m)) == m)"));
    assert!(lean.contains("firewall_combined_unsat"));
    assert!(lean.contains("revert m\n  decide"));
}

// ----------------------------------------------------------------------------
// General whole-DAG firewall emitter (`emit_general_firewall_lean`).
// ----------------------------------------------------------------------------

use ay_core::{Proof, ProofId, ProofStep, TheoryLemmaKind};

/// Build a `<=` literal `(<= a b)`.
fn le(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    cmp(terms, "<=", a, b)
}

#[test]
fn general_grounds_multiclause_lia_transitivity() {
    // x ≤ y, y ≤ z, ¬(x ≤ z) refuted by the ≤-transitivity lemma — a genuine
    // multi-clause, whole-DAG proof (3 Assume inputs + 1 theory lemma + a
    // resolution step to the empty clause).
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let le_xy = le(&mut terms, x, y);
    let le_yz = le(&mut terms, y, z);
    let le_xz = le(&mut terms, x, z);
    let not_le_xz = terms.mk_not(le_xz);
    let not_le_xy = terms.mk_not(le_xy);
    let not_le_yz = terms.mk_not(le_yz);

    let proof = Proof::from_steps(vec![
        ProofStep::Assume(le_xy),
        ProofStep::Assume(le_yz),
        ProofStep::Assume(not_le_xz),
        ProofStep::TheoryLemma {
            theory: "LIA".to_string(),
            clause: vec![not_le_xy, not_le_yz, le_xz],
            farkas: None,
            kind: TheoryLemmaKind::LiaGeneric,
            lia: None,
        },
        ProofStep::Resolution {
            clause: vec![],
            pivot: le_xz,
            clause1: ProofId(0),
            clause2: ProofId(0),
        },
    ]);

    let lean = emit_general_firewall_lean(&terms, &proof)
        .expect("multi-clause LIA transitivity should emit a general firewall cert");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");

    for needle in [
        "import AySoundness.Firewall",
        "abbrev Val := Nat → Int",
        "(m 0) ≤ (m 1)",
        "(m 1) ≤ (m 2)",
        "(m 0) ≤ (m 2)",
        "def original : List (Cid × Clause) := [(1, [1]), (2, [2]), (3, [-3])]",
        "def lemmas   : List (Cid × Clause) := [(4, [-1, -2, 3])]",
        "def proof    : List (Cid × Clause × List Int) := [(5, [], [1, 2, 3, 4])]",
        "theorem lemma_4_valid (m : Val)",
        "omega",
        "firewall_combined_unsat",
        "theorem no_model",
    ] {
        assert!(lean.contains(needle), "general LIA cert missing: {needle}");
    }
}

#[test]
fn general_shares_atom_id_across_two_lemmas() {
    // a ≤ b, b ≤ c, c ≤ d, ¬(a ≤ d) refuted via TWO chained transitivity lemmas
    // that SHARE the intermediate atom `a ≤ c` — exercising the global atom
    // table (one Nat id reused across both lemma clauses).
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);
    let le_ab = le(&mut terms, a, b);
    let le_bc = le(&mut terms, b, c);
    let le_cd = le(&mut terms, c, d);
    let le_ad = le(&mut terms, a, d);
    let le_ac = le(&mut terms, a, c);
    let n_ab = terms.mk_not(le_ab);
    let n_bc = terms.mk_not(le_bc);
    let n_cd = terms.mk_not(le_cd);
    let n_ad = terms.mk_not(le_ad);
    let n_ac = terms.mk_not(le_ac);

    let proof = Proof::from_steps(vec![
        ProofStep::Assume(le_ab),
        ProofStep::Assume(le_bc),
        ProofStep::Assume(le_cd),
        ProofStep::Assume(n_ad),
        // lemma 1: ¬(a≤b) ∨ ¬(b≤c) ∨ (a≤c)  — introduces atom a≤c.
        ProofStep::TheoryLemma {
            theory: "LIA".to_string(),
            clause: vec![n_ab, n_bc, le_ac],
            farkas: None,
            kind: TheoryLemmaKind::LiaGeneric,
            lia: None,
        },
        // lemma 2: ¬(a≤c) ∨ ¬(c≤d) ∨ (a≤d)  — reuses atom a≤c.
        ProofStep::TheoryLemma {
            theory: "LIA".to_string(),
            clause: vec![n_ac, n_cd, le_ad],
            farkas: None,
            kind: TheoryLemmaKind::LiaGeneric,
            lia: None,
        },
        ProofStep::Resolution {
            clause: vec![],
            pivot: le_ad,
            clause1: ProofId(0),
            clause2: ProofId(0),
        },
    ]);

    let lean = emit_general_firewall_lean(&terms, &proof)
        .expect("two-lemma chained transitivity should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");

    // atoms: 1=a≤b, 2=b≤c, 3=c≤d, 4=a≤d, 5=a≤c (a≤c first seen in lemma 1).
    assert!(
        lean.contains("def lemmas   : List (Cid × Clause) := [(5, [-1, -2, 5]), (6, [-5, -3, 4])]")
    );
    assert!(lean.contains("theorem lemma_5_valid (m : Val)"));
    assert!(lean.contains("theorem lemma_6_valid (m : Val)"));
    // Two-way membership split.
    assert!(lean.contains("rcases hcl with h | h <;> subst h"));
    assert!(lean.contains("· exact lemma_5_valid m"));
    assert!(lean.contains("· exact lemma_6_valid m"));
    // Shared atom 5 (a≤c) rendered once, referenced by both lemmas.
    assert!(lean.contains("(m 0) ≤ (m 2)"));
}

#[test]
fn general_grounds_function_congruence() {
    // a = b, ¬(f a = f b) refuted by the EUF congruence lemma — switches to the
    // AUGMENTED model `(Nat → Int) × (Int → Int)` (m.1 = scalar valuation, m.2 =
    // the single unary function f); congruence lemma discharged by by_cases on
    // the argument equality + simp (no omega).
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let fa = terms.mk_app(Symbol::named("f"), vec![a], Sort::Int);
    let fb = terms.mk_app(Symbol::named("f"), vec![b], Sort::Int);
    let eq_ab = eq(&mut terms, a, b);
    let eq_fab = eq(&mut terms, fa, fb);
    let n_ab = terms.mk_not(eq_ab);
    let n_fab = terms.mk_not(eq_fab);

    let proof = Proof::from_steps(vec![
        ProofStep::Assume(eq_ab),
        ProofStep::Assume(n_fab),
        ProofStep::TheoryLemma {
            theory: "EUF".to_string(),
            clause: vec![n_ab, eq_fab],
            farkas: None,
            kind: TheoryLemmaKind::EufCongruent,
            lia: None,
        },
        ProofStep::Resolution {
            clause: vec![],
            pivot: eq_fab,
            clause1: ProofId(0),
            clause2: ProofId(0),
        },
    ]);

    let lean = emit_general_firewall_lean(&terms, &proof)
        .expect("congruence proof should emit (augmented model)");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("abbrev Val := (Nat → Int) × (Nat → Int → Int)"));
    assert!(lean.contains("(m.1 0) = (m.1 1)")); // argument equality atom
    assert!(lean.contains("((m.2 0) (m.1 0)) = ((m.2 0) (m.1 1))")); // congruence conclusion (fn family idx 0)
                                                                     // congruence lemma: by_cases on the arg-eq + simp, NO omega.
    assert!(lean.contains("by_cases h1 : (m.1 0) = (m.1 1) <;> simp [h1]"));
    assert!(!lean.contains("simp [h1] <;> omega"));
}

#[test]
fn general_grounds_full_combined_example() {
    // The genuine mixed EUF+LIA conflict `a ≤ b ∧ b ≤ a ∧ f a ≠ f b` — the
    // CombinedExample, now emitted by the general driver from a whole proof DAG:
    // an LIA antisymmetry lemma (a≤b ∧ b≤a → a=b, by omega) and an EUF congruence
    // lemma (a=b → f a = f b, by simp), connected by the SHARED interface atom
    // `a = b`. Both theories load-bearing; one shared augmented model.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let fa = terms.mk_app(Symbol::named("f"), vec![a], Sort::Int);
    let fb = terms.mk_app(Symbol::named("f"), vec![b], Sort::Int);
    let le_ab = le(&mut terms, a, b);
    let le_ba = le(&mut terms, b, a);
    let eq_ab = eq(&mut terms, a, b);
    let eq_fab = eq(&mut terms, fa, fb);
    let n_le_ab = terms.mk_not(le_ab);
    let n_le_ba = terms.mk_not(le_ba);
    let n_ab = terms.mk_not(eq_ab);
    let n_fab = terms.mk_not(eq_fab);

    let proof = Proof::from_steps(vec![
        ProofStep::Assume(le_ab),
        ProofStep::Assume(le_ba),
        ProofStep::Assume(n_fab),
        // LIA antisymmetry: ¬(a≤b) ∨ ¬(b≤a) ∨ (a=b)
        ProofStep::TheoryLemma {
            theory: "LIA".to_string(),
            clause: vec![n_le_ab, n_le_ba, eq_ab],
            farkas: None,
            kind: TheoryLemmaKind::LiaGeneric,
            lia: None,
        },
        // EUF congruence: ¬(a=b) ∨ (f a = f b)
        ProofStep::TheoryLemma {
            theory: "EUF".to_string(),
            clause: vec![n_ab, eq_fab],
            farkas: None,
            kind: TheoryLemmaKind::EufCongruent,
            lia: None,
        },
        ProofStep::Resolution {
            clause: vec![],
            pivot: eq_fab,
            clause1: ProofId(0),
            clause2: ProofId(0),
        },
    ]);

    let lean = emit_general_firewall_lean(&terms, &proof)
        .expect("full combined EUF+LIA example should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("abbrev Val := (Nat → Int) × (Nat → Int → Int)"));
    // atoms: 1=a≤b, 2=b≤a, 3=f a=f b, 4=a=b (a=b first seen in the LIA lemma).
    assert!(lean.contains("((m.2 0) (m.1 0)) = ((m.2 0) (m.1 1))"));
    // LIA lemma uses omega; congruence lemma uses simp (no omega).
    assert!(lean.contains("<;> omega"));
    assert!(lean.contains("· exact lemma_4_valid m"));
    assert!(lean.contains("· exact lemma_5_valid m"));
}

#[test]
fn general_grounds_predicate_congruence() {
    // a = b, P a, ¬(P b) refuted by the EUF predicate-congruence lemma — switches
    // to the AUGMENTED predicate model `(Nat → Int) × (Int → Bool)` (m.1 = scalar
    // valuation, m.2 = the single unary predicate P). Predicate atoms render as
    // raw `Bool` (no `decide`); lemma discharged by by_cases on the argument
    // equality + simp (no omega).
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let eq_ab = eq(&mut terms, a, b);
    let pa = terms.mk_app(Symbol::named("P"), vec![a], Sort::Bool);
    let pb = terms.mk_app(Symbol::named("P"), vec![b], Sort::Bool);
    let n_ab = terms.mk_not(eq_ab);
    let n_pa = terms.mk_not(pa);
    let n_pb = terms.mk_not(pb);

    let proof = Proof::from_steps(vec![
        ProofStep::Assume(eq_ab),
        ProofStep::Assume(pa),
        ProofStep::Assume(n_pb),
        ProofStep::TheoryLemma {
            theory: "EUF".to_string(),
            clause: vec![n_ab, n_pa, pb],
            farkas: None,
            kind: TheoryLemmaKind::EufCongruentPred,
            lia: None,
        },
        ProofStep::Resolution {
            clause: vec![],
            pivot: pb,
            clause1: ProofId(0),
            clause2: ProofId(0),
        },
    ]);

    let lean = emit_general_firewall_lean(&terms, &proof)
        .expect("predicate-congruence proof should emit (augmented predicate model)");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("abbrev Val := (Nat → Int) × (Nat → Int → Bool)"));
    assert!(lean.contains("(m.1 0) = (m.1 1)")); // argument equality atom (decide)
                                                 // predicate atoms render as raw Bool (no `decide` wrapper), pred family idx 0.
    assert!(lean.contains("=> ((m.2 0) (m.1 0))"));
    assert!(lean.contains("=> ((m.2 0) (m.1 1))"));
    assert!(!lean.contains("decide ((m.2"));
    // congruence lemma: by_cases on the arg-eq + simp, NO omega.
    assert!(lean.contains("by_cases h1 : (m.1 0) = (m.1 1) <;> simp [h1]"));
    assert!(!lean.contains("simp [h1] <;> omega"));
}

#[test]
fn general_grounds_two_function_congruence() {
    // a = b ∧ f a = g a ∧ ¬(f b = g b) — UNSAT needing f-congruence, g-congruence,
    // and equality transitivity over the (Int) function RESULTS. Exercises the
    // function FAMILY model `(Nat → Int) × (Nat → Int → Int)`: f = index 0,
    // g = index 1. The transitivity lemma (all function-result equalities) uses
    // omega; the two congruence lemmas use simp.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let fa = terms.mk_app(Symbol::named("f"), vec![a], Sort::Int);
    let fb = terms.mk_app(Symbol::named("f"), vec![b], Sort::Int);
    let ga = terms.mk_app(Symbol::named("g"), vec![a], Sort::Int);
    let gb = terms.mk_app(Symbol::named("g"), vec![b], Sort::Int);
    let eq_ab = eq(&mut terms, a, b);
    let eq_faga = eq(&mut terms, fa, ga);
    let eq_fbgb = eq(&mut terms, fb, gb);
    let eq_fafb = eq(&mut terms, fa, fb);
    let eq_gagb = eq(&mut terms, ga, gb);
    let n_ab = terms.mk_not(eq_ab);
    let n_fbgb = terms.mk_not(eq_fbgb);
    let n_fafb = terms.mk_not(eq_fafb);
    let n_gagb = terms.mk_not(eq_gagb);
    let n_faga = terms.mk_not(eq_faga);

    let proof = Proof::from_steps(vec![
        ProofStep::Assume(eq_ab),
        ProofStep::Assume(eq_faga),
        ProofStep::Assume(n_fbgb),
        // L1 f-congruence: ¬(a=b) ∨ (f a = f b)
        ProofStep::TheoryLemma {
            theory: "EUF".to_string(),
            clause: vec![n_ab, eq_fafb],
            farkas: None,
            kind: TheoryLemmaKind::EufCongruent,
            lia: None,
        },
        // L2 g-congruence: ¬(a=b) ∨ (g a = g b)
        ProofStep::TheoryLemma {
            theory: "EUF".to_string(),
            clause: vec![n_ab, eq_gagb],
            farkas: None,
            kind: TheoryLemmaKind::EufCongruent,
            lia: None,
        },
        // L3 transitivity: ¬(f a=f b) ∨ ¬(g a=g b) ∨ ¬(f a=g a) ∨ (f b=g b)
        ProofStep::TheoryLemma {
            theory: "EUF".to_string(),
            clause: vec![n_fafb, n_gagb, n_faga, eq_fbgb],
            farkas: None,
            kind: TheoryLemmaKind::EufTransitive,
            lia: None,
        },
        ProofStep::Resolution {
            clause: vec![],
            pivot: eq_fbgb,
            clause1: ProofId(0),
            clause2: ProofId(0),
        },
    ]);

    let lean = emit_general_firewall_lean(&terms, &proof)
        .expect("two-function conflict should emit (function family model)");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("abbrev Val := (Nat → Int) × (Nat → Int → Int)"));
    assert!(lean.contains("(m.2 0)")); // f = family index 0
    assert!(lean.contains("(m.2 1)")); // g = family index 1
                                       // the transitivity lemma (all function-result equalities) uses omega.
    assert!(lean.contains("<;> simp [h2, h3, h4, h5] <;> omega") || lean.contains("<;> omega"));
}

#[test]
fn general_grounds_function_predicate_mix() {
    // a = b ∧ P(f a) ∧ ¬P(f b) — UNSAT via f-congruence then P-congruence over the
    // function-application argument. Exercises the MIXED model
    // `(Nat → Int) × (Nat → Int → Int) × (Nat → Int → Bool)`, including a predicate
    // over a function application `P(f a)`.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let fa = terms.mk_app(Symbol::named("f"), vec![a], Sort::Int);
    let fb = terms.mk_app(Symbol::named("f"), vec![b], Sort::Int);
    let pfa = terms.mk_app(Symbol::named("P"), vec![fa], Sort::Bool);
    let pfb = terms.mk_app(Symbol::named("P"), vec![fb], Sort::Bool);
    let eq_ab = eq(&mut terms, a, b);
    let eq_fafb = eq(&mut terms, fa, fb);
    let n_ab = terms.mk_not(eq_ab);
    let n_fafb = terms.mk_not(eq_fafb);
    let n_pfa = terms.mk_not(pfa);
    let n_pfb = terms.mk_not(pfb);

    let proof = Proof::from_steps(vec![
        ProofStep::Assume(eq_ab),
        ProofStep::Assume(pfa),
        ProofStep::Assume(n_pfb),
        // Lf f-congruence: ¬(a=b) ∨ (f a = f b)
        ProofStep::TheoryLemma {
            theory: "EUF".to_string(),
            clause: vec![n_ab, eq_fafb],
            farkas: None,
            kind: TheoryLemmaKind::EufCongruent,
            lia: None,
        },
        // Lp P-congruence over the fn-app argument: ¬(f a = f b) ∨ ¬P(f a) ∨ P(f b)
        ProofStep::TheoryLemma {
            theory: "EUF".to_string(),
            clause: vec![n_fafb, n_pfa, pfb],
            farkas: None,
            kind: TheoryLemmaKind::EufCongruentPred,
            lia: None,
        },
        ProofStep::Resolution {
            clause: vec![],
            pivot: pfb,
            clause1: ProofId(0),
            clause2: ProofId(0),
        },
    ]);

    let lean = emit_general_firewall_lean(&terms, &proof)
        .expect("function+predicate mix should emit (mixed family model)");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("abbrev Val := (Nat → Int) × (Nat → Int → Int) × (Nat → Int → Bool)"));
    // predicate over a function application: P(f a) = (m.2.2 0) ((m.2.1 0) (m.1 0)).
    assert!(lean.contains("(m.2.2 0) ((m.2.1 0) (m.1 0))"));
    // the predicate-congruence lemma by_cases on the fn-app argument equality, simp.
    assert!(lean.contains("((m.2.1 0) (m.1 0)) = ((m.2.1 0) (m.1 1)) <;> simp"));
}

#[test]
fn general_declines_unsupported_kind() {
    // An array-extensionality lemma is outside the renderable set — decline.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let eq_ab = eq(&mut terms, a, b);
    let n_ab = terms.mk_not(eq_ab);

    let proof = Proof::from_steps(vec![
        ProofStep::Assume(eq_ab),
        ProofStep::Assume(n_ab),
        ProofStep::TheoryLemma {
            theory: "ARRAY".to_string(),
            clause: vec![n_ab, eq_ab],
            farkas: None,
            kind: TheoryLemmaKind::ArrayExtensionality,
            lia: None,
        },
        ProofStep::Resolution {
            clause: vec![],
            pivot: eq_ab,
            clause1: ProofId(0),
            clause2: ProofId(0),
        },
    ]);

    assert!(
        emit_general_firewall_lean(&terms, &proof).is_none(),
        "unsupported lemma kind (array extensionality) must decline"
    );
}

#[test]
fn general_declines_without_empty_clause() {
    // No terminal empty clause ⇒ not a refutation ⇒ decline.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let le_xy = le(&mut terms, x, y);
    let le_yx = le(&mut terms, y, x);
    let n_xy = terms.mk_not(le_xy);
    let n_yx = terms.mk_not(le_yx);
    let eq_xy = cmp(&mut terms, "=", x, y);
    let proof = Proof::from_steps(vec![
        ProofStep::Assume(le_xy),
        ProofStep::Assume(le_yx),
        ProofStep::TheoryLemma {
            theory: "LIA".to_string(),
            clause: vec![n_xy, n_yx, eq_xy],
            farkas: None,
            kind: TheoryLemmaKind::LiaGeneric,
            lia: None,
        },
        // No empty clause.
    ]);
    assert!(emit_general_firewall_lean(&terms, &proof).is_none());
}

// ==== APPENDED TESTS: word_equations ====
#[test]
fn emits_str_word_eq_len_from_parsed_assertions() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let strlit = |s: &str| PTerm::Const(PConst::String(s.to_string()));
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let concat = |xs: Vec<PTerm>| PTerm::App("str.++".to_string(), xs);
    let eq = |a: PTerm, b: PTerm| PTerm::App("=".to_string(), vec![a, b]);
    let str_len_eq = |v: &str, k: &str| {
        eq(
            PTerm::App("str.len".to_string(), vec![sym(v)]),
            PTerm::Const(PConst::Numeral(k.to_string())),
        )
    };

    // POSITIVE (we02): (= (str.++ x x) "aba") → 2·len x = 3, ℕ-infeasible.
    let we02 = vec![eq(concat(vec![sym("x"), sym("x")]), strlit("aba"))];
    let lean = emit_str_word_eq_len_firewall_lean_from_parsed(&we02)
        .expect("we02 parity word-equation length conflict should emit");
    assert!(lean.contains("import AySoundness.StringThy"));
    assert!(lean.contains("StringThy.len_cat"));
    assert!(lean.contains("firewall_combined_unsat"));
    assert!(lean.contains("abbrev Val := StringThy.Str"));
    assert!(lean.contains("StringThy.cat m m"));

    // POSITIVE (we08): x·"ab" = "a"·y ∧ |x|=1 ∧ |y|=1 → 1+2 = 1+1, infeasible.
    let we08 = vec![
        eq(
            concat(vec![sym("x"), strlit("ab")]),
            concat(vec![strlit("a"), sym("y")]),
        ),
        str_len_eq("x", "1"),
        str_len_eq("y", "1"),
    ];
    let lean08 = emit_str_word_eq_len_firewall_lean_from_parsed(&we08)
        .expect("we08 length-pin word-equation conflict should emit");
    assert!(lean08.contains("StringThy.Str × StringThy.Str"));
    assert!(lean08.contains("firewall_combined_unsat"));

    // POSITIVE (we11): (= (str.++ x x x) "ab") → 3·len x = 2, ℕ-infeasible.
    let we11 = vec![eq(concat(vec![sym("x"), sym("x"), sym("x")]), strlit("ab"))];
    assert!(emit_str_word_eq_len_firewall_lean_from_parsed(&we11).is_some());

    // NEGATIVE (we03-shape): "a"·x = x·"b" — equal lengths (1+len x each), the
    // length projection is SATISFIABLE, so decline (needs positional reasoning,
    // not a length conflict).
    let we03 = vec![eq(
        concat(vec![strlit("a"), sym("x")]),
        concat(vec![sym("x"), strlit("b")]),
    )];
    assert!(emit_str_word_eq_len_firewall_lean_from_parsed(&we03).is_none());

    // NEGATIVE (we01-shape): (= (str.++ x y) "aba") — two FREE variable lengths,
    // length system is satisfiable, decline.
    let we01 = vec![eq(concat(vec![sym("x"), sym("y")]), strlit("aba"))];
    assert!(emit_str_word_eq_len_firewall_lean_from_parsed(&we01).is_none());
}

// ==== APPENDED TESTS: sets_setlia ====
/// Build `(set.singleton n)`.
#[cfg(test)]
fn set_singleton_pterm(n: i64) -> ay_frontend::command::Term {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    PTerm::App(
        "set.singleton".to_string(),
        vec![PTerm::Const(PConst::Numeral(n.to_string()))],
    )
}

/// Build `(set.insert n s)`.
#[cfg(test)]
fn set_insert_pterm(n: i64, s: ay_frontend::command::Term) -> ay_frontend::command::Term {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    PTerm::App(
        "set.insert".to_string(),
        vec![PTerm::Const(PConst::Numeral(n.to_string())), s],
    )
}

#[test]
fn emits_set_subset_structural_from_parsed() {
    use ay_frontend::command::Term as PTerm;
    // (not (set.subset {1} {0,1})) -- subset HOLDS, negation UNSAT.
    let subset = PTerm::App(
        "set.subset".to_string(),
        vec![
            set_singleton_pterm(1),
            set_insert_pterm(0, set_singleton_pterm(1)),
        ],
    );
    let parsed = vec![PTerm::App("not".to_string(), vec![subset])];
    let lean = emit_set_subset_structural_firewall_lean_from_parsed(&parsed)
        .expect("negated-valid-subset conflict should emit");
    assert!(lean.contains("firewall_combined_unsat"));
    assert!(
        lean.contains("SetThy.subset (SetThy.singleton 1) (SetThy.insert 0 (SetThy.singleton 1))")
    );
    assert!(lean.contains("[(1, [-1])]"));
}

#[test]
fn set_subset_structural_declines_when_subset_fails() {
    use ay_frontend::command::Term as PTerm;
    // (not (set.subset {0} {1})) -- subset FAILS, negation SAT; decline.
    let subset = PTerm::App(
        "set.subset".to_string(),
        vec![set_singleton_pterm(0), set_singleton_pterm(1)],
    );
    let parsed = vec![PTerm::App("not".to_string(), vec![subset])];
    assert!(emit_set_subset_structural_firewall_lean_from_parsed(&parsed).is_none());
}

#[test]
fn set_subset_structural_declines_non_structural() {
    use ay_frontend::command::Term as PTerm;
    let subset = PTerm::App(
        "set.subset".to_string(),
        vec![
            PTerm::Symbol("s".to_string()),
            PTerm::Symbol("t".to_string()),
        ],
    );
    let parsed = vec![PTerm::App("not".to_string(), vec![subset])];
    assert!(emit_set_subset_structural_firewall_lean_from_parsed(&parsed).is_none());
}

#[test]
fn emits_set_eq_structural_from_parsed() {
    use ay_frontend::command::Term as PTerm;
    // (= {0} {1}) -- not equal, UNSAT.
    let parsed = vec![PTerm::App(
        "=".to_string(),
        vec![set_singleton_pterm(0), set_singleton_pterm(1)],
    )];
    let lean = emit_set_eq_structural_firewall_lean_from_parsed(&parsed)
        .expect("false set-equality conflict should emit");
    assert!(lean.contains("firewall_combined_unsat"));
    assert!(lean.contains("SetThy.seteq (SetThy.singleton 0) (SetThy.singleton 1)"));
    assert!(lean.contains("[(1, [1])]"));
}

#[test]
fn set_eq_structural_declines_when_equal() {
    use ay_frontend::command::Term as PTerm;
    // (= {0,1} {0,1}) -- equal, SAT; decline.
    let parsed = vec![PTerm::App(
        "=".to_string(),
        vec![
            set_insert_pterm(0, set_singleton_pterm(1)),
            set_insert_pterm(1, set_singleton_pterm(0)),
        ],
    )];
    assert!(emit_set_eq_structural_firewall_lean_from_parsed(&parsed).is_none());
}

#[test]
fn set_eq_structural_declines_non_structural() {
    use ay_frontend::command::Term as PTerm;
    let parsed = vec![PTerm::App(
        "=".to_string(),
        vec![PTerm::Symbol("s".to_string()), set_singleton_pterm(1)],
    )];
    assert!(emit_set_eq_structural_firewall_lean_from_parsed(&parsed).is_none());
}

#[test]
fn emits_set_subset_structural_false_from_parsed() {
    use ay_frontend::command::Term as PTerm;
    // (set.subset {0} {1}) -- subset FAILS, positive assertion UNSAT.
    let parsed = vec![PTerm::App(
        "set.subset".to_string(),
        vec![set_singleton_pterm(0), set_singleton_pterm(1)],
    )];
    let lean = emit_set_subset_structural_false_firewall_lean_from_parsed(&parsed)
        .expect("false-subset conflict should emit");
    assert!(lean.contains("firewall_combined_unsat"));
    assert!(lean.contains("SetThy.subset (SetThy.singleton 0) (SetThy.singleton 1)"));
    assert!(lean.contains("[(1, [1])]"));
}

#[test]
fn set_subset_structural_false_declines_when_subset_holds() {
    use ay_frontend::command::Term as PTerm;
    // (set.subset {1} {0,1}) -- subset HOLDS, positive assertion SAT; decline.
    let parsed = vec![PTerm::App(
        "set.subset".to_string(),
        vec![
            set_singleton_pterm(1),
            set_insert_pterm(0, set_singleton_pterm(1)),
        ],
    )];
    assert!(emit_set_subset_structural_false_firewall_lean_from_parsed(&parsed).is_none());
}

// ==== APPENDED TESTS: arrays_alia ====
#[test]
fn emits_array_row_mismatch_from_parsed() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    // (= (select (store a i 5) i) 10) — ROW-same yields 5, asserted 10 → UNSAT.
    let store = PTerm::App(
        "store".to_string(),
        vec![
            PTerm::Symbol("a".to_string()),
            PTerm::Symbol("i".to_string()),
            num("5"),
        ],
    );
    let sel = PTerm::App(
        "select".to_string(),
        vec![store, PTerm::Symbol("i".to_string())],
    );
    let eqn = PTerm::App("=".to_string(), vec![sel, num("10")]);
    let parsed = vec![eqn];

    let lean = emit_array_row_mismatch_firewall_lean_from_parsed(&parsed)
        .expect("ROW-same positive mismatch should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("abbrev Val := (Nat → Nat) × (Nat → Nat)"));
    assert!(lean.contains("if (m.2 0) = (m.2 0) then (5 : Nat) else"));
    assert!(lean.contains("= (10 : Nat)"));
    assert!(lean.contains("firewall_combined_unsat"));

    // Arith-normalized read index (+ i 0) ≡ i — still a mismatch.
    let store2 = PTerm::App(
        "store".to_string(),
        vec![
            PTerm::Symbol("a".to_string()),
            PTerm::Symbol("i".to_string()),
            num("42"),
        ],
    );
    let ridx = PTerm::App(
        "+".to_string(),
        vec![PTerm::Symbol("i".to_string()), num("0")],
    );
    let sel2 = PTerm::App("select".to_string(), vec![store2, ridx]);
    let eqn2 = PTerm::App("=".to_string(), vec![sel2, num("43")]);
    assert!(emit_array_row_mismatch_firewall_lean_from_parsed(&[eqn2]).is_some());
}

#[test]
fn array_row_mismatch_declines_matching_value() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    // (= (select (store a i 5) i) 5) — read yields 5, asserted 5: SAT, must decline.
    let store = PTerm::App(
        "store".to_string(),
        vec![
            PTerm::Symbol("a".to_string()),
            PTerm::Symbol("i".to_string()),
            num("5"),
        ],
    );
    let sel = PTerm::App(
        "select".to_string(),
        vec![store, PTerm::Symbol("i".to_string())],
    );
    let eqn = PTerm::App("=".to_string(), vec![sel, num("5")]);
    assert!(emit_array_row_mismatch_firewall_lean_from_parsed(&[eqn]).is_none());

    // Different (non-normalizing) read index j ≠ i: not ROW-same → decline.
    let store2 = PTerm::App(
        "store".to_string(),
        vec![
            PTerm::Symbol("a".to_string()),
            PTerm::Symbol("i".to_string()),
            num("5"),
        ],
    );
    let sel2 = PTerm::App(
        "select".to_string(),
        vec![store2, PTerm::Symbol("j".to_string())],
    );
    let eqn2 = PTerm::App("=".to_string(), vec![sel2, num("10")]);
    assert!(emit_array_row_mismatch_firewall_lean_from_parsed(&[eqn2]).is_none());
}

#[test]
fn emits_array_inlined_nested_store_swap_from_parsed() {
    use ay_frontend::command::Term as PTerm;
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let store = |a: PTerm, i: PTerm, v: PTerm| PTerm::App("store".to_string(), vec![a, i, v]);
    let select = |a: PTerm, i: PTerm| PTerm::App("select".to_string(), vec![a, i]);
    // (not (= i j)), (= b (store (store a i (select a j)) j (select a i))),
    // (not (= (select b i) (select a j))). After swap b[i] = a[j], so UNSAT.
    let diseq = PTerm::App(
        "not".to_string(),
        vec![PTerm::App("=".to_string(), vec![sym("i"), sym("j")])],
    );
    let swap = store(
        store(sym("a"), sym("i"), select(sym("a"), sym("j"))),
        sym("j"),
        select(sym("a"), sym("i")),
    );
    let bdef = PTerm::App("=".to_string(), vec![sym("b"), swap]);
    let target = PTerm::App(
        "not".to_string(),
        vec![PTerm::App(
            "=".to_string(),
            vec![select(sym("b"), sym("i")), select(sym("a"), sym("j"))],
        )],
    );
    let parsed = vec![diseq.clone(), bdef, target.clone()];

    let lean = emit_array_inlined_nested_store_firewall_lean_from_parsed(&parsed)
        .expect("array-let swap conflict should emit after inlining");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("abbrev Val := (Nat → Nat) × (Nat → Nat)"));
    assert!(lean.contains("firewall_combined_unsat"));

    // Declines when there is no array-let to inline (nothing this wrapper adds).
    assert!(emit_array_inlined_nested_store_firewall_lean_from_parsed(&[diseq, target]).is_none());
}

// ==== APPENDED TESTS: array unconditional / define-fun expansion ====

// store_idempotent: `select (store (store a i v) i v) j = select (store a i v) j`
// holds for ALL j with NO guarding disequality — the two if-trees agree on both
// the `j = i` and `j ≠ i` branches. The relaxed nested emitter grounds the
// UNCONDITIONAL `row_eq` lemma (non-empty but unbacked guard `j = i`).
#[test]
fn emits_array_store_idempotent_unconditional_from_parsed() {
    use ay_frontend::command::Term as PTerm;
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let store = |a: PTerm, i: PTerm, v: PTerm| PTerm::App("store".to_string(), vec![a, i, v]);
    let select = |a: PTerm, i: PTerm| PTerm::App("select".to_string(), vec![a, i]);

    let lhs = select(
        store(store(sym("a"), sym("i"), sym("v")), sym("i"), sym("v")),
        sym("j"),
    );
    let rhs = select(store(sym("a"), sym("i"), sym("v")), sym("j"));
    let main = PTerm::App(
        "not".to_string(),
        vec![PTerm::App("=".to_string(), vec![lhs, rhs])],
    );

    let lean = emit_array_nested_store_row_firewall_lean_from_parsed(&[main])
        .expect("store-idempotence identity should emit unconditionally");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("namespace AySoundness.Emitted.ArrUncond_"));
    // The unconditional lemma clause is the bare row_eq `[1]`, no guard atoms.
    assert!(lean.contains("def lemmas   : List (Cid × Clause) := [(2, [1])]"));
    // The single non-reflexive `if`-condition `j = i` is discharged by by_cases.
    assert!(lean.contains("by_cases h2 : (m.2 0) = (m.2 1)"));
    assert!(lean.contains("firewall_combined_unsat"));
}

// store_eq_transitivity / array_bv_store, in their inlined form: after the
// array-let `b = store a i e` is substituted, `select b i = e` collapses to a
// reflexive single-store ROW1 with an EMPTY guard. The unconditional emitter
// grounds it with a plain `simp` (no by_cases).
#[test]
fn emits_array_reflexive_row1_empty_guard_from_parsed() {
    use ay_frontend::command::Term as PTerm;
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let store = |a: PTerm, i: PTerm, v: PTerm| PTerm::App("store".to_string(), vec![a, i, v]);
    let select = |a: PTerm, i: PTerm| PTerm::App("select".to_string(), vec![a, i]);

    // b = store a i e ; not (= (select b i) e)  — the store_eq_transitivity shape.
    let bdef = PTerm::App(
        "=".to_string(),
        vec![sym("b"), store(sym("a"), sym("i"), sym("e"))],
    );
    let target = PTerm::App(
        "not".to_string(),
        vec![PTerm::App(
            "=".to_string(),
            vec![select(sym("b"), sym("i")), sym("e")],
        )],
    );
    let parsed = vec![bdef, target];

    let lean = emit_array_inlined_nested_store_firewall_lean_from_parsed(&parsed)
        .expect("reflexive ROW1 behind an array-let should emit after inlining");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    // Either the unconditional (empty-guard) grounding or the plain ROW1 grounding
    // is a sound certificate; both share the firewall attribution.
    assert!(
        lean.contains("namespace AySoundness.Emitted.ArrUncond_")
            || lean.contains("namespace AySoundness.Emitted.ArrRow1_")
    );
    assert!(lean.contains("firewall_combined_unsat"));
}

// storecomm_t1_np_sf_ai_00003, in its macro-expanded form: `fwd`/`rev` are nullary
// define-funs whose bodies are opposite-order 3-store chains, `(distinct i0 i1 i2)`
// backs the pairwise index inequalities, and `select fwd i0`/`select rev i0` both
// reduce to `e0`. Substituting the macro bodies exposes the guarded nested ROW
// conflict, and the `distinct` expansion backs every guard.
#[test]
fn emits_array_storecomm_defexpanded_from_parsed() {
    use ay_frontend::command::Term as PTerm;
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let store = |a: PTerm, i: PTerm, v: PTerm| PTerm::App("store".to_string(), vec![a, i, v]);
    let select = |a: PTerm, i: PTerm| PTerm::App("select".to_string(), vec![a, i]);

    let distinct = PTerm::App(
        "distinct".to_string(),
        vec![sym("i0"), sym("i1"), sym("i2")],
    );
    let target = PTerm::App(
        "not".to_string(),
        vec![PTerm::App(
            "=".to_string(),
            vec![select(sym("fwd"), sym("i0")), select(sym("rev"), sym("i0"))],
        )],
    );
    let parsed = vec![distinct, target];

    // fwd = store(store(store a0 i0 e0) i1 e1) i2 e2 ; rev = reverse order.
    let fwd = store(
        store(store(sym("a0"), sym("i0"), sym("e0")), sym("i1"), sym("e1")),
        sym("i2"),
        sym("e2"),
    );
    let rev = store(
        store(store(sym("a0"), sym("i2"), sym("e2")), sym("i1"), sym("e1")),
        sym("i0"),
        sym("e0"),
    );
    let defs = vec![("fwd".to_string(), fwd), ("rev".to_string(), rev)];

    let lean = emit_array_defexpanded_firewall_lean_from_parsed(&parsed, &defs)
        .expect("macro store-commute conflict should emit after define-fun expansion");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("abbrev Val := (Nat → Nat) × (Nat → Nat)"));
    assert!(lean.contains("firewall_combined_unsat"));
    // Guarded nested emitter: the pairwise index coincidences (expanded from the
    // `distinct`) appear as by_cases guards.
    assert!(lean.contains("by_cases"));

    // Declines when no macro expands (empty defs — nothing to substitute).
    assert!(emit_array_defexpanded_firewall_lean_from_parsed(&parsed, &[]).is_none());
    // Declines when the `distinct` is absent: the guards are then unbacked and the
    // conflict is not unconditionally valid (opposite-order writes at genuinely
    // possibly-equal indices) — fail closed.
    let no_distinct = vec![parsed[1].clone()];
    assert!(emit_array_defexpanded_firewall_lean_from_parsed(&no_distinct, &defs).is_none());
}

// storeinv_sf_chain, in its `define-fun` form: `a1 = store(a,i,select(a,i))`,
// `a2 = store(a1,j,select(a,j))`, `(not (= a2 a))`. Both writes put the base
// array's own value back, so `a2 = a` in every model — the negated equality is
// unsat. Expanding the macros exposes the write-back chain over base `a`.
#[test]
fn emits_array_writeback_chain_from_parsed() {
    use ay_frontend::command::Term as PTerm;
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let store = |a: PTerm, i: PTerm, v: PTerm| PTerm::App("store".to_string(), vec![a, i, v]);
    let select = |a: PTerm, i: PTerm| PTerm::App("select".to_string(), vec![a, i]);

    // (not (= a2 a)) with a1/a2 nullary define-fun write-backs over base a.
    let target = PTerm::App(
        "not".to_string(),
        vec![PTerm::App("=".to_string(), vec![sym("a2"), sym("a")])],
    );
    let a1_body = store(sym("a"), sym("i"), select(sym("a"), sym("i")));
    let a2_body = store(sym("a1"), sym("j"), select(sym("a"), sym("j")));
    let defs = vec![("a1".to_string(), a1_body), ("a2".to_string(), a2_body)];

    let lean = emit_array_writeback_chain_firewall_lean_from_parsed(&[target], &defs)
        .expect("write-back identity chain should emit after define-fun expansion");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("namespace AySoundness.Emitted.ArrWriteBack_"));
    assert!(lean.contains("abbrev Val := (Nat -> Nat) × (Nat -> Nat)"));
    assert!(lean.contains("attribute [local instance] Classical.propDecidable"));
    assert!(lean.contains("noncomputable def atomVal"));
    // Two store levels → a two-deep by_cases cascade.
    assert!(lean.contains("by_cases h1 : x = (m.2 0)"));
    assert!(lean.contains("by_cases h2 : x = (m.2 1)"));
    assert!(lean.contains("firewall_combined_unsat"));

    // Same conflict already expanded (no macros): still recognized directly.
    let expanded_chain = store(
        store(sym("a"), sym("i"), select(sym("a"), sym("i"))),
        sym("j"),
        select(sym("a"), sym("j")),
    );
    let direct = PTerm::App(
        "not".to_string(),
        vec![PTerm::App("=".to_string(), vec![expanded_chain, sym("a")])],
    );
    assert!(emit_array_writeback_chain_firewall_lean_from_parsed(&[direct], &[]).is_some());
}

#[test]
fn array_writeback_chain_declines_non_identity() {
    use ay_frontend::command::Term as PTerm;
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let store = |a: PTerm, i: PTerm, v: PTerm| PTerm::App("store".to_string(), vec![a, i, v]);
    let select = |a: PTerm, i: PTerm| PTerm::App("select".to_string(), vec![a, i]);

    // store(a, i, select(a, j)) with i ≠ j written index: NOT a write-back (the
    // read index differs from the store index), so `= a` does NOT hold — decline.
    let not_writeback = store(sym("a"), sym("i"), select(sym("a"), sym("j")));
    let target = PTerm::App(
        "not".to_string(),
        vec![PTerm::App("=".to_string(), vec![not_writeback, sym("a")])],
    );
    assert!(emit_array_writeback_chain_firewall_lean_from_parsed(&[target], &[]).is_none());

    // store(a, i, select(b, i)) — value reads a DIFFERENT array b, not the base a:
    // decline (this is not the write-back identity).
    let other_base = store(sym("a"), sym("i"), select(sym("b"), sym("i")));
    let target2 = PTerm::App(
        "not".to_string(),
        vec![PTerm::App("=".to_string(), vec![other_base, sym("a")])],
    );
    assert!(emit_array_writeback_chain_firewall_lean_from_parsed(&[target2], &[]).is_none());
}

// storeinv_cross_1idx: `v0 = store(a2,i,select(a1,i))`, `v1 = store(a1,i,select(a2,i))`,
// `(= v0 v1)`, `(not (= a1 a2))`. Equating the two index-`i` swaps forces `a1 = a2`
// pointwise (array extensionality), contradicting `a1 ≠ a2`. Inlining the array-lets
// exposes the swap equality.
#[test]
fn emits_array_storeinv_swap_from_parsed() {
    use ay_frontend::command::Term as PTerm;
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let store = |a: PTerm, i: PTerm, v: PTerm| PTerm::App("store".to_string(), vec![a, i, v]);
    let select = |a: PTerm, i: PTerm| PTerm::App("select".to_string(), vec![a, i]);
    let eq = |a: PTerm, b: PTerm| PTerm::App("=".to_string(), vec![a, b]);

    let v0def = eq(
        sym("v0"),
        store(sym("a2"), sym("i"), select(sym("a1"), sym("i"))),
    );
    let v1def = eq(
        sym("v1"),
        store(sym("a1"), sym("i"), select(sym("a2"), sym("i"))),
    );
    let equate = eq(sym("v0"), sym("v1"));
    let diseq = PTerm::App("not".to_string(), vec![eq(sym("a1"), sym("a2"))]);
    let parsed = vec![v0def, v1def, equate, diseq];

    let lean = emit_array_storeinv_swap_firewall_lean_from_parsed(&parsed, &[])
        .expect("single-index store-inverse cross-swap should emit after inlining");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("namespace AySoundness.Emitted.ArrStoreInv1_"));
    assert!(lean.contains("attribute [local instance] Classical.propDecidable"));
    assert!(lean.contains("def lemmas   : List (Cid × Clause) := [(3, [-1, 2])]"));
    assert!(lean.contains("firewall_combined_unsat"));
}

#[test]
fn array_storeinv_swap_declines_without_disequality() {
    use ay_frontend::command::Term as PTerm;
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let store = |a: PTerm, i: PTerm, v: PTerm| PTerm::App("store".to_string(), vec![a, i, v]);
    let select = |a: PTerm, i: PTerm| PTerm::App("select".to_string(), vec![a, i]);
    let eq = |a: PTerm, b: PTerm| PTerm::App("=".to_string(), vec![a, b]);

    // The swap equality WITHOUT the `a1 ≠ a2` premise is SAT (take a1 = a2) — must
    // NOT emit a (false) refutation.
    let swap = eq(
        store(sym("a2"), sym("i"), select(sym("a1"), sym("i"))),
        store(sym("a1"), sym("i"), select(sym("a2"), sym("i"))),
    );
    assert!(
        emit_array_storeinv_swap_firewall_lean_from_parsed(std::slice::from_ref(&swap), &[])
            .is_none()
    );

    // Non-swapped stores (same base both sides) with a1 ≠ a2 is NOT the store-inverse
    // conflict — decline.
    let non_swap = eq(
        store(sym("a1"), sym("i"), select(sym("a1"), sym("i"))),
        store(sym("a1"), sym("i"), select(sym("a2"), sym("i"))),
    );
    let diseq = PTerm::App("not".to_string(), vec![eq(sym("a1"), sym("a2"))]);
    assert!(emit_array_storeinv_swap_firewall_lean_from_parsed(&[non_swap, diseq], &[]).is_none());
}

#[test]
fn lia_firewall_declines_array_valued_define_fun() {
    use ay_frontend::command::Term as PTerm;
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let store = |a: PTerm, i: PTerm, v: PTerm| PTerm::App("store".to_string(), vec![a, i, v]);
    let select = |a: PTerm, i: PTerm| PTerm::App("select".to_string(), vec![a, i]);
    let context = cbr_typed_context(Sort::Int);

    // storeinv_sf_chain's residual assertions after ay folds arrays away:
    // `(not (= i j))` (integer) and `(not (= a2 a))` (ARRAY). The array
    // disequality must NOT be reconstructed as a linear-integer atom.
    let idx_diseq = PTerm::App(
        "not".to_string(),
        vec![PTerm::App("=".to_string(), vec![sym("i"), sym("j")])],
    );
    let arr_diseq = PTerm::App(
        "not".to_string(),
        vec![PTerm::App("=".to_string(), vec![sym("a2"), sym("a")])],
    );
    let a2_body = store(sym("a1"), sym("j"), select(sym("a"), sym("j")));
    let defs = vec![("a2".to_string(), a2_body)];

    // With the array-valued define-fun present, decline (this is not pure LIA).
    assert!(emit_lia_firewall_lean_from_parsed(&[idx_diseq, arr_diseq], &defs, &context).is_none());
    // A genuine linear-integer conflict `x > 5 ∧ x < 3` still emits: the gate only
    // fires on array-valued macros, and here `defs` has none.
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let conflict = vec![
        PTerm::App(">".to_string(), vec![sym("x"), num("5")]),
        PTerm::App("<".to_string(), vec![sym("x"), num("3")]),
    ];
    assert!(emit_lia_firewall_lean_from_parsed(&conflict, &defs, &context).is_some());
}

// ==== APPENDED TESTS: lia ====
#[test]
fn emits_lia_linear_conflict_from_parsed() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let context = cbr_typed_context(Sort::Int);
    // (> x 5) ∧ (< x 3): jointly integer-UNSAT bound conflict.
    let parsed = vec![
        PTerm::App(">".to_string(), vec![sym("x"), num("5")]),
        PTerm::App("<".to_string(), vec![sym("x"), num("3")]),
    ];
    let lean = emit_lia_firewall_lean_from_parsed(&parsed, &[], &context)
        .expect("linear integer bound conflict should emit");
    assert!(lean.contains("abbrev Val := Nat → Int"));
    assert!(lean.contains("firewall_combined_unsat"));
    assert!(lean.contains("(m 0)"));
    // A multi-variable linear system rendering distinct `(m i)` projections.
    let multi = vec![
        PTerm::App(
            "=".to_string(),
            vec![
                PTerm::App("+".to_string(), vec![sym("a"), sym("b")]),
                num("1"),
            ],
        ),
        PTerm::App(">=".to_string(), vec![sym("a"), num("1")]),
        PTerm::App(">=".to_string(), vec![sym("b"), num("1")]),
    ];
    let lean2 = emit_lia_firewall_lean_from_parsed(&multi, &[], &context)
        .expect("multi-variable linear conflict should emit");
    assert!(lean2.contains("(m 0)") && lean2.contains("(m 1)"));

    // Declines a genuinely NONLINEAR var*var product (omega cannot discharge).
    let nonlinear = vec![PTerm::App(
        "=".to_string(),
        vec![
            PTerm::App("*".to_string(), vec![sym("x"), sym("y")]),
            num("7"),
        ],
    )];
    assert!(emit_lia_firewall_lean_from_parsed(&nonlinear, &[], &context).is_none());
    // Declines non-arithmetic propositional structure (`or`).
    let prop = vec![PTerm::App("or".to_string(), vec![sym("p"), sym("q")])];
    assert!(emit_lia_firewall_lean_from_parsed(&prop, &[], &context).is_none());
}

#[test]
fn lia_firewall_requires_unique_int_constants_but_keeps_signed_literals() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let app = |op: &str, args: Vec<PTerm>| PTerm::App(op.to_string(), args);

    // SAT over Real at x=1/2. Numeral spelling does not make a Real variable Int.
    let strict_real_gap = vec![
        app(">", vec![sym("x"), num("0")]),
        app("<", vec![sym("x"), num("1")]),
    ];
    let real_context = cbr_typed_context(Sort::Real);
    assert!(
        emit_lia_firewall_lean_from_parsed(&strict_real_gap, &[], &real_context).is_none(),
        "numeral-only Real constraints must not be reinterpreted over Int"
    );

    let missing = ay_frontend::Context::new();
    assert!(emit_lia_firewall_lean_from_parsed(&strict_real_gap, &[], &missing).is_none());

    let mut ambiguous = cbr_typed_context(Sort::Int);
    ambiguous
        .register_native_function_alias(
            "x".to_string(),
            "__firewall_test_x_real".to_string(),
            Vec::new(),
            Sort::Real,
        )
        .expect("test constant overload should be valid");
    assert!(
        emit_lia_firewall_lean_from_parsed(&strict_real_gap, &[], &ambiguous).is_none(),
        "surface overloads have no identity in ParsedTerm and must be declined"
    );

    // ay's parsed AST can preserve a signed literal as numeric symbol text.
    // It remains an Int literal and needs no declaration in Context.
    let int_context = cbr_typed_context(Sort::Int);
    let signed_literal_conflict = vec![
        app(">=", vec![sym("x"), num("0")]),
        app(">", vec![app("*", vec![sym("-1"), sym("x")]), num("0")]),
    ];
    assert!(
        emit_lia_firewall_lean_from_parsed(&signed_literal_conflict, &[], &int_context).is_some(),
        "numeric-text signed literals must remain supported"
    );
}

#[test]
fn lia_firewall_declines_declared_quoted_numeric_real() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let app = |op: &str, args: Vec<PTerm>| PTerm::App(op.to_string(), args);

    // Quoting is erased in ParsedTerm, but Context records the declaration.
    // This source formula is SAT over Real at `|-1| = 1/2`; interpreting its
    // surface text as the signed Int literal -1 would manufacture an UNSAT
    // strict-gap firewall artifact.
    let mut context = ay_frontend::Context::new();
    register_firewall_test_constant(&mut context, "-1", Sort::Real);
    let strict_real_gap = vec![
        app(">", vec![sym("-1"), num("0")]),
        app("<", vec![sym("-1"), num("1")]),
    ];
    assert!(
        emit_lia_firewall_lean_from_parsed(&strict_real_gap, &[], &context).is_none(),
        "declared `|-1| : Real` must win over signed-literal fallback"
    );
}

#[test]
fn lia_firewall_keeps_declared_positive_numeric_int_as_variable() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let app = |op: &str, args: Vec<PTerm>| PTerm::App(op.to_string(), args);

    // A positive numeral token is `Const(Numeral)`, so `Symbol("1")` denotes
    // the quoted declaration `|1|`. It must receive a model slot, not become
    // the literal 1.
    let mut context = ay_frontend::Context::new();
    register_firewall_test_constant(&mut context, "1", Sort::Int);
    let conflict = vec![
        app(">", vec![sym("1"), num("5")]),
        app("<", vec![sym("1"), num("3")]),
    ];
    let lean = emit_lia_firewall_lean_from_parsed(&conflict, &[], &context)
        .expect("declared `|1| : Int` is inside the LIA fragment");
    assert!(
        lean.contains("(m 0)"),
        "declared positive numeric-name constant must remain a variable"
    );
}

#[test]
fn lia_firewall_declines_nonconstant_or_ambiguous_numeric_symbol_declaration() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let app = |op: &str, args: Vec<PTerm>| PTerm::App(op.to_string(), args);
    let parsed = vec![app(">", vec![sym("-1"), num("0")])];

    let mut nonconstant = ay_frontend::Context::new();
    nonconstant
        .register_native_function_alias(
            "-1".to_string(),
            "__firewall_test_numeric_function".to_string(),
            vec![Sort::Int],
            Sort::Int,
        )
        .expect("test numeric-name function should be valid");
    assert!(
        emit_lia_firewall_lean_from_parsed(&parsed, &[], &nonconstant).is_none(),
        "non-nullary `|-1|` declaration must not fall back to an Int literal"
    );

    let mut context = ay_frontend::Context::new();
    register_firewall_test_constant(&mut context, "-1", Sort::Int);
    context
        .register_native_function_alias(
            "-1".to_string(),
            "__firewall_test_numeric_real".to_string(),
            Vec::new(),
            Sort::Real,
        )
        .expect("test numeric-name overload should be valid");
    assert!(
        emit_lia_firewall_lean_from_parsed(&parsed, &[], &context).is_none(),
        "ambiguous `|-1|` declarations must not fall back to an Int literal"
    );
}

// ==== APPENDED TESTS: euf_uflia ====
#[test]
fn emits_euf_lia_congruence_from_parsed_assertions() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let app = |op: &str, a: Vec<PTerm>| PTerm::App(op.to_string(), a);
    let int_context = cbr_typed_context(Sort::Int);

    // POSITIVE: a>=3, a<=3, b=3, f(a)=10, f(b)=20 -> a=b=3 forces f(a)=f(b), 10!=20.
    let parsed = vec![
        app(">=", vec![sym("a"), num("3")]),
        app("<=", vec![sym("a"), num("3")]),
        app("=", vec![sym("b"), num("3")]),
        app("=", vec![app("f", vec![sym("a")]), num("10")]),
        app("=", vec![app("f", vec![sym("b")]), num("20")]),
    ];
    let lean = emit_euf_lia_congruence_firewall_lean_from_parsed(&parsed, &int_context)
        .expect("parsed EUF+LIA congruence conflict should emit");
    assert!(lean.contains("import AySoundness.Firewall"));
    assert!(lean.contains("firewall_combined_unsat"));
    assert!(lean.contains("f_f : Int -> Int"));
    assert!(lean.contains("omega"));
    assert!(lean.contains("rw [he"));

    // POSITIVE (implied-equality + one negated value atom): a+1=b+1, b+2=c+2,
    // f(a)=10, f(c)=10, !(f(b)=10) -> a=b=c so f(b)=f(a)=10, contradiction.
    let parsed3 = vec![
        app(
            "=",
            vec![
                app("+", vec![sym("a"), num("1")]),
                app("+", vec![sym("b"), num("1")]),
            ],
        ),
        app(
            "=",
            vec![
                app("+", vec![sym("b"), num("2")]),
                app("+", vec![sym("c"), num("2")]),
            ],
        ),
        app("=", vec![app("f", vec![sym("a")]), num("10")]),
        app("=", vec![app("f", vec![sym("c")]), num("10")]),
        app(
            "not",
            vec![app("=", vec![app("f", vec![sym("b")]), num("10")])],
        ),
    ];
    assert!(emit_euf_lia_congruence_firewall_lean_from_parsed(&parsed3, &int_context).is_some());

    // Numeric-text signed literals are emitted by ay's lenient parsed surface
    // for some inputs. Preserve them as literals in both LIA terms and UF values.
    let signed_literals = vec![
        app("=", vec![app("*", vec![sym("-1"), sym("a")]), num("0")]),
        app("=", vec![sym("b"), num("0")]),
        app("=", vec![app("f", vec![sym("a")]), sym("-1")]),
        app("=", vec![app("f", vec![sym("b")]), num("0")]),
    ];
    assert!(
        emit_euf_lia_congruence_firewall_lean_from_parsed(&signed_literals, &int_context).is_some(),
        "numeric-text signed literals must remain supported"
    );

    // NEGATIVE (no implied equality): a and b unconstrained, f(a)=10, f(b)=20 --
    // no LIA fact forces a=b, so no congruence conflict -> decline.
    let no_eq = vec![
        app("=", vec![app("f", vec![sym("a")]), num("10")]),
        app("=", vec![app("f", vec![sym("b")]), num("20")]),
    ];
    assert!(emit_euf_lia_congruence_firewall_lean_from_parsed(&no_eq, &int_context).is_none());

    // NEGATIVE (consistent values): a=b but f(a)=10, f(b)=10 -- no conflict.
    let consistent = vec![
        app("=", vec![sym("a"), num("3")]),
        app("=", vec![sym("b"), num("3")]),
        app("=", vec![app("f", vec![sym("a")]), num("10")]),
        app("=", vec![app("f", vec![sym("b")]), num("10")]),
    ];
    assert!(emit_euf_lia_congruence_firewall_lean_from_parsed(&consistent, &int_context).is_none());

    // NEGATIVE (Real / QF_UFLRA gate): decimal numerals are not Int -> decline.
    let real = vec![
        app(
            "=",
            vec![sym("a"), PTerm::Const(PConst::Decimal("5.0".to_string()))],
        ),
        app(
            "=",
            vec![sym("b"), PTerm::Const(PConst::Decimal("5.0".to_string()))],
        ),
        app("=", vec![app("f", vec![sym("a")]), num("10")]),
        app("=", vec![app("f", vec![sym("b")]), num("20")]),
    ];
    assert!(emit_euf_lia_congruence_firewall_lean_from_parsed(&real, &int_context).is_none());
}

#[test]
fn euf_lia_firewall_does_not_literalize_declared_quoted_numeric_int() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let app = |op: &str, args: Vec<PTerm>| PTerm::App(op.to_string(), args);

    // SAT: a=b and choose `|-1| = 0`, so both applications of f have value 0.
    // Treating the declared constant's numeric-looking text as literal -1
    // would invent a congruence conflict between f(a)=-1 and f(b)=0.
    let mut context = cbr_typed_context(Sort::Int);
    register_firewall_test_constant(&mut context, "-1", Sort::Int);
    let parsed = vec![
        app("=", vec![sym("a"), sym("b")]),
        app("=", vec![app("f", vec![sym("a")]), sym("-1")]),
        app("=", vec![app("f", vec![sym("b")]), num("0")]),
    ];
    assert!(
        emit_euf_lia_congruence_firewall_lean_from_parsed(&parsed, &context).is_none(),
        "declared `|-1| : Int` is a variable, not a UF-value literal"
    );
}

#[test]
fn euf_lia_firewall_keeps_declared_positive_numeric_int_as_variable() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let app = |op: &str, args: Vec<PTerm>| PTerm::App(op.to_string(), args);

    // `|1| = b` makes the two UF arguments equal. Both normalization and Lean
    // rendering must keep `|1|` as an Int variable; literalizing it would only
    // pin b=1 and miss the congruence bridge.
    let mut context = cbr_typed_context(Sort::Int);
    register_firewall_test_constant(&mut context, "1", Sort::Int);
    let parsed = vec![
        app("=", vec![sym("1"), sym("b")]),
        app("=", vec![app("f", vec![sym("1")]), num("10")]),
        app("=", vec![app("f", vec![sym("b")]), num("20")]),
    ];
    let lean = emit_euf_lia_congruence_firewall_lean_from_parsed(&parsed, &context)
        .expect("declared `|1| : Int` must participate in the congruence bridge");
    assert!(lean.contains("x_1 : Int"));
    assert!(lean.contains("m.x_1 = m.x_b"));
}

#[test]
fn euf_lia_firewall_requires_unique_int_signatures() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let app = |op: &str, args: Vec<PTerm>| PTerm::App(op.to_string(), args);
    let parsed = vec![
        app(">=", vec![sym("a"), num("3")]),
        app("<=", vec![sym("a"), num("3")]),
        app("=", vec![sym("b"), num("3")]),
        app("=", vec![app("f", vec![sym("a")]), num("10")]),
        app("=", vec![app("f", vec![sym("b")]), num("20")]),
    ];

    let missing = ay_frontend::Context::new();
    assert!(emit_euf_lia_congruence_firewall_lean_from_parsed(&parsed, &missing).is_none());

    let mut missing_function = ay_frontend::Context::new();
    for name in ["a", "b"] {
        register_firewall_test_constant(&mut missing_function, name, Sort::Int);
    }
    assert!(
        emit_euf_lia_congruence_firewall_lean_from_parsed(&parsed, &missing_function).is_none()
    );

    let mut wrong_function_sort = ay_frontend::Context::new();
    for name in ["a", "b"] {
        register_firewall_test_constant(&mut wrong_function_sort, name, Sort::Int);
    }
    wrong_function_sort
        .register_native_function_alias(
            "f".to_string(),
            "__firewall_test_int_to_real_f".to_string(),
            vec![Sort::Int],
            Sort::Real,
        )
        .expect("test Int-to-Real UF declaration should be valid");
    assert!(
        emit_euf_lia_congruence_firewall_lean_from_parsed(&parsed, &wrong_function_sort).is_none()
    );

    let mut ambiguous_constant = cbr_typed_context(Sort::Int);
    ambiguous_constant
        .register_native_function_alias(
            "a".to_string(),
            "__firewall_test_a_real".to_string(),
            Vec::new(),
            Sort::Real,
        )
        .expect("test constant overload should be valid");
    assert!(
        emit_euf_lia_congruence_firewall_lean_from_parsed(&parsed, &ambiguous_constant).is_none()
    );

    let mut ambiguous_function = cbr_typed_context(Sort::Int);
    ambiguous_function
        .register_native_function_alias(
            "f".to_string(),
            "__firewall_test_f_real_int".to_string(),
            vec![Sort::Real],
            Sort::Int,
        )
        .expect("test function overload should be valid");
    assert!(
        emit_euf_lia_congruence_firewall_lean_from_parsed(&parsed, &ambiguous_function).is_none()
    );
}

#[test]
fn euf_lia_firewall_declines_numeral_only_real_congruence_gap() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let app = |op: &str, args: Vec<PTerm>| PTerm::App(op.to_string(), args);

    let mut context = ay_frontend::Context::new();
    for name in ["a", "b"] {
        register_firewall_test_constant(&mut context, name, Sort::Real);
    }
    context
        .register_native_function_alias(
            "f".to_string(),
            "__firewall_test_real_to_int_f".to_string(),
            vec![Sort::Real],
            Sort::Int,
        )
        .expect("test Real-to-Int UF declaration should be valid");

    // SAT over Real: choose a=1/2 and b=1, so the two UF arguments differ.
    // Reinterpreting a and b as Int would instead force a=b=1 and manufacture
    // a false congruence conflict between the two distinct UF values.
    let parsed = vec![
        app(">", vec![sym("a"), num("0")]),
        app("<=", vec![sym("a"), num("1")]),
        app("=", vec![sym("b"), num("1")]),
        app("=", vec![app("f", vec![sym("a")]), num("10")]),
        app("=", vec![app("f", vec![sym("b")]), num("20")]),
    ];
    assert!(
        emit_euf_lia_congruence_firewall_lean_from_parsed(&parsed, &context).is_none(),
        "numeral-only Real constraints and a Real-to-Int UF must not be modelled as UFLIA"
    );
}

#[test]
fn euf_lia_firewall_checks_i64_normalization_bounds_and_pins() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let app = |op: &str, args: Vec<PTerm>| PTerm::App(op.to_string(), args);
    let uf_values = || {
        vec![
            app("=", vec![app("f", vec![sym("a")]), num("10")]),
            app("=", vec![app("f", vec![sym("b")]), num("20")]),
        ]
    };
    let context = cbr_typed_context(Sort::Int);
    let max = i64::MAX.to_string();
    let min = i64::MIN.to_string();

    // MAX+1 is valid unbounded SMT Int arithmetic but outside this recognizer's
    // i64 analysis domain.
    let mut normalization_overflow = vec![app(
        "=",
        vec![app("+", vec![sym("a"), num(&max), num("1")]), sym("b")],
    )];
    normalization_overflow.extend(uf_values());
    assert!(
        emit_euf_lia_congruence_firewall_lean_from_parsed(&normalization_overflow, &context,)
            .is_none()
    );

    // `a + MIN > 0` has an inclusive integer lower bound above i64::MAX.
    // The normal form fits, but bound extraction must decline exactly.
    let mut bound_overflow = vec![app(
        ">",
        vec![app("+", vec![sym("a"), sym(&min)]), num("0")],
    )];
    bound_overflow.extend(uf_values());
    assert!(emit_euf_lia_congruence_firewall_lean_from_parsed(&bound_overflow, &context).is_none());

    // `a + MIN = 0` would pin a to 2^63, outside the analysis domain.
    let mut pin_out_of_range = vec![app(
        "=",
        vec![app("+", vec![sym("a"), sym(&min)]), num("0")],
    )];
    pin_out_of_range.extend(uf_values());
    assert!(
        emit_euf_lia_congruence_firewall_lean_from_parsed(&pin_out_of_range, &context).is_none()
    );

    // The MIN/-1 pin shape used to panic while evaluating `-MIN / -1`.
    // The bounded recognizer may conservatively decline it, but must never
    // perform that overflowing i64 arithmetic or wrap into a false bridge.
    let pin_min = |name: &str| {
        app(
            "=",
            vec![
                app("+", vec![app("*", vec![sym("-1"), sym(name)]), sym(&min)]),
                num("0"),
            ],
        )
    };
    let mut exact_min_pins = vec![pin_min("a"), pin_min("b")];
    exact_min_pins.extend(uf_values());
    assert!(
        emit_euf_lia_congruence_firewall_lean_from_parsed(&exact_min_pins, &context).is_none(),
        "the MIN/-1 pin boundary must decline without panicking or wrapping"
    );
}

#[test]
fn emits_dt_occurs_check_from_parsed() {
    use ay_frontend::command::Term as PTerm;
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    // (= x (cons h (cons h x))) — the r3_rank1 recursive-list occurs-check:
    // `x` occurs as a PROPER subterm under two `cons` constructor layers.
    let inner = app("cons", vec![sym("h"), sym("x")]);
    let rhs = app("cons", vec![sym("h"), inner]);
    let parsed = vec![app("=", vec![sym("x"), rhs])];
    let ctors = vec!["cons".to_string(), "nil".to_string()];
    let decls: Vec<(String, Vec<String>)> = vec![("Lst".to_string(), ctors.clone())];
    let sels: Vec<(String, Vec<String>)> = vec![
        ("cons".to_string(), vec!["hd".to_string(), "tl".to_string()]),
        ("nil".to_string(), vec![]),
    ];

    let lean = emit_dt_occurs_check_firewall_lean_from_parsed(&parsed, &ctors, &decls, &sels)
        .expect("acyclicity / occurs-check conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("import AySoundness.Datatype"));
    assert!(lean.contains("acyclic_conflict_generic"));
    assert!(lean.contains("DtT.wrap.sizeOf_spec"));
    assert!(lean.contains("firewall_combined_unsat"));
    // depth 2 -> two nested `wrap` layers in the context.
    assert!(lean.contains("DtT.wrap (DtT.wrap (z))"));

    // Reversed orientation `(= (cons h (cons h x)) x)` also fires.
    let inner2 = app("cons", vec![sym("h"), sym("x")]);
    let rhs2 = app("cons", vec![sym("h"), inner2]);
    let rev = vec![app("=", vec![rhs2, sym("x")])];
    assert!(emit_dt_occurs_check_firewall_lean_from_parsed(&rev, &ctors, &decls, &sels).is_some());
}

#[test]
fn emits_dt_occurs_check_selector_mediated_from_parsed() {
    // Shape (B): `x = cons(cons(tl x))` over `Lst = cons(tl Lst) | nil`.
    // `x` occurs only under the selector `tl`, so the pure-constructor pass
    // declines; projecting field 0 of the top `cons` via its own selector `tl`
    // gives `tl x = cons(tl x)` = `t = cons t`, a depth-1 occurs-check.
    use ay_frontend::command::Term as PTerm;
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    let ctors = vec!["cons".to_string(), "nil".to_string()];
    let decls: Vec<(String, Vec<String>)> = vec![("Lst".to_string(), ctors.clone())];
    // Single-field `cons` with selector `tl` (matches the target .smt2).
    let sels: Vec<(String, Vec<String>)> = vec![
        ("cons".to_string(), vec!["tl".to_string()]),
        ("nil".to_string(), vec![]),
    ];

    let parsed = vec![app(
        "=",
        vec![
            sym("x"),
            app("cons", vec![app("cons", vec![app("tl", vec![sym("x")])])]),
        ],
    )];
    let lean = emit_dt_occurs_check_firewall_lean_from_parsed(&parsed, &ctors, &decls, &sels)
        .expect("selector-mediated occurs-check should emit");
    assert!(lean.contains("acyclic_conflict_generic"));
    assert!(lean.contains("DtT.wrap.sizeOf_spec"));
    // depth 1 -> a single `wrap` layer.
    assert!(lean.contains("DtT.wrap (z)"));

    // Reversed orientation fires too.
    let rev = vec![app(
        "=",
        vec![
            app("cons", vec![app("cons", vec![app("tl", vec![sym("x")])])]),
            sym("x"),
        ],
    )];
    assert!(emit_dt_occurs_check_firewall_lean_from_parsed(&rev, &ctors, &decls, &sels).is_some());

    // WITHOUT selector metadata the emitter cannot soundly project — decline.
    let no_sels: Vec<(String, Vec<String>)> = vec![];
    assert!(
        emit_dt_occurs_check_firewall_lean_from_parsed(&parsed, &ctors, &decls, &no_sels).is_none()
    );
}

#[test]
fn emits_dt_occurs_check_safe_ite_tester_from_parsed() {
    // Shape (C): tautological-tester `ite` + selector-self-eq under an asserted
    // tester, over `Rec = mkRec` (single ctor) and `Tree = leaf | node(left,right)`.
    //   (= (ite ((_ is mkRec) r) v12 v11) (left v12))
    //   ((_ is node) v12)
    // `is-mkRec` is a tautology (Rec single-ctor) so the ite folds to `v12`,
    // giving `v12 = left v12`; the asserted `is-node v12` gives the node form,
    // and substitution yields `v12 = node(v12, right v12)` = depth-1 occurs-check.
    use ay_frontend::command::{Index as PIndex, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    let tester = |c: &str, on: &str| {
        PTerm::IndexedApp(
            "is".to_string(),
            vec![PIndex::Symbol(c.to_string())],
            vec![sym(on)],
        )
    };
    let ctors = vec!["mkRec".to_string(), "leaf".to_string(), "node".to_string()];
    let decls: Vec<(String, Vec<String>)> = vec![
        ("Rec".to_string(), vec!["mkRec".to_string()]),
        (
            "Tree".to_string(),
            vec!["leaf".to_string(), "node".to_string()],
        ),
    ];
    let sels: Vec<(String, Vec<String>)> = vec![
        ("mkRec".to_string(), vec![]),
        ("leaf".to_string(), vec![]),
        (
            "node".to_string(),
            vec!["left".to_string(), "right".to_string()],
        ),
    ];

    let eq = app(
        "=",
        vec![
            app("ite", vec![tester("mkRec", "r"), sym("v12"), sym("v11")]),
            app("left", vec![sym("v12")]),
        ],
    );
    let parsed = vec![eq, tester("node", "v12")];
    let lean = emit_dt_occurs_check_firewall_lean_from_parsed(&parsed, &ctors, &decls, &sels)
        .expect("safe-ite tester occurs-check should emit");
    assert!(lean.contains("acyclic_conflict_generic"));
    assert!(lean.contains("DtT.wrap.sizeOf_spec"));
    assert!(lean.contains("DtT.wrap (z)"));

    // Without the asserted `(_ is node) v12`, the node form is not derivable —
    // `v12 = left v12` alone is SAT (a fixpoint under `left`) — decline.
    let no_tester = vec![app(
        "=",
        vec![
            app("ite", vec![tester("mkRec", "r"), sym("v12"), sym("v11")]),
            app("left", vec![sym("v12")]),
        ],
    )];
    assert!(
        emit_dt_occurs_check_firewall_lean_from_parsed(&no_tester, &ctors, &decls, &sels).is_none()
    );

    // If the ite guard is NOT a sole-constructor tester it is not a tautology
    // and must not fold — decline.
    let multi_decls: Vec<(String, Vec<String>)> = vec![
        (
            "Rec".to_string(),
            vec!["mkRec".to_string(), "mkRec2".to_string()],
        ),
        (
            "Tree".to_string(),
            vec!["leaf".to_string(), "node".to_string()],
        ),
    ];
    assert!(
        emit_dt_occurs_check_firewall_lean_from_parsed(&parsed, &ctors, &multi_decls, &sels)
            .is_none()
    );
}

#[test]
fn dt_occurs_check_declines_non_occurrence_and_selectors() {
    use ay_frontend::command::Term as PTerm;
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    let ctors = vec!["cons".to_string(), "nil".to_string()];
    let decls: Vec<(String, Vec<String>)> = vec![("Lst".to_string(), ctors.clone())];
    let sels: Vec<(String, Vec<String>)> = vec![
        ("cons".to_string(), vec!["hd".to_string(), "tl".to_string()]),
        ("nil".to_string(), vec![]),
    ];

    // No occurrence: `x = cons(h, y)` with y != x — genuinely SAT, must decline.
    let sat = vec![app(
        "=",
        vec![sym("x"), app("cons", vec![sym("h"), sym("y")])],
    )];
    assert!(emit_dt_occurs_check_firewall_lean_from_parsed(&sat, &ctors, &decls, &sels).is_none());

    // Non-constructor head (`t` is itself absent from a real ctor path): decline.
    let bogus = vec![app("=", vec![sym("x"), app("f", vec![sym("x")])])];
    assert!(
        emit_dt_occurs_check_firewall_lean_from_parsed(&bogus, &ctors, &decls, &sels).is_none()
    );

    // Selector-mediated shape (B) but the projected selector does not match the
    // occurring one: `x = cons(cons(tl x))` while `cons`'s single field selector
    // is `hd` (not `tl`). Projecting field 0 via `hd` yields `hd x`, which does
    // NOT occur in `cons(tl x)` — decline (fail-closed on selector mismatch).
    let mismatch_sels: Vec<(String, Vec<String>)> = vec![
        ("cons".to_string(), vec!["hd".to_string()]),
        ("nil".to_string(), vec![]),
    ];
    let sel = vec![app(
        "=",
        vec![
            sym("x"),
            app("cons", vec![app("cons", vec![app("tl", vec![sym("x")])])]),
        ],
    )];
    assert!(
        emit_dt_occurs_check_firewall_lean_from_parsed(&sel, &ctors, &decls, &mismatch_sels)
            .is_none()
    );
}

#[test]
fn emits_dt_tester_exclusion_from_parsed() {
    // bench `soundness_qf_dt_derived_terms/bug1_tester_excl_uf_app.smt2`:
    //   (declare-datatype Enum ((c0) (c1) (c2)))
    //   (assert ((_ is c0) (f x)))  (assert ((_ is c1) (f x)))
    // Two DISTINCT testers on the SAME opaque term `(f x)` — mutual exclusion.
    use ay_frontend::command::{Index as PIndex, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    let tester = |c: &str, on: PTerm| {
        PTerm::IndexedApp(
            "is".to_string(),
            vec![PIndex::Symbol(c.to_string())],
            vec![on],
        )
    };
    let decls: Vec<(String, Vec<String>)> = vec![(
        "Enum".to_string(),
        vec!["c0".to_string(), "c1".to_string(), "c2".to_string()],
    )];
    let fx = app("f", vec![sym("x")]);
    let parsed = vec![tester("c0", fx.clone()), tester("c1", fx.clone())];
    let lean = emit_dt_tester_exclusion_firewall_lean_from_parsed(&parsed, &decls)
        .expect("two distinct testers on one term should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("firewall_combined_unsat"));
    assert!(lean.contains("DtTesterExcl_"));
    assert!(lean.contains("| k0 | k1 | k2"));
    assert!(lean.contains(".k0 => true")); // isC_i selects c0
    assert!(lean.contains(".k1 => true")); // isC_j selects c1

    // SAME constructor on the same term is NOT a conflict — decline.
    let same = vec![tester("c0", fx.clone()), tester("c0", fx.clone())];
    assert!(emit_dt_tester_exclusion_firewall_lean_from_parsed(&same, &decls).is_none());

    // Distinct testers on DIFFERENT terms are not jointly a conflict — decline.
    let diff = vec![
        tester("c0", app("f", vec![sym("x")])),
        tester("c1", app("f", vec![sym("y")])),
    ];
    assert!(emit_dt_tester_exclusion_firewall_lean_from_parsed(&diff, &decls).is_none());

    // Constructors from DIFFERENT datatypes never mutually exclude on one term —
    // decline (fail-closed; also ill-typed, but the emitter must not rely on that).
    let two_dt: Vec<(String, Vec<String>)> = vec![
        ("A".to_string(), vec!["c0".to_string()]),
        ("B".to_string(), vec!["c1".to_string()]),
    ];
    assert!(emit_dt_tester_exclusion_firewall_lean_from_parsed(&parsed, &two_dt).is_none());
}

#[test]
fn emits_dt_exhaustiveness_from_parsed() {
    // bench `qf_dt/v2l60078.cvc.smt2` core conflict: over `list` (2 ctors
    // cons|null), `(not ((_ is cons) (cdr x4)))` AND `(not (= null (cdr x4)))` —
    // a list value that is neither constructor. Buried in a nested `and` of noise.
    use ay_frontend::command::Constant as PConst;
    use ay_frontend::command::{Index as PIndex, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    let not = |t: PTerm| app("not", vec![t]);
    let tester = |c: &str, on: PTerm| {
        PTerm::IndexedApp(
            "is".to_string(),
            vec![PIndex::Symbol(c.to_string())],
            vec![on],
        )
    };
    let decls: Vec<(String, Vec<String>)> = vec![
        (
            "nat".to_string(),
            vec!["succ".to_string(), "zero".to_string()],
        ),
        (
            "list".to_string(),
            vec!["cons".to_string(), "null".to_string()],
        ),
        (
            "tree".to_string(),
            vec!["node".to_string(), "leaf".to_string()],
        ),
    ];
    let cdr = app("cdr", vec![sym("x4")]);
    // Nested `(and (and NOISE (not is-cons(cdr x4))) (not (= null (cdr x4))))`.
    let noise = app("=", vec![app("node", vec![sym("x3")]), sym("x5")]);
    let succ_noise = not(tester("succ", sym("zero")));
    let parsed = vec![app(
        "and",
        vec![
            app(
                "and",
                vec![
                    app("and", vec![noise, succ_noise]),
                    not(tester("cons", cdr.clone())),
                ],
            ),
            not(app("=", vec![sym("null"), cdr.clone()])),
        ],
    )];
    let lean = emit_dt_exhaustiveness_firewall_lean_from_parsed(&parsed, &decls)
        .expect("2-ctor exhaustiveness conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("firewall_combined_unsat"));
    assert!(lean.contains("DtExhaust_"));
    assert!(lean.contains("| k0 | k1"));
    assert!(lean.contains("isC(T) ∨ T = D") || lean.contains("[1, 2]"));

    // Reversed equality order `(not (= (cdr x4) null))` also matches.
    let rev = vec![app(
        "and",
        vec![
            not(tester("cons", cdr.clone())),
            not(app("=", vec![cdr.clone(), sym("null")])),
        ],
    )];
    assert!(emit_dt_exhaustiveness_firewall_lean_from_parsed(&rev, &decls).is_some());

    // Datatype with >2 constructors is NOT exhausted by one neg-tester + one
    // diseq — decline (fail-closed).
    let three: Vec<(String, Vec<String>)> = vec![(
        "list".to_string(),
        vec!["cons".to_string(), "null".to_string(), "snoc".to_string()],
    )];
    assert!(emit_dt_exhaustiveness_firewall_lean_from_parsed(&parsed, &three).is_none());

    // Missing the disequality conjunct — `¬is-cons(t)` alone is SAT — decline.
    let only_tester = vec![not(tester("cons", cdr.clone()))];
    assert!(emit_dt_exhaustiveness_firewall_lean_from_parsed(&only_tester, &decls).is_none());

    // Disequality against a NON-nullary partner would be unsound; here `succ` is
    // in `nat`, term mismatched — no valid pairing — decline. (Also silences the
    // unused `PConst` import for numeral-free builds.)
    let _ = PConst::Numeral("0".to_string());
    let mismatch = vec![app(
        "and",
        vec![
            not(tester("cons", cdr.clone())),
            not(app("=", vec![sym("zero"), sym("other")])),
        ],
    )];
    assert!(emit_dt_exhaustiveness_firewall_lean_from_parsed(&mismatch, &decls).is_none());

    // Constructor surface names may be overloaded across datatype declarations.
    // The parsed terms carry no resolved sort identity, so choosing the first
    // owner could mistake a three-constructor carrier for a two-constructor one
    // and emit a false exhaustiveness refutation. Ambiguity must decline.
    let overloaded = vec![
        ("Two".to_string(), vec!["C".to_string(), "D".to_string()]),
        (
            "Three".to_string(),
            vec!["C".to_string(), "D".to_string(), "E".to_string()],
        ),
    ];
    let ambiguous = vec![
        not(tester("C", sym("t"))),
        not(app("=", vec![sym("D"), sym("t")])),
    ];
    assert!(emit_dt_exhaustiveness_firewall_lean_from_parsed(&ambiguous, &overloaded).is_none());

    // `C` can be unambiguous while its exhaustiveness partner `D` is overloaded.
    // Requiring only membership in C's constructor list would still lose D's
    // resolved datatype identity, so this ambiguity must also decline.
    let overloaded_partner = vec![
        ("Two".to_string(), vec!["C".to_string(), "D".to_string()]),
        ("Other".to_string(), vec!["D".to_string(), "E".to_string()]),
    ];
    assert!(
        emit_dt_exhaustiveness_firewall_lean_from_parsed(&ambiguous, &overloaded_partner).is_none()
    );
}

#[test]
fn emits_dt_selector_over_ctor_from_parsed() {
    // bench `datatype_simple.smt2`: `(= x (Some 0x2a))` + `(not (= (value x) 0x2a))`
    // — the selector `value` over the matching constructor `Some` projects `0x2a`.
    use ay_frontend::command::Constant as PConst;
    use ay_frontend::command::Term as PTerm;
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    let not = |t: PTerm| app("not", vec![t]);
    let k = PTerm::Const(PConst::Hexadecimal("000000000000002a".to_string()));
    // ctor->selectors: Some has one field selector `value`; None is nullary.
    let sels: Vec<(String, Vec<String>)> = vec![
        ("None_Option_bv64".to_string(), vec![]),
        ("Some_Option_bv64".to_string(), vec!["value".to_string()]),
    ];
    let decls = vec![(
        "Option_bv64".to_string(),
        vec![
            "None_Option_bv64".to_string(),
            "Some_Option_bv64".to_string(),
        ],
    )];
    let bind = app(
        "=",
        vec![sym("x"), app("Some_Option_bv64", vec![k.clone()])],
    );
    let diseq = app(
        "not",
        vec![app("=", vec![app("value", vec![sym("x")]), k.clone()])],
    );
    let parsed = vec![bind.clone(), diseq.clone()];
    let lean = emit_dt_selector_over_ctor_firewall_lean_from_parsed(&parsed, &decls, &sels)
        .expect("selector-over-constructor conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("firewall_combined_unsat"));
    assert!(lean.contains("DtSelCtor_"));
    assert!(lean.contains("def sel : D -> Int"));

    // If the selector's projected value does NOT match the constructor argument
    // (`(not (= (value x) 0x2b))` while `x = Some 0x2a`), it is not this identity
    // conflict — decline (fail-closed; that would be a genuine BV disequality).
    let other = PTerm::Const(PConst::Hexadecimal("000000000000002b".to_string()));
    let diseq2 = app(
        "not",
        vec![app("=", vec![app("value", vec![sym("x")]), other])],
    );
    assert!(emit_dt_selector_over_ctor_firewall_lean_from_parsed(
        &[bind.clone(), diseq2],
        &decls,
        &sels
    )
    .is_none());

    // A selector name that is NOT a field of the bound constructor — decline.
    let wrong_sels: Vec<(String, Vec<String>)> =
        vec![("Some_Option_bv64".to_string(), vec!["notvalue".to_string()])];
    assert!(
        emit_dt_selector_over_ctor_firewall_lean_from_parsed(&parsed, &decls, &wrong_sels)
            .is_none()
    );

    // Missing the constructor binding — `(value x) ≠ 0x2a` alone is SAT — decline.
    assert!(
        emit_dt_selector_over_ctor_firewall_lean_from_parsed(&[diseq], &decls, &sels).is_none()
    );

    // The elaboration context stores selector metadata by constructor surface
    // name, so overloads can overwrite field order. Parsed terms alone cannot
    // tell which `C` was resolved; require one datatype owner and decline.
    let overloaded_decls = vec![
        ("A".to_string(), vec!["C".to_string()]),
        ("B".to_string(), vec!["C".to_string()]),
    ];
    let overwritten_sels = vec![("C".to_string(), vec!["u".to_string(), "s".to_string()])];
    let overloaded_bind = app(
        "=",
        vec![
            sym("overloaded_x"),
            app(
                "C",
                vec![
                    PTerm::Const(PConst::Numeral("0".to_string())),
                    PTerm::Const(PConst::Numeral("1".to_string())),
                ],
            ),
        ],
    );
    let overloaded_diseq = not(app(
        "=",
        vec![
            app("s", vec![sym("overloaded_x")]),
            PTerm::Const(PConst::Numeral("1".to_string())),
        ],
    ));
    assert!(emit_dt_selector_over_ctor_firewall_lean_from_parsed(
        &[overloaded_bind, overloaded_diseq],
        &overloaded_decls,
        &overwritten_sels,
    )
    .is_none());
}

#[test]
fn emits_dt_case_split_ite_from_parsed() {
    // boolean-ite-guard, bench `qf_dt_occurs_ite_ctor_eq_false_sat.smt2`:
    //   (= (cons F) (ite b F nil))  over  Lst = cons(tl:Lst) | nil.
    // by_cases b: (b=true) `cons F = F` OCCURS-CHECK; (b=false) `cons F = nil`
    // DISTINCTNESS. Single lemma clause `[-1]` validated by the split.
    use ay_frontend::command::Term as PTerm;
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    let ctors = vec!["cons".to_string(), "nil".to_string()];
    let decls: Vec<(String, Vec<String>)> = vec![("Lst".to_string(), ctors.clone())];

    let parsed = vec![app(
        "=",
        vec![
            app("cons", vec![sym("F")]),
            app("ite", vec![sym("b"), sym("F"), sym("nil")]),
        ],
    )];
    let lean = emit_dt_case_split_firewall_lean_from_parsed(&parsed, &ctors, &decls)
        .expect("boolean-ite-guard case split should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("import AySoundness.Datatype"));
    assert!(lean.contains("firewall_combined_unsat"));
    assert!(lean.contains("cases hg : m.g"));
    assert!(lean.contains("acyclic_conflict_generic")); // occurs branch
    assert!(lean.contains("DtT.noConfusion")); // distinctness branch
    assert!(lean.contains("cond m.g (m.t) (DtT.base)"));

    // Reversed orientation `(= (ite b F nil) (cons F))` also fires.
    let rev = vec![app(
        "=",
        vec![
            app("ite", vec![sym("b"), sym("F"), sym("nil")]),
            app("cons", vec![sym("F")]),
        ],
    )];
    assert!(emit_dt_case_split_firewall_lean_from_parsed(&rev, &ctors, &decls).is_some());
}

#[test]
fn emits_dt_case_split_ite_with_folding_from_parsed() {
    // boolean-ite-guard AFTER sound const-folds, bench `dt_residual_falsesat_1.smt2`:
    //   (= (node v11 (ite v15 v5 v5) v10)
    //      (ite ((_ is nil) (cons v16 nil)) (ite v16 v12 (leaf c2)) (ite v15 v11 (leaf v2))))
    // Folds: reflexive `(ite v15 v5 v5)`→v5; tester `((_ is nil)(cons ..))`→false so
    // the outer ite→ELSE `(ite v15 v11 (leaf v2))`. Residual `node v11 v5 v10 =
    // ite v15 v11 (leaf v2)`: (v15=true) OCCURS-CHECK `node.. ≠ v11`; (v15=false)
    // DISTINCTNESS `node.. ≠ leaf v2`.
    use ay_frontend::command::{Index as PIndex, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    let tester = |c: &str, on: PTerm| {
        PTerm::IndexedApp(
            "is".to_string(),
            vec![PIndex::Symbol(c.to_string())],
            vec![on],
        )
    };
    let ctors = vec![
        "node".to_string(),
        "leaf".to_string(),
        "cons".to_string(),
        "nil".to_string(),
    ];
    let decls: Vec<(String, Vec<String>)> = vec![
        (
            "Tree".to_string(),
            vec!["leaf".to_string(), "node".to_string()],
        ),
        (
            "Lst".to_string(),
            vec!["cons".to_string(), "nil".to_string()],
        ),
    ];
    let lhs = app(
        "node",
        vec![
            sym("v11"),
            app("ite", vec![sym("v15"), sym("v5"), sym("v5")]),
            sym("v10"),
        ],
    );
    let rhs = app(
        "ite",
        vec![
            tester("nil", app("cons", vec![sym("v16"), sym("nil")])),
            app(
                "ite",
                vec![sym("v16"), sym("v12"), app("leaf", vec![sym("c2")])],
            ),
            app(
                "ite",
                vec![sym("v15"), sym("v11"), app("leaf", vec![sym("v2")])],
            ),
        ],
    );
    let parsed = vec![app("=", vec![lhs, rhs])];
    let lean = emit_dt_case_split_firewall_lean_from_parsed(&parsed, &ctors, &decls)
        .expect("folded boolean-ite-guard case split should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("acyclic_conflict_generic"));
    assert!(lean.contains("DtT.noConfusion"));
    assert!(lean.contains("cases hg : m.g"));
}

#[test]
fn emits_dt_case_split_distinct_disjunction_from_parsed() {
    // finite-distinct-disjunction, bench `qf_dt_acyclicity_casesplit_false_sat.smt2`:
    //   ((_ is nd) x)   and   (not (distinct (nd y x) lf x))
    // over Tree = lf | nd(lc,rc). The 3-way OR resolves against distinctness
    // `[-2]` (nd≠lf), occurs `[-3]` (nd(y,x)≠x) and tester-exclusion `[-1,-4]`.
    use ay_frontend::command::{Index as PIndex, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    let tester = |c: &str, on: &str| {
        PTerm::IndexedApp(
            "is".to_string(),
            vec![PIndex::Symbol(c.to_string())],
            vec![sym(on)],
        )
    };
    let ctors = vec!["lf".to_string(), "nd".to_string()];
    let decls: Vec<(String, Vec<String>)> = vec![("Tree".to_string(), ctors.clone())];
    let parsed = vec![
        tester("nd", "x"),
        app(
            "not",
            vec![app(
                "distinct",
                vec![app("nd", vec![sym("y"), sym("x")]), sym("lf"), sym("x")],
            )],
        ),
    ];
    let lean = emit_dt_case_split_firewall_lean_from_parsed(&parsed, &ctors, &decls)
        .expect("distinct-disjunction case split should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("import AySoundness.Datatype"));
    assert!(lean.contains("firewall_combined_unsat"));
    assert!(lean.contains("tester_node_leaf_excl") || lean.contains("isNode"));
    assert!(lean.contains("Tree.node_ne_leaf"));
    assert!(lean.contains("Tree.acyclic_r"));
    // The 3-lemma resolution table + disjunctive original clause.
    assert!(lean.contains("[(1, [1]), (2, [2, 3, 4])]"));
    assert!(lean.contains("[(3, [-2]), (4, [-3]), (5, [-1, -4])]"));
}

#[test]
fn dt_case_split_declines_unsound_shapes() {
    // Fail-closed guarantees: emit ONLY when both `ite` branches are refutable.
    use ay_frontend::command::Term as PTerm;
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    let ctors = vec!["cons".to_string(), "nil".to_string()];
    let decls: Vec<(String, Vec<String>)> = vec![("Lst".to_string(), ctors.clone())];

    // A branch that is a FRESH variable (not occurring in K, not a constructor)
    // makes `cons F = y` genuinely SAT — decline.
    let sat = vec![app(
        "=",
        vec![
            app("cons", vec![sym("F")]),
            app("ite", vec![sym("b"), sym("F"), sym("y")]),
        ],
    )];
    assert!(emit_dt_case_split_firewall_lean_from_parsed(&sat, &ctors, &decls).is_none());

    // K side is not a constructor application — decline.
    let non_ctor = vec![app(
        "=",
        vec![
            app("f", vec![sym("F")]),
            app("ite", vec![sym("b"), sym("F"), sym("nil")]),
        ],
    )];
    assert!(emit_dt_case_split_firewall_lean_from_parsed(&non_ctor, &ctors, &decls).is_none());

    // distinct-disjunction WITHOUT the asserted tester — the `lf = x` disjunct is
    // not refutable (x could genuinely be lf) — decline.
    let no_tester = vec![app(
        "not",
        vec![app(
            "distinct",
            vec![app("nd", vec![sym("y"), sym("x")]), sym("lf"), sym("x")],
        )],
    )];
    let tree_decls: Vec<(String, Vec<String>)> =
        vec![("Tree".to_string(), vec!["lf".to_string(), "nd".to_string()])];
    let tree_ctors = vec!["lf".to_string(), "nd".to_string()];
    assert!(
        emit_dt_case_split_firewall_lean_from_parsed(&no_tester, &tree_ctors, &tree_decls)
            .is_none()
    );
}

#[test]
fn emits_dt_enum_cardinality_from_parsed() {
    // bench `soundness_qf_dt_derived_terms/bug3_enum_card_ite_distinct.smt2`:
    //   (declare-datatypes ((Enum 0)) (((c0) (c1) (c2))))
    //   (declare-fun f (Enum) Enum)
    //   (assert (distinct (ite p v1 v2) (f a) a b))
    // 4 distinct Enum terms over a 3-element enum — pigeonhole (4 > 3).
    use ay_frontend::command::Term as PTerm;
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    // symbol -> result sort: every distinct arg resolves to `Enum`.
    let sym_sorts: Vec<(String, String)> = ["v1", "v2", "a", "b", "f"]
        .iter()
        .map(|n| (n.to_string(), "Enum".to_string()))
        .collect();
    let enum_datatypes: Vec<(String, usize)> = vec![("Enum".to_string(), 3)];
    let parsed = vec![app(
        "distinct",
        vec![
            app("ite", vec![sym("p"), sym("v1"), sym("v2")]),
            app("f", vec![sym("a")]),
            sym("a"),
            sym("b"),
        ],
    )];
    let lean =
        emit_dt_enum_cardinality_firewall_lean_from_parsed(&parsed, &enum_datatypes, &sym_sorts)
            .expect("4-distinct over a 3-enum should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("firewall_combined_unsat"));
    assert!(lean.contains("DtEnumCard_"));
    assert!(lean.contains("| k0 | k1 | k2"));
    assert!(lean.contains("cases x0 <;> cases x1 <;> cases x2 <;> cases x3 <;> decide"));
    // 4 opaque enum vars, 6 pairwise-equality atoms.
    assert!(lean.contains("x3 : EnumK"));
    assert!(lean.contains("[1, 2, 3, 4, 5, 6]"));

    // Enough constructors (4 ≥ 4 args) is NOT a pigeonhole — decline.
    let four_ctor: Vec<(String, usize)> = vec![("Enum".to_string(), 4)];
    assert!(
        emit_dt_enum_cardinality_firewall_lean_from_parsed(&parsed, &four_ctor, &sym_sorts)
            .is_none()
    );

    // An argument whose sort does NOT resolve (unknown symbol) — decline
    // (fail-closed; the common sort could not be pinned).
    let missing_sorts: Vec<(String, String)> = vec![("a".to_string(), "Enum".to_string())];
    assert!(emit_dt_enum_cardinality_firewall_lean_from_parsed(
        &parsed,
        &enum_datatypes,
        &missing_sorts
    )
    .is_none());

    // A non-enum sort (not in the finite-enum table) — decline.
    let mixed_sorts: Vec<(String, String)> = ["v1", "v2", "a", "b", "f"]
        .iter()
        .map(|n| (n.to_string(), "Other".to_string()))
        .collect();
    assert!(emit_dt_enum_cardinality_firewall_lean_from_parsed(
        &parsed,
        &enum_datatypes,
        &mixed_sorts
    )
    .is_none());
}

#[test]
fn emits_dt_f3_from_parsed() {
    // bench `soundness_fuzz_blitz/dt_residual/dt_residual_falsesat_4.smt2`:
    //   (declare-datatypes ((Enum 0) …) (((c0) (c1)) …))
    //   (declare-fun fEnum (Enum) Enum)
    //   (assert (= (fEnum v1) v2))
    //   (assert (distinct (fEnum v1) (fEnum (fEnum v2))))
    // `f³ = f` on the 2-element enum ⟹ `f v1 = v2` forces `f v1 = f (f v2)`,
    // contradicting the disequality.
    use ay_frontend::command::Term as PTerm;
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    // symbol -> result sort: v1, v2 and fEnum's result all inhabit `Enum`.
    let sym_sorts: Vec<(String, String)> = ["v1", "v2", "fEnum"]
        .iter()
        .map(|n| (n.to_string(), "Enum".to_string()))
        .collect();
    let enum_datatypes: Vec<(String, usize)> = vec![("Enum".to_string(), 2)];
    // (= (fEnum v1) v2)
    let pos = app("=", vec![app("fEnum", vec![sym("v1")]), sym("v2")]);
    // (distinct (fEnum v1) (fEnum (fEnum v2)))
    let f_v1 = app("fEnum", vec![sym("v1")]);
    let ff_v2 = app("fEnum", vec![app("fEnum", vec![sym("v2")])]);
    let neg = app("distinct", vec![f_v1, ff_v2]);
    let parsed = vec![pos.clone(), neg.clone()];

    let lean = emit_dt_f3_firewall_lean_from_parsed(&parsed, &enum_datatypes, &sym_sorts)
        .expect("f³=f 2-enum conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("import AySoundness.Datatype"));
    assert!(lean.contains("AySoundness.Datatype.F3.f3_conflict"));
    assert!(lean.contains("AySoundness.Datatype.F3.En"));
    assert!(lean.contains("firewall_combined_unsat"));
    assert!(lean.contains("DtF3_"));
    assert!(lean.contains("[-1, 2]"));

    // Assertion order independence: disequality first.
    let rev = vec![neg.clone(), pos.clone()];
    assert!(emit_dt_f3_firewall_lean_from_parsed(&rev, &enum_datatypes, &sym_sorts).is_some());

    // `(not (= …))` disequality form is also accepted.
    let neg_not = app(
        "not",
        vec![app(
            "=",
            vec![
                app("fEnum", vec![sym("v1")]),
                app("fEnum", vec![app("fEnum", vec![sym("v2")])]),
            ],
        )],
    );
    assert!(emit_dt_f3_firewall_lean_from_parsed(
        &[pos.clone(), neg_not],
        &enum_datatypes,
        &sym_sorts
    )
    .is_some());

    // DECLINE: a 3-constructor enum is not the 2-element F3 shape.
    let three: Vec<(String, usize)> = vec![("Enum".to_string(), 3)];
    assert!(emit_dt_f3_firewall_lean_from_parsed(&parsed, &three, &sym_sorts).is_none());

    // DECLINE: sort not a finite enum (not in the registry).
    let other_sorts: Vec<(String, String)> = ["v1", "v2", "fEnum"]
        .iter()
        .map(|n| (n.to_string(), "Other".to_string()))
        .collect();
    assert!(emit_dt_f3_firewall_lean_from_parsed(&parsed, &enum_datatypes, &other_sorts).is_none());

    // DECLINE: missing the positive equality `(= (fEnum v1) v2)`.
    assert!(emit_dt_f3_firewall_lean_from_parsed(
        std::slice::from_ref(&neg),
        &enum_datatypes,
        &sym_sorts
    )
    .is_none());

    // DECLINE: the disequality is over a DIFFERENT function than the equality
    // (no positive `(= (gEnum v1) v2)` witness exists).
    let sym_sorts_g: Vec<(String, String)> = ["v1", "v2", "fEnum", "gEnum"]
        .iter()
        .map(|n| (n.to_string(), "Enum".to_string()))
        .collect();
    let neg_g = app(
        "distinct",
        vec![
            app("gEnum", vec![sym("v1")]),
            app("gEnum", vec![app("gEnum", vec![sym("v2")])]),
        ],
    );
    assert!(
        emit_dt_f3_firewall_lean_from_parsed(&[pos, neg_g], &enum_datatypes, &sym_sorts_g)
            .is_none()
    );
}

#[test]
fn emits_dt_tester_casesplit_occurs_from_parsed() {
    // bench `soundness_qf_dt_derived_terms/fuzz_dt_falsesat_800.smt2`:
    //   (assert (= v7 (cons v11 (ite ((_ is none) v6)
    //                                (ite v13 v8 (cons v11 v7))
    //                                (ite v13 v8 v7)))))
    //   (assert (not (and v13 true)))
    // Assert-2 forces v13 = false, collapsing the inner ites to `(cons v11 v7)`
    // and `v7`. Residual `v7 = cons v11 (ite (is-none v6) (cons v11 v7) v7)`:
    // both branches occurs-check v7 (depth 2 then-branch, depth 1 else-branch).
    use ay_frontend::command::{Constant as PConst, Index as PIndex, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    let tester = |c: &str, on: PTerm| {
        PTerm::IndexedApp(
            "is".to_string(),
            vec![PIndex::Symbol(c.to_string())],
            vec![on],
        )
    };
    let tru = PTerm::Const(PConst::True);
    let ctors = vec![
        "c0".to_string(),
        "c1".to_string(),
        "none".to_string(),
        "some".to_string(),
        "cons".to_string(),
        "nil".to_string(),
        "leaf".to_string(),
        "node".to_string(),
        "mkRec".to_string(),
    ];
    let inner_then = app(
        "ite",
        vec![
            sym("v13"),
            sym("v8"),
            app("cons", vec![sym("v11"), sym("v7")]),
        ],
    );
    let inner_else = app("ite", vec![sym("v13"), sym("v8"), sym("v7")]);
    let rhs = app(
        "cons",
        vec![
            sym("v11"),
            app(
                "ite",
                vec![tester("none", sym("v6")), inner_then, inner_else],
            ),
        ],
    );
    let parsed = vec![
        app("=", vec![sym("v7"), rhs]),
        app("not", vec![app("and", vec![sym("v13"), tru])]),
    ];
    let lean = emit_dt_tester_casesplit_occurs_firewall_lean_from_parsed(&parsed, &ctors)
        .expect("forced-unit + tester-guard both-occurs case split should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("import AySoundness.Datatype"));
    assert!(lean.contains("firewall_combined_unsat"));
    assert!(lean.contains("DtTesterCaseSplit_"));
    assert!(lean.contains("cases hg : m.g"));
    assert!(lean.contains("acyclic_conflict_generic"));
    // then-branch depth 2, else-branch depth 1.
    assert!(lean.contains("def ctxT (z : DtT) : DtT := DtT.wrap (DtT.wrap (z))"));
    assert!(lean.contains("def ctxF (z : DtT) : DtT := DtT.wrap (z)"));

    // WITHOUT the forcing unit assertion the inner ites do not collapse (a stray
    // `ite v13 …` remains inside a branch), so the residual is NOT both-occurs —
    // decline (fail-closed).
    let no_force = vec![parsed[0].clone()];
    assert!(emit_dt_tester_casesplit_occurs_firewall_lean_from_parsed(&no_force, &ctors).is_none());
}

#[test]
fn emits_dt_tester_casesplit_mixed_from_parsed() {
    // bench `soundness_fuzz_blitz/dt_residual/dt_residual_falsesat_2.smt2`:
    //   (assert (= (ite ((_ is none) v6)
    //                   (node (node v12 v3 (leaf v1)) (mkRec v14 v16) (ite false (leaf v2) v11))
    //                   (ite (and false true) (ite v16 v12 v12) v11))
    //              (node v11 (nv (ite false (leaf v1) v12)) (leaf v2))))
    // All guards fold: `(ite false (leaf v2) v11) → v11`, `(and false true) → false`
    // so the ELSE `(ite false … v11) → v11`, and `(nv (ite false … v12)) → nv v12`.
    // Residual `(ite (is-none v6) THEN v11) = node(v11, nv v12, leaf v2)`, with
    //   THEN = node(node(v12,·,leaf v1), mkRec.., v11):
    //   * g = false (else): `v11 = node(v11, …)` → ACYCLICITY occurs-check (depth 1);
    //   * g = true  (then): `THEN = node(v11, …)`; node_inj → node(v12,·,leaf v1)=v11
    //     and v11=leaf v2 → node = leaf DISTINCTNESS. MIXED (a lemma per branch).
    use ay_frontend::command::{Constant as PConst, Index as PIndex, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    let tester = |c: &str, on: PTerm| {
        PTerm::IndexedApp(
            "is".to_string(),
            vec![PIndex::Symbol(c.to_string())],
            vec![on],
        )
    };
    let fls = PTerm::Const(PConst::False);
    let tru = PTerm::Const(PConst::True);
    let ctors = vec![
        "c0".to_string(),
        "c1".to_string(),
        "mkRec".to_string(),
        "none".to_string(),
        "some".to_string(),
        "cons".to_string(),
        "nil".to_string(),
        "leaf".to_string(),
        "node".to_string(),
    ];
    // Per-constructor recursive-field masks (`true` at a field of the datatype's
    // own sort). `Tree`: leaf(lv Enum) → [false]; node(left Tree)(nv Rec)(right
    // Tree) → [true,false,true].
    let ctor_rec: Vec<(String, Vec<bool>)> = vec![
        ("c0".to_string(), vec![]),
        ("c1".to_string(), vec![]),
        ("mkRec".to_string(), vec![false, false]),
        ("none".to_string(), vec![]),
        ("some".to_string(), vec![false]),
        ("cons".to_string(), vec![false, true]),
        ("nil".to_string(), vec![]),
        ("leaf".to_string(), vec![false]),
        ("node".to_string(), vec![true, false, true]),
    ];
    let then_branch = app(
        "node",
        vec![
            app(
                "node",
                vec![sym("v12"), sym("v3"), app("leaf", vec![sym("v1")])],
            ),
            app("mkRec", vec![sym("v14"), sym("v16")]),
            app(
                "ite",
                vec![fls.clone(), app("leaf", vec![sym("v2")]), sym("v11")],
            ),
        ],
    );
    let else_branch = app(
        "ite",
        vec![
            app("and", vec![fls.clone(), tru.clone()]),
            app("ite", vec![sym("v16"), sym("v12"), sym("v12")]),
            sym("v11"),
        ],
    );
    let lhs = app(
        "ite",
        vec![tester("none", sym("v6")), then_branch, else_branch],
    );
    let rhs = app(
        "node",
        vec![
            sym("v11"),
            app(
                "nv",
                vec![app(
                    "ite",
                    vec![fls.clone(), app("leaf", vec![sym("v1")]), sym("v12")],
                )],
            ),
            app("leaf", vec![sym("v2")]),
        ],
    );
    let parsed = vec![app("=", vec![lhs, rhs])];
    let lean = emit_dt_tester_casesplit_mixed_firewall_lean_from_parsed(&parsed, &ctors, &ctor_rec)
        .expect("mixed occurs+distinctness tester-guard case split should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("import AySoundness.Datatype"));
    assert!(lean.contains("firewall_combined_unsat"));
    assert!(lean.contains("DtTesterCaseSplitMixed_"));
    assert!(lean.contains("cases hg : m.g"));
    // else-branch: acyclicity occurs-check via the generic conflict.
    assert!(lean.contains("acyclic_conflict_generic"));
    assert!(lean
        .contains("fun z => AySoundness.Datatype.Tree.node (z) (AySoundness.Datatype.Tree.leaf)"));
    // then-branch: constructor distinctness via node_inj (+ node ≠ leaf).
    assert!(lean.contains("AySoundness.Datatype.Tree.node_inj heq"));
    // two datatype variables (v12 → t0, v11 → t1) plus the opaque guard.
    assert!(lean.contains("t0 : AySoundness.Datatype.Tree"));
    assert!(lean.contains("t1 : AySoundness.Datatype.Tree"));
    assert!(!lean.contains("t2 : AySoundness.Datatype.Tree"));

    // Reversed equality orientation still emits (the ite may be on either side).
    let PTerm::App(_, eqa) = &parsed[0] else {
        unreachable!()
    };
    let rev = vec![app("=", vec![eqa[1].clone(), eqa[0].clone()])];
    assert!(
        emit_dt_tester_casesplit_mixed_firewall_lean_from_parsed(&rev, &ctors, &ctor_rec).is_some()
    );
}

#[test]
fn declines_dt_tester_casesplit_mixed_selector_guarded() {
    // bench `soundness_qf_dt_derived_terms/fuzz_ufdt_falsesat_881.smt2` (assert1):
    //   (= v12 (node (right (ite v17 v12 (node v13 (mkRec v18 (gE v15)) v12)))
    //                v5 (left (node v13 v5 v13))))
    // The `ite` sits UNDER a `right(…)` selector (not at the top of a side), and
    // the top-level shape is `v12 = node(…)` (a bare variable, not a tester-guarded
    // `ite`). The selector blocks the binary-`Tree` abstraction → DECLINE (None),
    // fail-closed (this residual needs a nested by_cases + distinct-with-duplicate
    // reflexivity not covered by the occurs+distinct mixed render).
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    let ctors = vec![
        "mkRec".to_string(),
        "leaf".to_string(),
        "node".to_string(),
        "none".to_string(),
        "some".to_string(),
    ];
    let ctor_rec: Vec<(String, Vec<bool>)> = vec![
        ("mkRec".to_string(), vec![false, false]),
        ("leaf".to_string(), vec![false]),
        ("node".to_string(), vec![true, false, true]),
        ("none".to_string(), vec![]),
        ("some".to_string(), vec![false]),
    ];
    let inner_node = app(
        "node",
        vec![
            sym("v13"),
            app("mkRec", vec![sym("v18"), app("gE", vec![sym("v15")])]),
            sym("v12"),
        ],
    );
    let rhs = app(
        "node",
        vec![
            app(
                "right",
                vec![app("ite", vec![sym("v17"), sym("v12"), inner_node])],
            ),
            sym("v5"),
            app(
                "left",
                vec![app("node", vec![sym("v13"), sym("v5"), sym("v13")])],
            ),
        ],
    );
    let _ = PConst::True;
    let parsed = vec![app("=", vec![sym("v12"), rhs])];
    assert!(
        emit_dt_tester_casesplit_mixed_firewall_lean_from_parsed(&parsed, &ctors, &ctor_rec)
            .is_none()
    );
}

#[test]
fn emits_dt_nested_selector_casesplit_from_parsed() {
    // bench `soundness_qf_dt_derived_terms/fuzz_ufdt_falsesat_881.smt2` — the LAST
    // uncovered datatype file. Two residual assertions:
    //   assert1: (= v12 (node (right (ite v17 v12 (node v13 (mkRec v18 (gE v15)) v12)))
    //                         v5 (left (node v13 v5 v13))))
    //   assert2: (or (and (not v18) (not v17))
    //                (distinct (right v12)
    //                          (ite false v13 (node (leaf v2) (mkRec v18 v15) v13))
    //                          (ite v18 v12 v13) v12))
    // jointly UNSAT via a nested by_cases (v17 occurs-check / v17=true forces
    // v12=node v13 v13 then inner v18 distinct-with-duplicate). Fail-closed
    // elsewhere; the kernel-checked proof carries axioms ⊆ {propext, Quot.sound}.
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    let fls = PTerm::Const(PConst::False);

    let ctor_rec: Vec<(String, Vec<bool>)> = vec![
        ("mkRec".to_string(), vec![false, false]),
        ("leaf".to_string(), vec![false]),
        ("node".to_string(), vec![true, false, true]),
        ("none".to_string(), vec![]),
        ("some".to_string(), vec![false]),
    ];
    let ctor_selectors: Vec<(String, Vec<String>)> = vec![
        (
            "mkRec".to_string(),
            vec!["rs0".to_string(), "rs1".to_string()],
        ),
        ("leaf".to_string(), vec!["lv".to_string()]),
        (
            "node".to_string(),
            vec!["left".to_string(), "nv".to_string(), "right".to_string()],
        ),
        ("some".to_string(), vec!["val".to_string()]),
    ];

    // assert1
    let inner_node = app(
        "node",
        vec![
            sym("v13"),
            app("mkRec", vec![sym("v18"), app("gE", vec![sym("v15")])]),
            sym("v12"),
        ],
    );
    let a1_rhs = app(
        "node",
        vec![
            app(
                "right",
                vec![app("ite", vec![sym("v17"), sym("v12"), inner_node])],
            ),
            sym("v5"),
            app(
                "left",
                vec![app("node", vec![sym("v13"), sym("v5"), sym("v13")])],
            ),
        ],
    );
    let assert1 = app("=", vec![sym("v12"), a1_rhs]);

    // assert2
    let distinct = app(
        "distinct",
        vec![
            app("right", vec![sym("v12")]),
            app(
                "ite",
                vec![
                    fls.clone(),
                    sym("v13"),
                    app(
                        "node",
                        vec![
                            app("leaf", vec![sym("v2")]),
                            app("mkRec", vec![sym("v18"), sym("v15")]),
                            sym("v13"),
                        ],
                    ),
                ],
            ),
            app("ite", vec![sym("v18"), sym("v12"), sym("v13")]),
            sym("v12"),
        ],
    );
    let assert2 = app(
        "or",
        vec![
            app(
                "and",
                vec![app("not", vec![sym("v18")]), app("not", vec![sym("v17")])],
            ),
            distinct,
        ],
    );

    let parsed = vec![assert1, assert2];
    let lean = emit_dt_nested_selector_casesplit_firewall_lean_from_parsed(
        &parsed,
        &ctor_rec,
        &ctor_selectors,
    )
    .expect("nested selector-guarded datatype case split should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("import AySoundness.Datatype"));
    assert!(lean.contains("firewall_combined_unsat"));
    assert!(lean.contains("DtNestedSelectorCaseSplit_"));
    // outer split (v17) + acyclicity occurs-check branch.
    assert!(lean.contains("cases hv17 : m.v17"));
    assert!(lean.contains("AySoundness.Datatype.Tree.acyclic_l"));
    // inner split (v18) + distinct-with-duplicate.
    assert!(lean.contains("cases hv18 : m.v18"));
    assert!(lean.contains("distinct4"));
    assert!(lean.contains("axioms ⊆ {propext, Quot.sound}"));

    // Reversed equality orientation still emits (the variable may be on either side).
    let PTerm::App(_, eqa) = &parsed[0] else {
        unreachable!()
    };
    let rev1 = app("=", vec![eqa[1].clone(), eqa[0].clone()]);
    let rev = vec![rev1, parsed[1].clone()];
    assert!(emit_dt_nested_selector_casesplit_firewall_lean_from_parsed(
        &rev,
        &ctor_rec,
        &ctor_selectors
    )
    .is_some());

    // Fail-closed: dropping the `distinct` disjunct (assert2 becomes a lone `and`)
    // no longer matches the template.
    let no_or = vec![
        parsed[0].clone(),
        app(
            "and",
            vec![app("not", vec![sym("v18")]), app("not", vec![sym("v17")])],
        ),
    ];
    assert!(emit_dt_nested_selector_casesplit_firewall_lean_from_parsed(
        &no_or,
        &ctor_rec,
        &ctor_selectors
    )
    .is_none());
}

// ---------------------------------------------------------------------------
// `str.at` / `seq.at` / `seq.nth` positional-read firewall emitters.
// ---------------------------------------------------------------------------

#[test]
fn emits_str_at_len_from_parsed_assertions() {
    // str_at_len_symbolic_arrayselect_false_sat.smt2 /
    // xt_strat_len_false_sat.smt2: (= (str.len (str.at t (select a i))) 3).
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));

    let strat = app(
        "str.at",
        vec![sym("t"), app("select", vec![sym("a"), sym("i")])],
    );
    let parsed = vec![
        app("=", vec![app("str.len", vec![strat]), num("3")]),
        // red herring (irrelevant array assert)
        app("=", vec![app("select", vec![sym("a"), num("5")]), num("3")]),
    ];
    let lean = emit_str_at_len_firewall_lean_from_parsed(&parsed)
        .expect("str.at length conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    for needle in [
        "import AySoundness.StringThy",
        "namespace AySoundness.Emitted.StrAtLen_",
        "StrAt.strAt m.1 m.2",
        "StrAt.strAt_len_eq_conflict m.1 m.2 3 (by decide)",
        "firewall_combined_unsat",
    ] {
        assert!(lean.contains(needle), "emitted Lean missing: {needle}");
    }

    // N = 1 is within the (verified) bound — no conflict, decline.
    let sat = vec![app(
        "=",
        vec![
            app("str.len", vec![app("str.at", vec![sym("t"), num("0")])]),
            num("1"),
        ],
    )];
    assert!(emit_str_at_len_firewall_lean_from_parsed(&sat).is_none());
}

#[test]
fn emits_seq_at_pinned_from_parsed_assertions() {
    // qf_slia_seqat_symbolic_pinned_false_sat.smt2: s1=[3,-2,3], n0=1,
    // (= (seq.unit 1) (seq.at s1 n0)) — read is -2, so 1 ≠ -2.
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let unit = |v: PTerm| app("seq.unit", vec![v]);

    let parsed = vec![
        app(
            "=",
            vec![
                sym("s1"),
                app(
                    "seq.++",
                    vec![unit(num("3")), unit(sym("-2")), unit(num("3"))],
                ),
            ],
        ),
        app("=", vec![sym("n0"), num("1")]),
        app(
            "=",
            vec![unit(num("1")), app("seq.at", vec![sym("s1"), sym("n0")])],
        ),
        app("=", vec![sym("s0"), sym("s1")]),
    ];
    let lean = emit_seq_at_pinned_firewall_lean_from_parsed(&parsed)
        .expect("ground seq.at value mismatch should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    for needle in [
        "import AySoundness.SeqThy",
        "namespace AySoundness.Emitted.SeqAtPinned_",
        "SeqThy.unit (1 : Int)",
        "SeqThy.seqAt (([3, -2, 3]) : SeqThy.Seq Int) 1",
        "cases m <;> decide",
        "firewall_combined_unsat",
    ] {
        assert!(lean.contains(needle), "emitted Lean missing: {needle}");
    }

    // Matching value (read == unit) is NOT a conflict — decline.
    let sat = vec![
        app(
            "=",
            vec![
                sym("s1"),
                app("seq.++", vec![unit(num("3")), unit(num("9"))]),
            ],
        ),
        app("=", vec![sym("n0"), num("1")]),
        app(
            "=",
            vec![unit(num("9")), app("seq.at", vec![sym("s1"), sym("n0")])],
        ),
    ];
    assert!(emit_seq_at_pinned_firewall_lean_from_parsed(&sat).is_none());
}

#[test]
fn emits_seq_suffixof_from_parsed_assertions() {
    // seq_falsesat_suffixof_elem_mismatch.smt2: v1=[1], v2=[-1,-1],
    // (seq.suffixof v2 (seq.++ v3 v1)) — [-1,-1] ends in -1, v3++[1] ends in 1.
    use ay_frontend::command::Term as PTerm;
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    let unit = |v: &str| app("seq.unit", vec![sym(v)]);

    let parsed = vec![
        app("=", vec![sym("v1"), unit("1")]),
        app(
            "=",
            vec![sym("v2"), app("seq.++", vec![unit("-1"), unit("-1")])],
        ),
        app(
            "seq.suffixof",
            vec![sym("v2"), app("seq.++", vec![sym("v3"), sym("v1")])],
        ),
    ];
    let lean = emit_seq_suffixof_firewall_lean_from_parsed(&parsed)
        .expect("seq.suffixof last-element mismatch should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    for needle in [
        "import AySoundness.SeqThy",
        "namespace AySoundness.Emitted.SeqSuffixof_",
        "SeqThy.suffix_append_last_conflict",
        "SeqThy.suffixOf (([-1, -1]) : List Int) (p ++ (([1]) : List Int))",
        "theorem no_model (p : List Int)",
        "(-1) (1) h",
    ] {
        assert!(lean.contains(needle), "emitted Lean missing: {needle}");
    }

    // Matching last element (a == b) is NOT a conflict — decline.
    let sat = vec![
        app("=", vec![sym("v1"), unit("1")]),
        app(
            "=",
            vec![sym("v2"), app("seq.++", vec![unit("-1"), unit("1")])],
        ),
        app(
            "seq.suffixof",
            vec![sym("v2"), app("seq.++", vec![sym("v3"), sym("v1")])],
        ),
    ];
    assert!(emit_seq_suffixof_firewall_lean_from_parsed(&sat).is_none());
}

#[test]
fn emits_seq_extract_oob_replace_from_parsed_assertions() {
    // qf_slia_seqextract_oob_false_sat.smt2:
    // (= (seq.replace s0 (seq.extract (seq.unit 2) 1 n1) (seq.unit (- 0 2)))
    //    (seq.++ (seq.unit 0) (seq.unit 1)))
    // extract [2] at offset 1 is OOB (len [2] = 1 ≤ 1) → empty needle; replace
    // then prepends [-2] (head -2), but the whole [0,1] has head 0.
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let unit = |v: PTerm| app("seq.unit", vec![v]);

    let extract = app("seq.extract", vec![unit(num("2")), num("1"), sym("n1")]);
    let replace = app(
        "seq.replace",
        vec![sym("s0"), extract, unit(app("-", vec![num("0"), num("2")]))],
    );
    let whole = app("seq.++", vec![unit(num("0")), unit(num("1"))]);
    let parsed = vec![app("=", vec![replace, whole])];

    let lean = emit_seq_extract_oob_replace_firewall_lean_from_parsed(&parsed)
        .expect("OOB seq.extract / empty-needle seq.replace conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    for needle in [
        "import AySoundness.SeqThy",
        "namespace AySoundness.Emitted.SeqExtractOobReplace_",
        "SeqThy.seqExtract_oob (([2]) : SeqThy.Seq Int) 1 n (by decide)",
        "theorem needle_empty (n : Nat)",
        "SeqThy.seqReplaceEmpty s0 (([-2]) : SeqThy.Seq Int)",
        "SeqThy.seqReplaceEmpty_head s0 (([-2]) : SeqThy.Seq Int) (-2) (by decide)",
        "theorem no_model (s0 : SeqThy.Seq Int)",
        "(([0, 1]) : SeqThy.Seq Int)",
    ] {
        assert!(lean.contains(needle), "emitted Lean missing: {needle}");
    }

    // Matching head (replacement head == whole head) is NOT a conflict — decline.
    let sat_extract = app("seq.extract", vec![unit(num("2")), num("1"), sym("n1")]);
    let sat = vec![app(
        "=",
        vec![
            app("seq.replace", vec![sym("s0"), sat_extract, unit(num("0"))]),
            app("seq.++", vec![unit(num("0")), unit(num("1"))]),
        ],
    )];
    assert!(emit_seq_extract_oob_replace_firewall_lean_from_parsed(&sat).is_none());

    // IN-BOUNDS extract offset (0 < len [2]) — the needle may be non-empty, so the
    // empty-needle prepend model does not apply — decline (fail-closed).
    let ib_extract = app("seq.extract", vec![unit(num("2")), num("0"), sym("n1")]);
    let in_bounds = vec![app(
        "=",
        vec![
            app(
                "seq.replace",
                vec![
                    sym("s0"),
                    ib_extract,
                    unit(app("-", vec![num("0"), num("2")])),
                ],
            ),
            app("seq.++", vec![unit(num("0")), unit(num("1"))]),
        ],
    )];
    assert!(emit_seq_extract_oob_replace_firewall_lean_from_parsed(&in_bounds).is_none());
}

#[test]
fn emits_seq_nth_ground_lia_from_parsed_assertions() {
    // seq_falsesat_nth_ground_eval.smt2: v2=[0], v10=0,
    // (and (>= (- -3 4) (seq.nth v2 v10)) (not (<= v7 3))) — -7 >= 0 is false.
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));

    let parsed = vec![
        app("=", vec![sym("v2"), app("seq.unit", vec![num("0")])]),
        app("=", vec![sym("v10"), num("0")]),
        app(
            "and",
            vec![
                app(
                    ">=",
                    vec![
                        app("-", vec![sym("-3"), num("4")]),
                        app("seq.nth", vec![sym("v2"), sym("v10")]),
                    ],
                ),
                app("not", vec![app("<=", vec![sym("v7"), num("3")])]),
            ],
        ),
    ];
    let lean = emit_seq_nth_ground_lia_firewall_lean_from_parsed(&parsed)
        .expect("ground seq.nth + LIA conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    for needle in [
        "import AySoundness.SeqThy",
        "namespace AySoundness.Emitted.SeqNthLia_",
        "SeqThy.nthD (([0]) : SeqThy.Seq Int) 0 (0 : Int)",
        "(-7 : Int) ≥",
        "firewall_combined_unsat",
    ] {
        assert!(lean.contains(needle), "emitted Lean missing: {needle}");
    }

    // A TRUE comparison (0 >= -7) is no conflict — decline.
    let sat = vec![
        app("=", vec![sym("v2"), app("seq.unit", vec![num("0")])]),
        app("=", vec![sym("v10"), num("0")]),
        app(
            ">=",
            vec![
                app("seq.nth", vec![sym("v2"), sym("v10")]),
                app("-", vec![sym("-3"), num("4")]),
            ],
        ),
    ];
    assert!(emit_seq_nth_ground_lia_firewall_lean_from_parsed(&sat).is_none());
}

#[test]
fn emits_seq_at_ite_from_parsed_assertions() {
    // seq_falsesat_iteofseq_eq_operand.smt2: v1=[false,false], v3=empty,
    // (= (seq.at v1 0) (ite C (seq.unit true) (seq.++ v3 empty empty))).
    use ay_frontend::command::{
        Constant as PConst, QualifiedIdentifier, Sort as FSort, Term as PTerm,
    };
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let fls = || PTerm::Const(PConst::False);
    let tru = || PTerm::Const(PConst::True);
    let unit = |v: PTerm| app("seq.unit", vec![v]);
    let seq_bool = FSort::Parameterized("Seq".to_string(), vec![FSort::Simple("Bool".to_string())]);
    let empty = || {
        PTerm::QualifiedApp(
            QualifiedIdentifier::Symbol("seq.empty".to_string()),
            seq_bool.clone(),
            vec![],
        )
    };

    // Abstract OOB condition (never evaluated).
    let cond = app("seq.nth", vec![unit(sym("v5")), sym("-3")]);
    let parsed = vec![
        app(
            "=",
            vec![sym("v1"), app("seq.++", vec![unit(fls()), unit(fls())])],
        ),
        app("=", vec![sym("v3"), empty()]),
        app(
            "=",
            vec![
                app("seq.at", vec![sym("v1"), num("0")]),
                app(
                    "ite",
                    vec![
                        cond,
                        unit(tru()),
                        app("seq.++", vec![sym("v3"), empty(), empty()]),
                    ],
                ),
            ],
        ),
    ];
    let lean = emit_seq_at_ite_firewall_lean_from_parsed(&parsed)
        .expect("bounded seq.at-vs-ite conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    for needle in [
        "import AySoundness.SeqThy",
        "namespace AySoundness.Emitted.SeqAtIte_",
        "SeqThy.seqAt (([false, false]) : SeqThy.Seq Bool) 0",
        "bif m then (([true]) : SeqThy.Seq Bool) else (([]) : SeqThy.Seq Bool)",
        "cases m <;> decide",
        "firewall_combined_unsat",
    ] {
        assert!(lean.contains(needle), "emitted Lean missing: {needle}");
    }

    // If the true branch MATCHES the read ([false]), a c=true model satisfies it
    // — decline.
    let sat = vec![
        app(
            "=",
            vec![sym("v1"), app("seq.++", vec![unit(fls()), unit(fls())])],
        ),
        app("=", vec![sym("v3"), empty()]),
        app(
            "=",
            vec![
                app("seq.at", vec![sym("v1"), num("0")]),
                app(
                    "ite",
                    vec![
                        sym("c"),
                        unit(fls()),
                        app("seq.++", vec![sym("v3"), empty()]),
                    ],
                ),
            ],
        ),
    ];
    assert!(emit_seq_at_ite_firewall_lean_from_parsed(&sat).is_none());
}

#[test]
fn emits_str_indexof_absent_ge_from_parsed_assertions() {
    // xt_indexof_symstart_false_sat.smt2:
    //   (assert (>= (str.indexof "a" "ca" n) 0))
    // needle "ca" = [99, 97] is longer than haystack "a" = [97], so it is ABSENT
    // → str.indexof = -1 for every start, and -1 ≥ 0 is false.
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let sstr = |s: &str| PTerm::Const(PConst::String(s.to_string()));

    let idx = app("str.indexof", vec![sstr("a"), sstr("ca"), sym("n")]);
    let parsed = vec![app(">=", vec![idx, num("0")])];

    let lean = emit_str_indexof_absent_ge_firewall_lean_from_parsed(
        &parsed,
        MAX_INDEXOF_FIREWALL_SOURCE_BYTES,
    )
    .expect("bounded emission should not hit its resource fence")
    .expect("str.indexof absent ≥ 0 conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    for needle in [
        "import AySoundness.StringThy",
        "namespace AySoundness.Emitted.StrIndexofAbsentGe_",
        "IndexOfThy.indexOf [97] [99, 97] m",
        "IndexOfThy.indexOf_absent_all_start [97] [99, 97] (by decide) m",
        "firewall_combined_unsat",
        "#print axioms no_model",
    ] {
        assert!(lean.contains(needle), "emitted Lean missing: {needle}");
    }
    // The closing of `indexOf … = -1` must NOT go through `simp` (it would leak
    // Classical.choice): the only `simp only` touches `atomVal`/`h1`, never the
    // raw `indexOf`.
    assert!(
        !lean.contains("simp only [atomVal, decide_eq_false_iff_not]"),
        "must not reduce indexOf via simp"
    );

    // A PRESENT needle (needle occurs in the haystack) is NOT a conflict — decline.
    let present = vec![app(
        ">=",
        vec![
            app("str.indexof", vec![sstr("ca"), sstr("ca"), sym("n")]),
            num("0"),
        ],
    )];
    assert!(matches!(
        emit_str_indexof_absent_ge_firewall_lean_from_parsed(
            &present,
            MAX_INDEXOF_FIREWALL_SOURCE_BYTES,
        ),
        Ok(None)
    ));

    // `(>= 0 (str.indexof …))` (operand order flipped ⇒ 0 ≥ -1 is TRUE) — decline.
    let flipped = vec![app(
        ">=",
        vec![
            num("0"),
            app("str.indexof", vec![sstr("a"), sstr("ca"), sym("n")]),
        ],
    )];
    assert!(matches!(
        emit_str_indexof_absent_ge_firewall_lean_from_parsed(
            &flipped,
            MAX_INDEXOF_FIREWALL_SOURCE_BYTES,
        ),
        Ok(None)
    ));
}

#[test]
fn emits_str_indexof_is_digit_from_parsed_assertions() {
    // str_indexof_transitive_alias_false_sat.smt2:
    //   (assert (= v "cba")) (assert (= w "aba")) (assert (= v t))
    //   (assert (str.is_digit (str.from_int (str.indexof t w k))))
    // t aliases "cba", w = "aba"; "aba" is ABSENT from "cba" → str.indexof = -1,
    // str.from_int(-1) = "", str.is_digit("") = false.
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    let sstr = |s: &str| PTerm::Const(PConst::String(s.to_string()));

    let is_digit = app(
        "str.is_digit",
        vec![app(
            "str.from_int",
            vec![app("str.indexof", vec![sym("t"), sym("w"), sym("k")])],
        )],
    );
    let parsed = vec![
        app("=", vec![sym("v"), sstr("cba")]),
        app("=", vec![sym("w"), sstr("aba")]),
        app("=", vec![sym("v"), sym("t")]),
        is_digit,
    ];

    let lean = emit_str_indexof_is_digit_firewall_lean_from_parsed(
        &parsed,
        MAX_INDEXOF_FIREWALL_SOURCE_BYTES,
    )
    .expect("bounded emission should not hit its resource fence")
    .expect("str.indexof absent is_digit conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    for needle in [
        "import AySoundness.StringThy",
        "namespace AySoundness.Emitted.StrIndexofIsDigit_",
        "IndexOfThy.isDigit (IndexOfThy.fromInt (IndexOfThy.indexOf [99, 98, 97] [97, 98, 97] m))",
        "IndexOfThy.indexOf_absent_all_start [99, 98, 97] [97, 98, 97] (by decide) m",
        "firewall_combined_unsat",
        "#print axioms no_model",
    ] {
        assert!(lean.contains(needle), "emitted Lean missing: {needle}");
    }

    // A PRESENT needle (e.g. "aba" IS a substring of "aba") is no conflict — the
    // index is 0, str.from_int 0 = "0", str.is_digit "0" = true — decline.
    let present = vec![app(
        "str.is_digit",
        vec![app(
            "str.from_int",
            vec![app("str.indexof", vec![sstr("aba"), sstr("aba"), sym("k")])],
        )],
    )];
    assert!(matches!(
        emit_str_indexof_is_digit_firewall_lean_from_parsed(
            &present,
            MAX_INDEXOF_FIREWALL_SOURCE_BYTES,
        ),
        Ok(None)
    ));

    // Un-aliased needle (t never bound to a ground literal) — not ground — decline.
    let ungrounded = vec![app(
        "str.is_digit",
        vec![app(
            "str.from_int",
            vec![app("str.indexof", vec![sym("t"), sym("w"), sym("k")])],
        )],
    )];
    assert!(matches!(
        emit_str_indexof_is_digit_firewall_lean_from_parsed(
            &ungrounded,
            MAX_INDEXOF_FIREWALL_SOURCE_BYTES,
        ),
        Ok(None)
    ));
}

#[test]
fn str_indexof_alias_resolution_is_linearithmic_and_bounded() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    use std::time::{Duration, Instant};

    let sym = |s: String| PTerm::Symbol(s);
    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    // Reverse propagation is the old fixpoint implementation's worst case:
    // the literal at s9999 made only one earlier symbol ground per full pass.
    let mut parsed = Vec::with_capacity(MAX_INDEXOF_ALIAS_ASSERTIONS);
    for index in 0..(MAX_INDEXOF_ALIAS_ASSERTIONS - 1) {
        parsed.push(app(
            "=",
            vec![sym(format!("s{index}")), sym(format!("s{}", index + 1))],
        ));
    }
    parsed.push(app(
        "=",
        vec![
            sym(format!("s{}", MAX_INDEXOF_ALIAS_ASSERTIONS - 1)),
            PTerm::Const(PConst::String("ground".to_string())),
        ],
    ));

    let started = Instant::now();
    let binds = collect_str_binds(&parsed).expect("at-cap alias graph must resolve");
    let elapsed = started.elapsed();
    assert_eq!(binds.len(), MAX_INDEXOF_ALIAS_ASSERTIONS);
    assert_eq!(binds.get("s0"), Some(&"ground"));
    assert!(
        elapsed < Duration::from_secs(5),
        "10k reverse alias chain took {elapsed:?}"
    );

    parsed.push(app(
        "=",
        vec![sym("extra".to_string()), sym("s0".to_string())],
    ));
    assert!(
        collect_str_binds(&parsed).is_none(),
        "over-cap explicit emission must decline before graph construction"
    );
}

#[test]
fn str_indexof_substring_search_and_rendering_are_resource_bounded() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    use std::time::{Duration, Instant};

    let prefix = "a".repeat(125_000);
    let absent_needle = format!("{prefix}b");
    let absent_hay = "a".repeat(250_000);
    let present_hay = format!("{absent_hay}b");
    let started = Instant::now();
    assert_eq!(needle_absent(&absent_hay, &absent_needle), Some(true));
    assert_eq!(needle_absent(&present_hay, &absent_needle), Some(false));
    assert_eq!(needle_absent("abc", ""), Some(false));
    assert_eq!(needle_absent("x🙂éy", "🙂é"), Some(false));
    // The UTF-8 encodings of `é` (c3 a9) and `©` (c2 a9) share a trailing
    // continuation byte. That byte overlap is not a codepoint match.
    assert_eq!(needle_absent("é", "©"), Some(true));
    assert_eq!(needle_absent("🙂", ""), Some(false));
    let elapsed = started.elapsed();
    assert!(
        elapsed < Duration::from_secs(5),
        "linear no-allocation substring ratchet took {elapsed:?}"
    );
    assert_eq!(
        needle_absent(&"a".repeat(MAX_INDEXOF_LITERAL_BYTES), "b"),
        None,
        "checked work cap must reject before substring search"
    );

    let app = |o: &str, a: Vec<PTerm>| PTerm::App(o.to_string(), a);
    let oversized_hay = "a".repeat(MAX_INDEXOF_LITERAL_BYTES - 1);
    let parsed = vec![app(
        ">=",
        vec![
            app(
                "str.indexof",
                vec![
                    PTerm::Const(PConst::String(oversized_hay)),
                    PTerm::Const(PConst::String("b".to_string())),
                    PTerm::Symbol("n".to_string()),
                ],
            ),
            PTerm::Const(PConst::Numeral("0".to_string())),
        ],
    )];
    assert!(
        emit_str_indexof_absent_ge_firewall_lean_from_parsed(
            &parsed,
            MAX_INDEXOF_FIREWALL_SOURCE_BYTES,
        )
        .is_err(),
        "codepoint-list amplification must be declined before rendering"
    );

    let small = vec![app(
        ">=",
        vec![
            app(
                "str.indexof",
                vec![
                    PTerm::Const(PConst::String("a".to_string())),
                    PTerm::Const(PConst::String("b".to_string())),
                    PTerm::Symbol("n".to_string()),
                ],
            ),
            PTerm::Const(PConst::Numeral("0".to_string())),
        ],
    )];
    assert!(
        emit_str_indexof_absent_ge_firewall_lean_from_parsed(
            &small,
            INDEXOF_RENDER_FIXED_RESERVE - 1,
        )
        .is_err(),
        "caller source budget must be checked before collection/rendering"
    );
}

// ---------------------------------------------------------------------------
// QF_AX extensionality / read-over-write / congruence firewall emitters.
// ---------------------------------------------------------------------------

fn ax_sym(s: &str) -> PTerm {
    PTerm::Symbol(s.to_string())
}
fn ax_store(a: PTerm, i: PTerm, v: PTerm) -> PTerm {
    PTerm::App("store".to_string(), vec![a, i, v])
}
fn ax_select(a: PTerm, i: PTerm) -> PTerm {
    PTerm::App("select".to_string(), vec![a, i])
}
fn ax_eq(a: PTerm, b: PTerm) -> PTerm {
    PTerm::App("=".to_string(), vec![a, b])
}
fn ax_neq(a: PTerm, b: PTerm) -> PTerm {
    PTerm::App("not".to_string(), vec![ax_eq(a, b)])
}

#[test]
fn emits_array_write_back_identity_from_parsed() {
    // (not (= (store a i (select a i)) a)) — write_back_identity.smt2.
    let inner = ax_store(
        ax_sym("a"),
        ax_sym("i"),
        ax_select(ax_sym("a"), ax_sym("i")),
    );
    let parsed = vec![ax_neq(inner, ax_sym("a"))];
    let lean = emit_array_write_back_identity_firewall_lean_from_parsed(&parsed)
        .expect("write-back identity should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("theorem no_model"));
    assert!(lean.contains("ArrayThy.ext_nonvacuous"));
    assert!(lean.contains("(fun j => if j = m.i then m.a m.i else m.a j) = m.a"));
    assert!(lean.contains("firewall_combined_unsat"));
}

#[test]
fn array_write_back_declines_wrong_value() {
    // (not (= (store a i (select a j)) a)) — stored value reads a DIFFERENT index,
    // not the write-back identity; decline (fail-closed).
    let inner = ax_store(
        ax_sym("a"),
        ax_sym("i"),
        ax_select(ax_sym("a"), ax_sym("j")),
    );
    let parsed = vec![ax_neq(inner, ax_sym("a"))];
    assert!(emit_array_write_back_identity_firewall_lean_from_parsed(&parsed).is_none());
}

#[test]
fn emits_array_store_eq_select_eq_from_parsed() {
    // (= (store a i v) (store b i w)) ∧ (not (= v w)) — store_eq_implies_select_eq.
    let eqn = ax_eq(
        ax_store(ax_sym("a"), ax_sym("i"), ax_sym("v")),
        ax_store(ax_sym("b"), ax_sym("i"), ax_sym("w")),
    );
    let parsed = vec![eqn, ax_neq(ax_sym("v"), ax_sym("w"))];
    let lean = emit_array_store_eq_select_eq_firewall_lean_from_parsed(&parsed)
        .expect("store-eq ⇒ value-eq should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("theorem no_model"));
    assert!(lean.contains("ArrayThy.sel_upd_same"));
    assert!(lean.contains("decide (m.v = m.w)"));
    assert!(lean.contains("firewall_combined_unsat"));
}

#[test]
fn array_store_eq_select_eq_declines_distinct_index() {
    // (= (store a i v) (store b k w)) ∧ (not (= v w)) — different store indices, so
    // v = w does NOT follow; decline (fail-closed).
    let eqn = ax_eq(
        ax_store(ax_sym("a"), ax_sym("i"), ax_sym("v")),
        ax_store(ax_sym("b"), ax_sym("k"), ax_sym("w")),
    );
    let parsed = vec![eqn, ax_neq(ax_sym("v"), ax_sym("w"))];
    assert!(emit_array_store_eq_select_eq_firewall_lean_from_parsed(&parsed).is_none());
}

#[test]
fn emits_array_store_eq_base_other_from_parsed() {
    // (= (store a i v) (store b i w)), (not (= i j)),
    // (not (= (select a j) (select b j))) — store_eq_implies_base_eq_at_other.
    let eqn = ax_eq(
        ax_store(ax_sym("a"), ax_sym("i"), ax_sym("v")),
        ax_store(ax_sym("b"), ax_sym("i"), ax_sym("w")),
    );
    let sel_diseq = ax_neq(
        ax_select(ax_sym("a"), ax_sym("j")),
        ax_select(ax_sym("b"), ax_sym("j")),
    );
    let parsed = vec![eqn, ax_neq(ax_sym("i"), ax_sym("j")), sel_diseq];
    let lean = emit_array_store_eq_base_other_firewall_lean_from_parsed(&parsed)
        .expect("store-eq ⇒ base-eq at other should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("theorem no_model"));
    assert!(lean.contains("ArrayThy.sel_upd_other"));
    assert!(lean.contains("decide (m.a m.j = m.b m.j)"));
    assert!(lean.contains("firewall_combined_unsat"));
}

#[test]
fn array_store_eq_base_other_declines_without_index_diseq() {
    // Missing the (not (= i j)) guard: select a j = select b j does NOT follow;
    // decline (fail-closed).
    let eqn = ax_eq(
        ax_store(ax_sym("a"), ax_sym("i"), ax_sym("v")),
        ax_store(ax_sym("b"), ax_sym("i"), ax_sym("w")),
    );
    let sel_diseq = ax_neq(
        ax_select(ax_sym("a"), ax_sym("j")),
        ax_select(ax_sym("b"), ax_sym("j")),
    );
    let parsed = vec![eqn, sel_diseq];
    assert!(emit_array_store_eq_base_other_firewall_lean_from_parsed(&parsed).is_none());
}

#[test]
fn emits_array_eq_select_from_parsed() {
    // (= a b) ∧ (not (= (select a i) (select b i))) — array_eq_select.smt2.
    let parsed = vec![
        ax_eq(ax_sym("a"), ax_sym("b")),
        ax_neq(
            ax_select(ax_sym("a"), ax_sym("i")),
            ax_select(ax_sym("b"), ax_sym("i")),
        ),
    ];
    let lean = emit_array_eq_select_firewall_lean_from_parsed(&parsed)
        .expect("array-eq ⇒ select-eq should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("theorem no_model"));
    assert!(lean.contains("decide (m.a m.i = m.b m.i)"));
    assert!(lean.contains("firewall_combined_unsat"));
}

#[test]
fn array_eq_select_declines_without_array_eq() {
    // No (= a b): select a i ≠ select b i is SAT; must NOT emit a refutation.
    let parsed = vec![ax_neq(
        ax_select(ax_sym("a"), ax_sym("i")),
        ax_select(ax_sym("b"), ax_sym("i")),
    )];
    assert!(emit_array_eq_select_firewall_lean_from_parsed(&parsed).is_none());
}

#[test]
fn emits_array_store_congruence_from_parsed() {
    // (= a b) ∧ (not (= (store a i v) (store b i v))) — ext_congruence.smt2.
    let parsed = vec![
        ax_eq(ax_sym("a"), ax_sym("b")),
        ax_neq(
            ax_store(ax_sym("a"), ax_sym("i"), ax_sym("v")),
            ax_store(ax_sym("b"), ax_sym("i"), ax_sym("v")),
        ),
    ];
    let lean = emit_array_store_congruence_firewall_lean_from_parsed(&parsed)
        .expect("array-eq ⇒ store-eq should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("theorem no_model"));
    assert!(lean.contains("(fun j => if j = m.i then m.v else m.a j)"));
    assert!(lean.contains("firewall_combined_unsat"));
}

#[test]
fn array_store_congruence_declines_distinct_value() {
    // (= a b) ∧ (not (= (store a i v) (store b i w))) with v ≠ w: store equality
    // does NOT follow from a = b; decline (fail-closed).
    let parsed = vec![
        ax_eq(ax_sym("a"), ax_sym("b")),
        ax_neq(
            ax_store(ax_sym("a"), ax_sym("i"), ax_sym("v")),
            ax_store(ax_sym("b"), ax_sym("i"), ax_sym("w")),
        ),
    ];
    assert!(emit_array_store_congruence_firewall_lean_from_parsed(&parsed).is_none());
}

#[test]
fn emits_array_eq_chain_row1_from_parsed() {
    // (= a b), (= b (store c i v)), (= c d), (not (= (select a i) v)) —
    // eq_chain_four_arrays.smt2. The chain a = b = store(c,i,v) + ROW-1.
    let parsed = vec![
        ax_eq(ax_sym("a"), ax_sym("b")),
        ax_eq(ax_sym("b"), ax_store(ax_sym("c"), ax_sym("i"), ax_sym("v"))),
        ax_eq(ax_sym("c"), ax_sym("d")),
        ax_neq(ax_select(ax_sym("a"), ax_sym("i")), ax_sym("v")),
    ];
    let lean = emit_array_eq_chain_row1_firewall_lean_from_parsed(&parsed)
        .expect("equality-chain ⇒ ROW-1 should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("theorem no_model"));
    assert!(lean.contains("ArrayThy.sel_upd_same"));
    assert!(lean.contains(".trans"));
    assert!(lean.contains("firewall_combined_unsat"));
}

#[test]
fn array_eq_chain_row1_declines_without_chain() {
    // (not (= (select a i) v)) alone — no equality chain to a store; decline.
    let parsed = vec![ax_neq(ax_select(ax_sym("a"), ax_sym("i")), ax_sym("v"))];
    assert!(emit_array_eq_chain_row1_firewall_lean_from_parsed(&parsed).is_none());
}

// ---- store commutativity (storecomm_*): direct array and read-forwarded ----

#[test]
fn emits_array_store_commute_direct_from_parsed() {
    // storecomm_minimal / storecomm_array_diseq (byte-identical):
    // (not (= i j)),
    // (not (= (store (store a i v) j w) (store (store a j w) i v))).
    // Two orderings of the same two writes; equal by extensionality under i ≠ j.
    let store_l = ax_store(
        ax_store(ax_sym("a"), ax_sym("i"), ax_sym("v")),
        ax_sym("j"),
        ax_sym("w"),
    );
    let store_r = ax_store(
        ax_store(ax_sym("a"), ax_sym("j"), ax_sym("w")),
        ax_sym("i"),
        ax_sym("v"),
    );
    let parsed = vec![ax_neq(ax_sym("i"), ax_sym("j")), ax_neq(store_l, store_r)];
    let lean = emit_array_store_commute_firewall_lean_from_parsed(&parsed)
        .expect("direct store-commutativity should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("namespace AySoundness.Emitted.ArrStoreComm_"));
    assert!(lean.contains("theorem no_model"));
    assert!(lean.contains("firewall_combined_unsat"));
    // DIRECT form: function-equality atom (noncomputable via Classical) proved by
    // funext, guarded by the single index coincidence.
    assert!(lean.contains("attribute [local instance] Classical.propDecidable"));
    assert!(lean.contains("noncomputable def atomVal"));
    assert!(lean.contains("funext x"));
    assert!(lean.contains("def lemmas   : List (Cid × Clause) := [(3, [1, 2])]"));
}

#[test]
fn emits_array_store_commute_select_from_parsed() {
    // storecomm_sf_minimal, define-funs already expanded:
    // (not (= i1 i2)),
    // (not (= (select (store (store a i1 v1) i2 v2) k)
    //         (select (store (store a i2 v2) i1 v1) k))).
    let l = ax_store(
        ax_store(ax_sym("a"), ax_sym("i1"), ax_sym("v1")),
        ax_sym("i2"),
        ax_sym("v2"),
    );
    let r = ax_store(
        ax_store(ax_sym("a"), ax_sym("i2"), ax_sym("v2")),
        ax_sym("i1"),
        ax_sym("v1"),
    );
    let parsed = vec![
        ax_neq(ax_sym("i1"), ax_sym("i2")),
        ax_neq(ax_select(l, ax_sym("k")), ax_select(r, ax_sym("k"))),
    ];
    let lean = emit_array_store_commute_firewall_lean_from_parsed(&parsed)
        .expect("read-forwarded store-commutativity should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("namespace AySoundness.Emitted.ArrStoreComm_"));
    assert!(lean.contains("firewall_combined_unsat"));
    // SELECT form: values compared as Nat — computable atom (no Classical / funext).
    assert!(!lean.contains("Classical.propDecidable"));
    assert!(!lean.contains("noncomputable def atomVal"));
    assert!(!lean.contains("funext"));
    assert!(lean.contains("by_cases"));
}

#[test]
fn emits_array_store_commute_select_3idx_from_parsed() {
    // storecomm_sf_3idx (expanded): 1-2-3 vs 3-2-1 orderings, three pairwise
    // index disequalities backing the guards, read forwarded at k.
    let l = ax_store(
        ax_store(
            ax_store(ax_sym("a"), ax_sym("i1"), ax_sym("v1")),
            ax_sym("i2"),
            ax_sym("v2"),
        ),
        ax_sym("i3"),
        ax_sym("v3"),
    );
    let r = ax_store(
        ax_store(
            ax_store(ax_sym("a"), ax_sym("i3"), ax_sym("v3")),
            ax_sym("i2"),
            ax_sym("v2"),
        ),
        ax_sym("i1"),
        ax_sym("v1"),
    );
    let parsed = vec![
        ax_neq(ax_sym("i1"), ax_sym("i2")),
        ax_neq(ax_sym("i1"), ax_sym("i3")),
        ax_neq(ax_sym("i2"), ax_sym("i3")),
        ax_neq(ax_select(l, ax_sym("k")), ax_select(r, ax_sym("k"))),
    ];
    let lean = emit_array_store_commute_firewall_lean_from_parsed(&parsed)
        .expect("3-index read-forwarded store-commutativity should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    // Three pairwise coincidences ⇒ guard atoms 2,3,4, lemma clause [1,2,3,4].
    assert!(lean.contains("def lemmas   : List (Cid × Clause) := [(5, [1, 2, 3, 4])]"));
    assert!(lean.contains("firewall_combined_unsat"));
}

#[test]
fn emits_array_store_commute_defexpanded_from_parsed() {
    // The REAL storecomm_sf_minimal shape: `lhs`/`rhs` are nullary define-fun
    // macros whose bodies are opposite-order 2-store chains, and the target reads
    // both at `k`. The nested emitter declines (the read index is unconstrained,
    // so its unbacked guards do not close); the store-commute emitter in the
    // define-fun-expansion chain grounds it.
    let lbody = ax_store(
        ax_store(ax_sym("a"), ax_sym("i1"), ax_sym("v1")),
        ax_sym("i2"),
        ax_sym("v2"),
    );
    let rbody = ax_store(
        ax_store(ax_sym("a"), ax_sym("i2"), ax_sym("v2")),
        ax_sym("i1"),
        ax_sym("v1"),
    );
    let target = ax_neq(
        ax_select(ax_sym("lhs"), ax_sym("k")),
        ax_select(ax_sym("rhs"), ax_sym("k")),
    );
    let parsed = vec![ax_neq(ax_sym("i1"), ax_sym("i2")), target];
    let defs = vec![("lhs".to_string(), lbody), ("rhs".to_string(), rbody)];
    let lean = emit_array_defexpanded_firewall_lean_from_parsed(&parsed, &defs)
        .expect("define-fun-expanded store-commutativity should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("namespace AySoundness.Emitted.ArrStoreComm_"));
    assert!(lean.contains("firewall_combined_unsat"));
    // Declines when no macro expands (empty defs — nothing to substitute).
    assert!(emit_array_defexpanded_firewall_lean_from_parsed(&parsed, &[]).is_none());
}

#[test]
fn array_store_commute_declines_without_index_diseq() {
    // Same two store orderings but NO (not (= i j)): the guard is unbacked, so the
    // arrays are NOT equal in general (i = j gives store a i w ≠ store a i v);
    // decline (fail-closed).
    let store_l = ax_store(
        ax_store(ax_sym("a"), ax_sym("i"), ax_sym("v")),
        ax_sym("j"),
        ax_sym("w"),
    );
    let store_r = ax_store(
        ax_store(ax_sym("a"), ax_sym("j"), ax_sym("w")),
        ax_sym("i"),
        ax_sym("v"),
    );
    let parsed = vec![ax_neq(store_l, store_r)];
    assert!(emit_array_store_commute_firewall_lean_from_parsed(&parsed).is_none());
}

#[test]
fn array_store_commute_declines_non_permutation() {
    // (not (= i j)) with (not (= (store (store a i v) j w) (store (store a j w) i v2)))
    // — the two chains write DIFFERENT values at index i (v vs v2), so they are not
    // the same array even under i ≠ j; decline (fail-closed).
    let store_l = ax_store(
        ax_store(ax_sym("a"), ax_sym("i"), ax_sym("v")),
        ax_sym("j"),
        ax_sym("w"),
    );
    let store_r = ax_store(
        ax_store(ax_sym("a"), ax_sym("j"), ax_sym("w")),
        ax_sym("i"),
        ax_sym("v2"),
    );
    let parsed = vec![ax_neq(ax_sym("i"), ax_sym("j")), ax_neq(store_l, store_r)];
    assert!(emit_array_store_commute_firewall_lean_from_parsed(&parsed).is_none());
}

// ---- conflicting stores (conflicting_stores.smt2): ROW-1 through a variable ----

#[test]
fn emits_array_conflicting_stores_from_parsed() {
    // (not (= e1 e2)), (= a (store b i e1)), (= a (store b i e2)).
    let parsed = vec![
        ax_neq(ax_sym("e1"), ax_sym("e2")),
        ax_eq(
            ax_sym("a"),
            ax_store(ax_sym("b"), ax_sym("i"), ax_sym("e1")),
        ),
        ax_eq(
            ax_sym("a"),
            ax_store(ax_sym("b"), ax_sym("i"), ax_sym("e2")),
        ),
    ];
    let lean = emit_array_conflicting_stores_firewall_lean_from_parsed(&parsed)
        .expect("conflicting stores should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("namespace AySoundness.Emitted.ArrConflStores_"));
    assert!(lean.contains("ArrayThy.sel_upd_same"));
    assert!(lean.contains("decide (m.e1 = m.e2)"));
    assert!(lean.contains("firewall_combined_unsat"));
}

#[test]
fn array_conflicting_stores_declines_distinct_index() {
    // Two stores bound to the same variable but at DIFFERENT indices: e1 = e2 does
    // not follow; decline (fail-closed).
    let parsed = vec![
        ax_neq(ax_sym("e1"), ax_sym("e2")),
        ax_eq(
            ax_sym("a"),
            ax_store(ax_sym("b"), ax_sym("i"), ax_sym("e1")),
        ),
        ax_eq(
            ax_sym("a"),
            ax_store(ax_sym("b"), ax_sym("k"), ax_sym("e2")),
        ),
    ];
    assert!(emit_array_conflicting_stores_firewall_lean_from_parsed(&parsed).is_none());
}

#[test]
fn array_conflicting_stores_declines_without_value_diseq() {
    // No (not (= e1 e2)): the two bindings are jointly satisfiable (e1 = e2);
    // decline (fail-closed).
    let parsed = vec![
        ax_eq(
            ax_sym("a"),
            ax_store(ax_sym("b"), ax_sym("i"), ax_sym("e1")),
        ),
        ax_eq(
            ax_sym("a"),
            ax_store(ax_sym("b"), ax_sym("i"), ax_sym("e2")),
        ),
    ];
    assert!(emit_array_conflicting_stores_firewall_lean_from_parsed(&parsed).is_none());
}

// ---- diamond conflict (diamond_conflict.smt2): store-eq ⇒ ROW-1 vs ROW-2 ----

#[test]
fn emits_array_diamond_conflict_from_parsed() {
    // (= b (store a i v)), (= c (store a j w)), (not (= i j)), (= b c),
    // (not (= v (select a i))).
    let parsed = vec![
        ax_eq(ax_sym("b"), ax_store(ax_sym("a"), ax_sym("i"), ax_sym("v"))),
        ax_eq(ax_sym("c"), ax_store(ax_sym("a"), ax_sym("j"), ax_sym("w"))),
        ax_neq(ax_sym("i"), ax_sym("j")),
        ax_eq(ax_sym("b"), ax_sym("c")),
        ax_neq(ax_sym("v"), ax_select(ax_sym("a"), ax_sym("i"))),
    ];
    let lean = emit_array_diamond_conflict_firewall_lean_from_parsed(&parsed)
        .expect("diamond conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("namespace AySoundness.Emitted.ArrDiamond_"));
    assert!(lean.contains("decide (m.v = m.a m.i)"));
    assert!(lean.contains("firewall_combined_unsat"));
}

#[test]
fn array_diamond_conflict_declines_without_index_diseq() {
    // Missing (not (= i j)): under i = j the read-back need not hit the base at i,
    // so v = select a i does not follow; decline (fail-closed).
    let parsed = vec![
        ax_eq(ax_sym("b"), ax_store(ax_sym("a"), ax_sym("i"), ax_sym("v"))),
        ax_eq(ax_sym("c"), ax_store(ax_sym("a"), ax_sym("j"), ax_sym("w"))),
        ax_eq(ax_sym("b"), ax_sym("c")),
        ax_neq(ax_sym("v"), ax_select(ax_sym("a"), ax_sym("i"))),
    ];
    assert!(emit_array_diamond_conflict_firewall_lean_from_parsed(&parsed).is_none());
}

#[test]
fn array_diamond_conflict_declines_different_base() {
    // The two stores are over DIFFERENT bases (a vs d): reading `store d j w` at i
    // yields `d i`, not `a i`, so `v = select a i` does not follow; decline.
    let parsed = vec![
        ax_eq(ax_sym("b"), ax_store(ax_sym("a"), ax_sym("i"), ax_sym("v"))),
        ax_eq(ax_sym("c"), ax_store(ax_sym("d"), ax_sym("j"), ax_sym("w"))),
        ax_neq(ax_sym("i"), ax_sym("j")),
        ax_eq(ax_sym("b"), ax_sym("c")),
        ax_neq(ax_sym("v"), ax_select(ax_sym("a"), ax_sym("i"))),
    ];
    assert!(emit_array_diamond_conflict_firewall_lean_from_parsed(&parsed).is_none());
}

fn register_firewall_test_constant(context: &mut ay_frontend::Context, name: &str, sort: Sort) {
    let term = context.terms.mk_var(name, sort.clone());
    context.register_symbol(name.to_string(), term, sort);
}

fn cbr_typed_context(numeric_sort: Sort) -> ay_frontend::Context {
    let mut context = ay_frontend::Context::new();
    for name in ["a", "b", "c", "x", "y"] {
        register_firewall_test_constant(&mut context, name, numeric_sort.clone());
    }
    register_firewall_test_constant(&mut context, "arr", Sort::array(Sort::Int, Sort::Int));
    context
        .register_native_function_alias(
            "f".to_string(),
            "__firewall_test_f".to_string(),
            vec![numeric_sort.clone()],
            numeric_sort,
        )
        .expect("test UF declaration should be valid");
    context
}

fn c4_typed_context(element_sort: Sort) -> ay_frontend::Context {
    let mut context = ay_frontend::Context::new();
    let array_sort = Sort::array(Sort::Int, element_sort);
    for name in ["a", "b"] {
        register_firewall_test_constant(&mut context, name, array_sort.clone());
    }
    context
}

// ==== APPENDED TESTS: euf_cong_bridge (UF congruence closing an LIA system) ====
#[test]
fn emits_euf_cong_bridge_uf_in_bounds_from_parsed() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let app = |op: &str, a: Vec<PTerm>| PTerm::App(op.to_string(), a);
    let context = cbr_typed_context(Sort::Int);

    // a = b, f(a) < 0, f(b) >= 0 : congruence a=b => f(a)=f(b), then omega-unsat.
    let parsed = vec![
        app("=", vec![sym("a"), sym("b")]),
        app("<", vec![app("f", vec![sym("a")]), num("0")]),
        app(">=", vec![app("f", vec![sym("b")]), num("0")]),
    ];
    let lean = emit_euf_congruence_bridge_firewall_lean_from_parsed(&parsed, &context)
        .expect("UF-in-bounds congruence conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    for needle in [
        "import AySoundness.Firewall",
        "firewall_combined_unsat",
        "f_f : Int -> Int",
        "m.f_f (m.x_a) < (0 : Int)",
        "m.f_f (m.x_b) >= (0 : Int)",
        "have hbr0 : m.f_f (m.x_a) = m.f_f (m.x_b)",
        "rw [he0]",
        "omega",
        "theorem no_model",
    ] {
        assert!(lean.contains(needle), "emitted Lean missing: {needle}");
    }
}

#[test]
fn emits_euf_cong_bridge_uf_diseq_drops_inert_store_from_parsed() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let app = |op: &str, a: Vec<PTerm>| PTerm::App(op.to_string(), a);
    let context = cbr_typed_context(Sort::Int);

    // (x+1)=(y+1), (store a (f x) 0)=(store a (f y) 0) [INERT, dropped], f(x)!=f(y).
    // x=y => f(x)=f(y) by congruence, contradicting the disequality.
    let parsed = vec![
        app(
            "=",
            vec![
                app("+", vec![sym("x"), num("1")]),
                app("+", vec![sym("y"), num("1")]),
            ],
        ),
        app(
            "=",
            vec![
                app(
                    "store",
                    vec![sym("arr"), app("f", vec![sym("x")]), num("0")],
                ),
                app(
                    "store",
                    vec![sym("arr"), app("f", vec![sym("y")]), num("0")],
                ),
            ],
        ),
        app(
            "not",
            vec![app(
                "=",
                vec![app("f", vec![sym("x")]), app("f", vec![sym("y")])],
            )],
        ),
    ];
    let lean = emit_euf_congruence_bridge_firewall_lean_from_parsed(&parsed, &context)
        .expect("UF-disequality congruence conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    for needle in [
        "firewall_combined_unsat",
        "decide (m.f_f (m.x_x) = m.f_f (m.x_y))",
        "have hbr0 : m.f_f (m.x_x) = m.f_f (m.x_y)",
        "theorem no_model",
    ] {
        assert!(lean.contains(needle), "emitted Lean missing: {needle}");
    }
    // The inert array-store equality must NOT appear as a modelled atom (2 atoms).
    assert!(
        !lean.contains("store"),
        "inert array-store assertion should have been dropped from the core"
    );
    assert!(
        lean.contains("[(1, [1]), (2, [-2])]"),
        "expected exactly two core atoms"
    );
}

#[test]
fn euf_cong_bridge_declines_without_congruence_conflict() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let app = |op: &str, a: Vec<PTerm>| PTerm::App(op.to_string(), a);
    let int_context = cbr_typed_context(Sort::Int);
    let real_context = cbr_typed_context(Sort::Real);

    // (a) No implied equality: a, b unconstrained; f(a)<0, f(b)>=0 is SAT.
    let no_eq = vec![
        app("<", vec![app("f", vec![sym("a")]), num("0")]),
        app(">=", vec![app("f", vec![sym("b")]), num("0")]),
    ];
    assert!(emit_euf_congruence_bridge_firewall_lean_from_parsed(&no_eq, &int_context).is_none());

    // (b) Consistent under congruence: a=b, f(a)>=0, f(b)>=0 -- no conflict.
    let consistent = vec![
        app("=", vec![sym("a"), sym("b")]),
        app(">=", vec![app("f", vec![sym("a")]), num("0")]),
        app(">=", vec![app("f", vec![sym("b")]), num("0")]),
    ];
    assert!(
        emit_euf_congruence_bridge_firewall_lean_from_parsed(&consistent, &int_context).is_none()
    );

    // (c) Pure-LIA conflict with NO uninterpreted function: x>=5, x<=3. Infeasible
    // but no congruence bridge -> declined (left to the LIA emitter).
    let pure_lia = vec![
        app(">=", vec![sym("x"), num("5")]),
        app("<=", vec![sym("x"), num("3")]),
    ];
    assert!(
        emit_euf_congruence_bridge_firewall_lean_from_parsed(&pure_lia, &int_context).is_none()
    );

    // (d) Real / QF_UFLRA gate: decimal numerals are not Int -> decline.
    let real = vec![
        app("=", vec![sym("a"), sym("b")]),
        app(
            "<",
            vec![
                app("f", vec![sym("a")]),
                PTerm::Const(PConst::Decimal("0.0".to_string())),
            ],
        ),
        app(
            ">=",
            vec![
                app("f", vec![sym("b")]),
                PTerm::Const(PConst::Decimal("0.0".to_string())),
            ],
        ),
    ];
    assert!(emit_euf_congruence_bridge_firewall_lean_from_parsed(&real, &real_context).is_none());

    // (e) Empty assertion list -> decline.
    assert!(emit_euf_congruence_bridge_firewall_lean_from_parsed(&[], &int_context).is_none());
}

#[test]
fn euf_cong_bridge_declines_numeral_only_real_strict_gap() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let app = |op: &str, args: Vec<PTerm>| PTerm::App(op.to_string(), args);
    let context = cbr_typed_context(Sort::Real);

    // SAT over Real: choose a=b and f(a)=f(b)=1/2. The former untyped emitter
    // rounded >0/<1 to integer bounds 1/0 and emitted a false local conflict.
    let parsed = vec![
        app("=", vec![sym("a"), sym("b")]),
        app(">", vec![app("f", vec![sym("a")]), num("0")]),
        app("<", vec![app("f", vec![sym("b")]), num("1")]),
    ];
    assert!(
        emit_euf_congruence_bridge_firewall_lean_from_parsed(&parsed, &context).is_none(),
        "a numeral-spelled Real formula must not be reinterpreted over Int"
    );
}

#[test]
fn euf_cong_bridge_declines_missing_or_ambiguous_surface_types() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let app = |op: &str, args: Vec<PTerm>| PTerm::App(op.to_string(), args);
    let parsed = vec![
        app("=", vec![sym("a"), sym("b")]),
        app("<", vec![app("f", vec![sym("a")]), num("0")]),
        app(">=", vec![app("f", vec![sym("b")]), num("0")]),
    ];

    let missing = ay_frontend::Context::new();
    assert!(emit_euf_congruence_bridge_firewall_lean_from_parsed(&parsed, &missing).is_none());

    let mut ambiguous = cbr_typed_context(Sort::Int);
    ambiguous
        .register_native_function_alias(
            "f".to_string(),
            "__firewall_test_f_real".to_string(),
            vec![Sort::Real],
            Sort::Real,
        )
        .expect("test overload should be valid");
    assert!(
        emit_euf_congruence_bridge_firewall_lean_from_parsed(&parsed, &ambiguous).is_none(),
        "surface overloads have no identity in ParsedTerm and must be declined"
    );
}

#[test]
fn euf_cong_bridge_declines_i64_analysis_overflow() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let app = |op: &str, args: Vec<PTerm>| PTerm::App(op.to_string(), args);
    let context = cbr_typed_context(Sort::Int);
    let max = i64::MAX.to_string();

    // Legal unbounded SMT Int arithmetic, but MAX+1 is outside the recognizer's
    // deliberately bounded i64 analysis domain. Decline; never panic or wrap.
    let normalization_overflow = vec![
        app("=", vec![sym("a"), sym("b")]),
        app(
            ">",
            vec![
                app("+", vec![app("f", vec![sym("a")]), num(&max), num("1")]),
                num("0"),
            ],
        ),
        app("<", vec![app("f", vec![sym("b")]), num("0")]),
    ];
    assert!(emit_euf_congruence_bridge_firewall_lean_from_parsed(
        &normalization_overflow,
        &context,
    )
    .is_none());

    // This normalizes to coefficient 1 and constant MIN without overflowing;
    // converting `x + MIN > 0` to an inclusive i64 lower bound would exceed MAX.
    let bound_overflow = vec![
        app("=", vec![sym("a"), sym("b")]),
        app(
            ">",
            vec![
                app(
                    "+",
                    vec![
                        app("f", vec![sym("a")]),
                        app("-", vec![num(&max)]),
                        app("-", vec![num("1")]),
                    ],
                ),
                num("0"),
            ],
        ),
        app("<", vec![app("f", vec![sym("b")]), num("0")]),
    ];
    assert!(
        emit_euf_congruence_bridge_firewall_lean_from_parsed(&bound_overflow, &context).is_none()
    );
}

// ==== APPENDED TESTS: array_sum_bound (fused array-ROW + LIA) ====
#[test]
fn emits_array_sum_bound_from_parsed() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let app = |op: &str, a: Vec<PTerm>| PTerm::App(op.to_string(), a);
    let sel = |a: &str, i: &str| app("select", vec![sym(a), num(i)]);
    let store = |b: &str, i: &str, v: &str| app("store", vec![sym(b), num(i), num(v)]);
    let context = c4_typed_context(Sort::Int);

    // b=store(a,0,10), b=store(b,1,20), (select b 0)+(select b 1) > 31 : 30 !> 31.
    let parsed = vec![
        app("=", vec![sym("b"), store("a", "0", "10")]),
        app("=", vec![sym("b"), store("b", "1", "20")]),
        app(
            ">",
            vec![app("+", vec![sel("b", "0"), sel("b", "1")]), num("31")],
        ),
    ];
    let lean = emit_array_sum_bound_firewall_lean_from_parsed(&parsed, &context)
        .expect("fused array-ROW + LIA conflict should emit");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    for needle in [
        "import AySoundness.Firewall",
        "firewall_combined_unsat",
        "Classical.propDecidable",
        "a : Int -> Int",
        "b : Int -> Int",
        "(m.b (0 : Int) + m.b (1 : Int)) > (31 : Int)",
        "have e_b_0 : m.b (0 : Int) = (10 : Int)",
        "have e_b_1 : m.b (1 : Int) = (20 : Int)",
        "congrFun h1",
        "congrFun h2",
        "omega",
        "theorem no_model",
    ] {
        assert!(lean.contains(needle), "emitted Lean missing: {needle}");
    }
}

#[test]
fn array_sum_bound_declines_feasible_or_ungrounded() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let app = |op: &str, a: Vec<PTerm>| PTerm::App(op.to_string(), a);
    let sel = |a: &str, i: &str| app("select", vec![sym(a), num(i)]);
    let store = |b: &str, i: &str, v: &str| app("store", vec![sym(b), num(i), num(v)]);
    let context = c4_typed_context(Sort::Int);

    // (a) FEASIBLE: 10 + 20 = 30 > 29 holds -> no conflict -> decline.
    let feasible = vec![
        app("=", vec![sym("b"), store("a", "0", "10")]),
        app("=", vec![sym("b"), store("b", "1", "20")]),
        app(
            ">",
            vec![app("+", vec![sel("b", "0"), sel("b", "1")]), num("29")],
        ),
    ];
    assert!(emit_array_sum_bound_firewall_lean_from_parsed(&feasible, &context).is_none());

    // (b) NO store equality -> decline.
    let no_store = vec![app(">", vec![sel("b", "0"), num("31")])];
    assert!(emit_array_sum_bound_firewall_lean_from_parsed(&no_store, &context).is_none());

    // (c) UNGROUNDABLE read: store writes index 5, read is at index 0 -> decline.
    let ungrounded = vec![
        app("=", vec![sym("b"), store("a", "5", "10")]),
        app(">", vec![sel("b", "0"), num("31")]),
    ];
    assert!(emit_array_sum_bound_firewall_lean_from_parsed(&ungrounded, &context).is_none());

    // (d) Empty -> decline.
    assert!(emit_array_sum_bound_firewall_lean_from_parsed(&[], &context).is_none());
}

#[test]
fn array_sum_bound_declines_non_int_missing_or_ambiguous_array_types() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let app = |op: &str, args: Vec<PTerm>| PTerm::App(op.to_string(), args);
    let sel = |array: &str, index: &str| app("select", vec![sym(array), num(index)]);
    let store = |base: &str, index: &str, value: &str| {
        app("store", vec![sym(base), num(index), num(value)])
    };
    let parsed = vec![
        app("=", vec![sym("b"), store("a", "0", "10")]),
        app("=", vec![sym("b"), store("b", "1", "20")]),
        app(
            ">",
            vec![app("+", vec![sel("b", "0"), sel("b", "1")]), num("31")],
        ),
    ];

    let real_elements = c4_typed_context(Sort::Real);
    assert!(
        emit_array_sum_bound_firewall_lean_from_parsed(&parsed, &real_elements).is_none(),
        "an Array Int Real formula must not be reinterpreted as Array Int Int"
    );

    let missing = ay_frontend::Context::new();
    assert!(emit_array_sum_bound_firewall_lean_from_parsed(&parsed, &missing).is_none());

    let mut ambiguous = c4_typed_context(Sort::Int);
    ambiguous
        .register_native_function_alias(
            "b".to_string(),
            "__firewall_test_b_real_array".to_string(),
            Vec::new(),
            Sort::array(Sort::Int, Sort::Real),
        )
        .expect("test array overload should be valid");
    assert!(
        emit_array_sum_bound_firewall_lean_from_parsed(&parsed, &ambiguous).is_none(),
        "ambiguous surface array names must be declined"
    );
}

#[test]
fn array_sum_bound_declines_i64_grounding_overflow() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let app = |op: &str, args: Vec<PTerm>| PTerm::App(op.to_string(), args);
    let context = c4_typed_context(Sort::Int);
    let max = i64::MAX.to_string();

    // Grounding the read produces MAX+1, outside the recognizer's i64 analysis
    // domain. The SMT Int expression is legal; the diagnostic must just decline.
    let parsed = vec![
        app(
            "=",
            vec![sym("b"), app("store", vec![sym("a"), num("0"), num(&max)])],
        ),
        app(
            ">",
            vec![
                app("+", vec![app("select", vec![sym("b"), num("0")]), num("1")]),
                num("0"),
            ],
        ),
    ];
    assert!(emit_array_sum_bound_firewall_lean_from_parsed(&parsed, &context).is_none());
}

// ---------------------------------------------------------------------------
// LIA firewall: subset-refutation faithfulness + `first`-combinator hygiene.
// ---------------------------------------------------------------------------

/// Build the `la_generic` clause AY derives for
/// `benchmarks/smt/QF_LIA/pigeonhole_3_2.smt2` — five negated comparisons over
/// the six 0/1 variables. The six binary-domain assertions are NOT part of it:
/// the emitted artifact refutes a strict SUBSET of the query's atoms.
fn pigeonhole_3_2_la_generic(terms: &mut TermStore) -> Vec<TermId> {
    let v: Vec<TermId> = ["p11", "p21", "p31", "p12", "p22", "p32"]
        .iter()
        .map(|n| terms.mk_var(*n, Sort::Int))
        .collect();
    let one = terms.mk_int(num_bigint::BigInt::from(1));
    fn sum(terms: &mut TermStore, xs: Vec<TermId>) -> TermId {
        terms.mk_app(Symbol::named("+"), xs, Sort::Int)
    }
    // Hole capacity bounds.
    let hole1 = sum(terms, vec![v[0], v[1], v[2]]);
    let hole2 = sum(terms, vec![v[3], v[4], v[5]]);
    let c1 = cmp(terms, "<=", hole1, one);
    let c2 = cmp(terms, "<=", hole2, one);
    // "Exactly one hole" per pigeon, written `1 = pᵢ₂ + pᵢ₁` as AY renders it.
    let p2 = sum(terms, vec![v[4], v[1]]);
    let p1 = sum(terms, vec![v[3], v[0]]);
    let p3 = sum(terms, vec![v[5], v[2]]);
    let c3 = cmp(terms, "=", one, p2);
    let c4 = cmp(terms, "=", one, p1);
    let c5 = cmp(terms, "=", one, p3);
    [c1, c2, c3, c4, c5]
        .iter()
        .map(|&c| terms.mk_not(c))
        .collect()
}

#[test]
fn lia_subset_refutation_is_faithful_to_the_query_atoms() {
    // The emitted `original`/`atomVal` pair IS the refuted system. Witness that
    // it renders exactly the lemma's comparisons, under an injective and total
    // variable-to-index map, with one unit clause per atom.
    let mut terms = TermStore::new();
    let lits = pigeonhole_3_2_la_generic(&mut terms);
    let lean = emit_lia_firewall_lean(&terms, &lits).expect("pigeonhole la_generic should emit");

    // (a) Each atom is the faithful rendering of the corresponding literal, in
    //     literal order, over SIX distinct valuation indices — one per query
    //     variable, none conflated, none invented.
    for arm in [
        "| 1 => decide (((m 0) + (m 1) + (m 2)) ≤ (1 : Int))",
        "| 2 => decide (((m 3) + (m 4) + (m 5)) ≤ (1 : Int))",
        "| 3 => decide ((1 : Int) = ((m 4) + (m 1)))",
        "| 4 => decide ((1 : Int) = ((m 3) + (m 0)))",
        "| 5 => decide ((1 : Int) = ((m 5) + (m 2)))",
    ] {
        assert!(lean.contains(arm), "atom table missing/renamed: {arm}");
    }
    // The map is TOTAL over 0..5: every index occurs, none above.
    for i in 0..6 {
        assert!(lean.contains(&format!("(m {i})")), "variable {i} unmapped");
    }
    assert!(!lean.contains("(m 6)"), "index outside the variable map");

    // (b) `original` is exactly one unit clause per atom, asserted with the
    //     polarity OPPOSITE the lemma literal — the refuted system is the
    //     rendered atoms and nothing else.
    assert!(
        lean.contains(
            "def original : List (Cid × Clause) := [(1, [1]), (2, [2]), (3, [3]), (4, [4]), (5, [5])]"
        ),
        "original is not the per-atom unit-clause subset"
    );
    assert!(
        lean.contains("def lemmas   : List (Cid × Clause) := [(6, [-1, -2, -3, -4, -5])]"),
        "lemma clause does not negate exactly the asserted atoms"
    );
}

#[test]
fn lia_rejects_atoms_referencing_unmapped_valuation_indices() {
    // The faithfulness side-condition itself: an atom mentioning an index the
    // variable map never allocated must fail closed, never emit.
    assert!(lia_atom_indices_are_in_range(["(m 0) ≤ (m 1)"], 2));
    assert!(!lia_atom_indices_are_in_range(["(m 0) ≤ (m 2)"], 2));
    assert!(!lia_atom_indices_are_in_range(["(m 0) ≤ (m )"], 2));
    assert!(lia_atom_indices_are_in_range(["(1 : Int) ≤ (2 : Int)"], 0));
}

#[test]
fn lia_lemma_tactic_keeps_the_case_split_first_while_it_is_affordable() {
    // At or below the width bound the historical case-split product must stay
    // the FIRST alternative, so every artifact that closes today keeps its proof
    // term — and its axiom basis — unchanged.
    let mut terms = TermStore::new();
    let lits = pigeonhole_3_2_la_generic(&mut terms);
    let lean = emit_lia_firewall_lean(&terms, &lits).expect("should emit");
    let first_at = lean.find("first").expect("tactic must use `first`");
    let case_at = lean[first_at..]
        .find("by_cases h1")
        .expect("case-split alternative missing");
    let omega_at = lean[first_at..]
        .find("Bool.or_eq_true")
        .expect("linear alternative missing");
    assert!(
        case_at < omega_at,
        "5 atoms is within MAX_CASE_SPLIT_FIRST_ATOMS; the case split must lead"
    );
    // The wall-clock guard on these input-amplifiable artifacts stays in force.
    // Only the stack-depth guard is scaled, and it is never unbounded.
    assert!(
        !lean.contains("maxHeartbeats"),
        "emitted artifacts must never touch maxHeartbeats"
    );
    assert!(lean.contains("set_option maxRecDepth "));
}

#[test]
fn lia_lemma_tactic_leads_with_the_linear_script_on_wide_clauses() {
    // Above the bound the case-split product cannot finish inside Lean's
    // per-declaration heartbeat budget, and exhausting it aborts the whole
    // declaration — `first` could never reach a later alternative. So the linear
    // script must lead there.
    let mut terms = TermStore::new();
    let one = terms.mk_int(num_bigint::BigInt::from(1));
    let mut lits = Vec::new();
    for i in 0..=MAX_CASE_SPLIT_FIRST_ATOMS {
        let x = terms.mk_var(format!("x{i}"), Sort::Int);
        let le = cmp(&mut terms, "<=", x, one);
        lits.push(terms.mk_not(le));
    }
    let lean = emit_lia_firewall_lean(&terms, &lits).expect("wide clause should emit");
    let first_at = lean.find("first").expect("tactic must use `first`");
    let case_at = lean[first_at..].find("by_cases h1").expect("case split");
    let omega_at = lean[first_at..].find("Bool.or_eq_true").expect("linear");
    assert!(
        omega_at < case_at,
        "wide clause must lead with the linear script"
    );
}

#[test]
fn scaled_max_rec_depth_is_bounded_and_monotone() {
    // Input-amplifiable: the stack-depth guard grows with clause size but is
    // clamped, so a hostile proof cannot ask for an unbounded elaboration stack.
    assert_eq!(scaled_max_rec_depth(0), 4_096);
    assert!(scaled_max_rec_depth(100) >= scaled_max_rec_depth(10));
    assert_eq!(scaled_max_rec_depth(usize::MAX), 262_144);
    assert!(scaled_max_rec_depth(647) <= 262_144);
}

// ==== APPENDED TESTS: nia_product ====

/// Parse a list of assertion bodies with the real frontend parser.
fn nia_parsed(asserts: &[&str]) -> Vec<ay_frontend::command::Term> {
    asserts.iter().map(|s| parse_assertion(s)).collect()
}

/// `benchmarks/smt/QF_NIA/simple_product_unsat.smt2` — the headline target. On
/// main this file emits NOTHING (`--emit-firewall-lean` exits 1 and publishes no
/// verdict at all); the McCormick bridge is what makes it groundable.
#[test]
fn emits_nia_product_for_simple_product_unsat() {
    let context = cbr_typed_context(Sort::Int);
    let parsed = nia_parsed(&[
        "(>= x 1)",
        "(<= x 2)",
        "(>= y 1)",
        "(<= y 2)",
        "(= (* x y) 7)",
    ]);
    let lean = emit_nia_product_firewall_lean_from_parsed(&parsed, &[], &context)
        .expect("1 <= x,y <= 2 with x*y = 7 is a bilinear product conflict");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    // O4: the import header must be exactly the allow-listed pair, IN THE ORDER
    // `crates/ay/src/firewall_verify.rs::ALLOWED_EMITTED_IMPORTS` strips them.
    assert!(lean.starts_with("import AySoundness.Firewall\nimport AySoundness.NiaProduct\n"));
    assert_eq!(lean.matches("\nimport ").count(), 1);
    assert!(lean.contains("firewall_combined_unsat"));
    assert!(lean.contains("decide (((m 0) * (m 1)) = (7 : Int))"));
    // All four corners are available here (x and y are boxed on both sides).
    for lemma in ["mul_lb_ll", "mul_lb_uu", "mul_ub_ul", "mul_ub_lu"] {
        assert!(
            lean.contains(&format!(
                "AySoundness.NiaProduct.{lemma} (x := (m 0)) (y := (m 1))"
            )),
            "missing corner {lemma}"
        );
    }
}

/// **O1 REGRESSION.** `omega` atomises `x * y` and `y * x` as two INDEPENDENT
/// unknowns. A recognizer that models both occurrences as one fresh product
/// variable (as the Rust gate does) but renders them in surface order produces a
/// gate/goal mismatch and an artifact the kernel REJECTS — while
/// `--emit-firewall-lean` has already published `unsat` on the strength of it.
///
/// The emitter must therefore canonicalise the factor order. `x*y + y*x = 14`
/// under `1 <= x,y <= 2` must render ONE product atom (folded to `2 * (x*y)`),
/// and the commuted spelling must never appear.
#[test]
fn nia_product_canonicalizes_commuted_bilinear_factors() {
    let context = cbr_typed_context(Sort::Int);
    let parsed = nia_parsed(&[
        "(>= x 1)",
        "(<= x 2)",
        "(>= y 1)",
        "(<= y 2)",
        "(= (+ (* x y) (* y x)) 14)",
    ]);
    let lean = emit_nia_product_firewall_lean_from_parsed(&parsed, &[], &context)
        .expect("the commuted-duplicate product conflict must be groundable");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(
        !lean.contains("((m 1) * (m 0))"),
        "commuted factor order leaked into the emitted goal — omega would see two atoms"
    );
    assert!(lean.contains("decide (((2 : Int) * ((m 0) * (m 1))) = (14 : Int))"));
    // The bridge is instantiated on the canonical factor order too.
    assert!(lean.contains("(x := (m 0)) (y := (m 1))"));
    assert!(!lean.contains("(x := (m 1)) (y := (m 0))"));
}

/// `benchmarks/smt/QF_NIA/sign_consistency.smt2` — LOWER bounds only. The full
/// four-corner envelope is unavailable, so only `mul_lb_ll` may be injected; the
/// emitter must not invent the missing upper bounds.
#[test]
fn emits_nia_product_with_lower_bounds_only() {
    let context = cbr_typed_context(Sort::Int);
    let parsed = nia_parsed(&["(> x 0)", "(> y 0)", "(< (* x y) 0)"]);
    let lean = emit_nia_product_firewall_lean_from_parsed(&parsed, &[], &context)
        .expect("x,y > 0 with x*y < 0 is refutable from the lower-lower corner alone");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("mul_lb_ll"));
    for absent in ["mul_lb_uu", "mul_ub_ul", "mul_ub_lu"] {
        assert!(
            !lean.contains(absent),
            "invented an absent bound for {absent}"
        );
    }
    // `x > 0` over the integers tightens to `x >= 1`: the corner is instantiated
    // at the INTEGER bound, matching what `omega` derives for the side goal.
    assert!(lean.contains("(a := (1 : Int)) (c := (1 : Int))"));
}

/// A SQUARE `x * x` is the `i == j` case: both corner coefficients land on the
/// same slot and no special casing is needed.
#[test]
fn emits_nia_product_for_square_conflict() {
    let context = cbr_typed_context(Sort::Int);
    let parsed = nia_parsed(&["(>= x (- 5))", "(<= x 5)", "(= (* x x) 30)"]);
    let lean = emit_nia_product_firewall_lean_from_parsed(&parsed, &[], &context)
        .expect("-5 <= x <= 5 bounds x*x <= 25, refuting x*x = 30");
    eprintln!("----LEAN-BEGIN----\n{lean}\n----LEAN-END----");
    assert!(lean.contains("decide (((m 0) * (m 0)) = (30 : Int))"));
    assert!(lean.contains("(x := (m 0)) (y := (m 0))"));
}

/// A MIXED-SIGN box needs more than one corner: `x, y` in `[-2, 3]` bounds
/// `x * y <= 6`, which only the upper corners see.
#[test]
fn emits_nia_product_for_mixed_sign_box() {
    let context = cbr_typed_context(Sort::Int);
    let parsed = nia_parsed(&[
        "(>= x (- 2))",
        "(<= x 3)",
        "(>= y (- 2))",
        "(<= y 3)",
        "(= (* x y) 20)",
    ]);
    let lean = emit_nia_product_firewall_lean_from_parsed(&parsed, &[], &context)
        .expect("mixed-sign box conflict should emit");
    assert!(lean.contains("(a := (-2 : Int))"));
    assert!(lean.contains("(b := (3 : Int))"));
}

/// **No misfire.** Every SATISFIABLE system must decline: `--emit-firewall-lean`
/// turns an emission into a published verdict, so a fired emitter on a
/// satisfiable reconstruction would be a kernel-failing artifact behind an
/// `unsat`.
#[test]
fn nia_product_declines_satisfiable_systems() {
    let context = cbr_typed_context(Sort::Int);
    // benchmarks/smt/QF_NIA/simple_product_sat.smt2 shape: x*y = 4 in [1,4]^2.
    let sat_product = nia_parsed(&[
        "(>= x 1)",
        "(<= x 4)",
        "(>= y 1)",
        "(<= y 4)",
        "(= (* x y) 4)",
    ]);
    assert!(emit_nia_product_firewall_lean_from_parsed(&sat_product, &[], &context).is_none());
    // benchmarks/smt/QF_NIA/square_bounds.smt2: x*x = 9 in [-5, 5] — SAT (x = 3).
    let square_sat = nia_parsed(&["(>= x (- 5))", "(<= x 5)", "(= (* x x) 9)"]);
    assert!(emit_nia_product_firewall_lean_from_parsed(&square_sat, &[], &context).is_none());
    // benchmarks/smt/QF_NIA/tswift_pattern.smt2: SAT (width = height = 1).
    let tswift = nia_parsed(&["(> x 0)", "(> y 0)", "(<= (* x y) 100)", "(>= (* x y) 1)"]);
    assert!(emit_nia_product_firewall_lean_from_parsed(&tswift, &[], &context).is_none());
    // The McCormick envelope is a RELAXATION: `x*y = 5` in [1,3]^2 is outside the
    // integer solution set but INSIDE the envelope, so the gate cannot refute it
    // and must decline rather than emit an omega-unclosable artifact.
    let relaxation_gap = nia_parsed(&[
        "(>= x 1)",
        "(<= x 3)",
        "(>= y 1)",
        "(<= y 3)",
        "(= (* x y) 5)",
    ]);
    assert!(emit_nia_product_firewall_lean_from_parsed(&relaxation_gap, &[], &context).is_none());
}

/// **O2 faithfulness gate.** A `store`-bodied `define-fun` makes the assertion an
/// ARRAY atom; reconstructing it as two fresh integers would be an unsound
/// abstraction. The `defs` parameter must not be dropped.
#[test]
fn nia_product_declines_array_valued_define_fun() {
    use ay_frontend::command::Term as PTerm;
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let context = cbr_typed_context(Sort::Int);
    let a2_body = PTerm::App(
        "store".to_string(),
        vec![
            sym("arr"),
            sym("x"),
            PTerm::App("select".to_string(), vec![sym("arr"), sym("x")]),
        ],
    );
    let defs = vec![("a2".to_string(), a2_body)];
    let with_array = nia_parsed(&["(>= x 1)", "(<= x 2)", "(= (* x x) 7)", "(not (= a2 arr))"]);
    assert!(emit_nia_product_firewall_lean_from_parsed(&with_array, &defs, &context).is_none());
    // The gate fires only on assertions that MENTION the array macro: an
    // otherwise identical query without it still emits.
    let without_array = nia_parsed(&["(>= x 1)", "(<= x 2)", "(= (* x x) 7)"]);
    assert!(emit_nia_product_firewall_lean_from_parsed(&without_array, &defs, &context).is_some());
}

/// Non-Int atoms must decline: `omega` is an INTEGER procedure and the McCormick
/// corners are `Int` lemmas.
#[test]
fn nia_product_declines_non_int_and_unresolved_symbols() {
    let real_context = cbr_typed_context(Sort::Real);
    let parsed = nia_parsed(&[
        "(>= x 1)",
        "(<= x 2)",
        "(>= y 1)",
        "(<= y 2)",
        "(= (* x y) 7)",
    ]);
    assert!(emit_nia_product_firewall_lean_from_parsed(&parsed, &[], &real_context).is_none());
    // An undeclared variable is not an Int constant and is not a signed literal.
    let missing = ay_frontend::Context::new();
    assert!(emit_nia_product_firewall_lean_from_parsed(&parsed, &[], &missing).is_none());
}

/// Shapes outside the single-bilinear-product fragment decline.
#[test]
fn nia_product_declines_out_of_fragment_shapes() {
    let context = cbr_typed_context(Sort::Int);
    // A purely LINEAR conflict has no product: the LIA emitter owns it, and
    // duplicating it here would only add a redundant artifact.
    let linear = nia_parsed(&["(> x 5)", "(< x 3)"]);
    assert!(emit_nia_product_firewall_lean_from_parsed(&linear, &[], &context).is_none());
    // TWO distinct bilinear pairs — the model has one product slot only.
    let two_products = nia_parsed(&[
        "(>= x 1)",
        "(<= x 2)",
        "(>= y 1)",
        "(<= y 2)",
        "(>= a 1)",
        "(<= a 2)",
        "(= (+ (* x y) (* a y)) 99)",
    ]);
    assert!(emit_nia_product_firewall_lean_from_parsed(&two_products, &[], &context).is_none());
    // DEGREE 3 (`x * x * x`) is not bilinear.
    let cubic = nia_parsed(&["(>= x 1)", "(<= x 2)", "(< (* x (* x x)) 0)"]);
    assert!(emit_nia_product_firewall_lean_from_parsed(&cubic, &[], &context).is_none());
    // Propositional structure is not a comparison.
    let disjunction = nia_parsed(&["(or (= (* x y) 7) (= x 1))"]);
    assert!(emit_nia_product_firewall_lean_from_parsed(&disjunction, &[], &context).is_none());
    // `mod`/`div` are outside the Fourier-Motzkin gate's domain.
    let modular = nia_parsed(&["(>= x 1)", "(<= x 2)", "(= (mod (* x y) 3) 7)"]);
    assert!(emit_nia_product_firewall_lean_from_parsed(&modular, &[], &context).is_none());
    // An empty assertion list has nothing to reconstruct.
    assert!(emit_nia_product_firewall_lean_from_parsed(&[], &[], &context).is_none());
}

/// `benchmarks/smt/QF_NIA/nia_negative_factor_falseprove.smt2` is the standing
/// false-UNSAT regression (SAT witness `x = -4, y = -10`). Its assertions must
/// NOT produce a refutation artifact — that would be a wrong verdict published
/// with a proof attached.
#[test]
fn nia_product_declines_the_negative_factor_false_prove_regression() {
    let context = cbr_typed_context(Sort::Int);
    let parsed = nia_parsed(&[
        "(>= (* x y) 6)",
        "(>= y (- 10))",
        "(<= y 3)",
        "(<= x 10)",
        "(< (* x (* x x)) 0)",
    ]);
    assert!(emit_nia_product_firewall_lean_from_parsed(&parsed, &[], &context).is_none());
    // Even with the cubic assertion removed (leaving a bilinear-only system that
    // the recognizer CAN model), the system is satisfiable and must decline.
    let bilinear_only = nia_parsed(&["(>= (* x y) 6)", "(>= y (- 10))", "(<= y 3)", "(<= x 10)"]);
    assert!(emit_nia_product_firewall_lean_from_parsed(&bilinear_only, &[], &context).is_none());
}

/// Disequality atoms carry no linear row, so they only ever WEAKEN the gate —
/// they are still rendered and hypothesised, but can never make an otherwise
/// feasible system look infeasible.
#[test]
fn nia_product_disequalities_do_not_strengthen_the_gate() {
    let context = cbr_typed_context(Sort::Int);
    // `x*y != 7` cannot be refuted by the (inequality-only) envelope: decline.
    let diseq_only = nia_parsed(&[
        "(>= x 1)",
        "(<= x 2)",
        "(>= y 1)",
        "(<= y 2)",
        "(not (= (* x y) 7))",
    ]);
    assert!(emit_nia_product_firewall_lean_from_parsed(&diseq_only, &[], &context).is_none());
    // Adding a disequality to a genuinely infeasible system still emits, and the
    // disequality is rendered faithfully as a hypothesis.
    let with_diseq = nia_parsed(&[
        "(>= x 1)",
        "(<= x 2)",
        "(>= y 1)",
        "(<= y 2)",
        "(= (* x y) 7)",
        "(distinct x y)",
    ]);
    let lean = emit_nia_product_firewall_lean_from_parsed(&with_diseq, &[], &context)
        .expect("the underlying product conflict is still refutable");
    assert!(lean.contains("(m 0) ≠ (m 1)"));
}

/// SMT Int expressions are unbounded; the recognizer's `i64` analysis domain and
/// the gate's `i128` elimination domain are not. Every arithmetic step is
/// checked, so an out-of-domain query must DECLINE, never panic or wrap into a
/// bogus infeasibility.
#[test]
fn nia_product_declines_out_of_domain_coefficients() {
    let context = cbr_typed_context(Sort::Int);
    let huge = i64::MAX.to_string();
    let over = format!("{}0", i64::MAX); // one decimal digit past i64::MAX
                                         // A coefficient beyond i64 in the product's own term.
    let big_coeff = nia_parsed(&[
        "(>= x 1)",
        "(<= x 2)",
        "(>= y 1)",
        "(<= y 2)",
        &format!("(= (* {over} (* x y)) 7)"),
    ]);
    assert!(emit_nia_product_firewall_lean_from_parsed(&big_coeff, &[], &context).is_none());
    // Bounds at the i64 extreme make the corner constants (`p * q`) overflow.
    let huge_box = nia_parsed(&[
        &format!("(>= x {huge})"),
        &format!("(<= x {huge})"),
        &format!("(>= y {huge})"),
        &format!("(<= y {huge})"),
        "(= (* x y) 0)",
    ]);
    assert!(emit_nia_product_firewall_lean_from_parsed(&huge_box, &[], &context).is_none());
    // Too many distinct Int variables for the elimination budget.
    let mut wide: Vec<String> = vec!["(= (* x y) 7)".to_string()];
    for i in 0..12 {
        wide.push(format!("(>= v{i} {i})"));
    }
    let mut wide_context = ay_frontend::Context::new();
    for name in ["x", "y"] {
        register_firewall_test_constant(&mut wide_context, name, Sort::Int);
    }
    for i in 0..12 {
        register_firewall_test_constant(&mut wide_context, &format!("v{i}"), Sort::Int);
    }
    let wide_refs: Vec<&str> = wide.iter().map(String::as_str).collect();
    let wide_parsed = nia_parsed(&wide_refs);
    assert!(emit_nia_product_firewall_lean_from_parsed(&wide_parsed, &[], &wide_context).is_none());
}

/// The binary64 vocabulary gate must range over the WHOLE formula, not over the
/// symbols that happen to sit in direct `fp.*` operand position.
///
/// An earlier version collected only direct same-sort `fp.*` operands, so a
/// non-binary64 value reachable any other way was never examined and the gate's
/// `all(...)` passed VACUOUSLY. Since the entire purpose of the gate is that
/// `Term::Symbol` carries no sort — the `Float32` clone of `guard_claim_guard2`
/// has byte-identical parsed terms yet is SATISFIABLE — a subset check is worth
/// nothing. Each shape below was demonstrated to return `true` before the fix.
#[test]
fn fp_vocabulary_gate_rejects_non_binary64_reachable_off_the_operand_path() {
    // A Float32 symbol declared in the session, reachable only under `=`.
    let via_eq = vec![parse_assertion("(= f32a f32b)")];
    let mut table = f64_formats();
    table.push(("f32a".to_string(), Some((8, 24))));
    table.push(("f32b".to_string(), Some((8, 24))));
    assert!(
        !parsed_fp_vocabulary_is_binary64(&via_eq, &[], &table),
        "a declared Float32 symbol must decline however it is reached"
    );

    // binary32 arithmetic behind an `(_ to_fp 8 24)` conversion: the indices
    // name the result format, and IndexedApp arguments used to be recursed into
    // without ever being collected.
    let via_to_fp = vec![parse_assertion(
        "(fp.isNormal ((_ to_fp 8 24) RNE (fp.to_real nx)))",
    )];
    assert!(
        !parsed_fp_vocabulary_is_binary64(&via_to_fp, &[], &f64_formats()),
        "a to_fp index pair other than (11,53) must decline"
    );
    // The binary64 conversion itself is still acceptable.
    let to_fp64 = vec![parse_assertion(
        "(fp.isNormal ((_ to_fp 11 53) RNE (fp.to_real nx)))",
    )];
    assert!(parsed_fp_vocabulary_is_binary64(
        &to_fp64,
        &[],
        &f64_formats()
    ));

    // A Float32 operand under `ite`, which is not an `fp.*` operator.
    let via_ite = vec![parse_assertion("(fp.isNormal (ite B f32a nx))")];
    let mut ite_table = f64_formats();
    ite_table.push(("f32a".to_string(), Some((8, 24))));
    assert!(
        !parsed_fp_vocabulary_is_binary64(&via_ite, &[], &ite_table),
        "a Float32 value under `ite` must decline"
    );

    // An `(fp ...)` bit-pattern literal: the surface syntax does not carry the
    // format, so it is refused outright rather than assumed binary64.
    let via_literal = vec![parse_assertion(
        "(fp.isNormal (fp #b0 #b00000001 #b00000000000000000000000))",
    )];
    assert!(
        !parsed_fp_vocabulary_is_binary64(&via_literal, &[], &f64_formats()),
        "an `fp` bit-pattern literal must decline"
    );
}

// ---------------------------------------------------------------------------
// `str.in_re` LENGTH-INVARIANT emitter (AySoundness.RegexThy).
// ---------------------------------------------------------------------------

fn in_re_parsed(asserts: &[&str]) -> Vec<ay_frontend::command::Term> {
    asserts.iter().map(|s| parse_assertion(s)).collect()
}

/// Emit for a SINGLE-SHOT query (no push/pop, one check-sat).
fn emit_in_re(asserts: &[&str]) -> Option<String> {
    emit_str_in_re_len_firewall_lean_from_parsed(&in_re_parsed(asserts), true)
}

/// `benchmarks/smtcomp/QF_SLIA/.../regex-011-unsat-fuzz-graft-reverse.smt2` —
/// the headline target. `":{'hAa"` is 6 code points and the regex is the
/// doubly-nested `re.+ (re.* ...)`, so the MODULAR invariant sees `6 ∤ 4`
/// straight through the nesting.
#[test]
fn emits_str_in_re_modular_conflict_for_regex_011() {
    let lean = emit_in_re(&[
        r#"(str.in_re x (re.+ (re.* (str.to_re ":{'hAa"))))"#,
        r#"(str.in_re y (str.to_re "dP!$ba"))"#,
        "(= 4 (str.len x))",
    ])
    .expect("modular conflict");
    assert!(lean.contains("import AySoundness.RegexThy"));
    assert!(lean.contains("RegexThy.regex_len_mod_conflict (k := 6)"));
    assert!(lean.contains("decide (StringThy.len m = 4)"));
    // `re.+ r` is rendered as the Lean `plus` abbreviation `cat r (star r)`.
    assert!(lean.contains(
        "RegexThy.Re.cat (RegexThy.Re.star (RegexThy.Re.lit [58, 123, 39, 104, 65, 97]))"
    ));
    assert!(lean.contains("theorem no_model"));
}

/// The finite-language tier: `str.to_re "...."` bounds every member at 4, and
/// the modular check does NOT close it (4 ∣ 20).
#[test]
fn emits_str_in_re_max_len_conflict() {
    let lean = emit_in_re(&[r#"(str.in_re x (str.to_re "...."))"#, "(= (str.len x) 20)"])
        .expect("max-length conflict");
    assert!(lean.contains("RegexThy.regex_len_max_conflict (n := 4)"));
}

/// The "too short" tier.
#[test]
fn emits_str_in_re_min_len_conflict() {
    let lean = emit_in_re(&[
        r#"(str.in_re x (re.++ (str.to_re "abc") (re.+ (str.to_re "de"))))"#,
        "(= (str.len x) 4)",
    ])
    .expect("min-length conflict");
    assert!(lean.contains("RegexThy.regex_len_min_conflict hm h"));
}

/// INEQUALITY pins fire only through the two proved inequality corollaries.
/// `(< (str.len x) 5)` normalises to `len ≤ 4`, below `minLen = 5`.
#[test]
fn emits_str_in_re_min_len_conflict_for_strict_upper_bound() {
    let lean = emit_in_re(&[
        r#"(str.in_re x (re.++ (str.to_re "abc") (re.+ (str.to_re "de"))))"#,
        "(< (str.len x) 5)",
    ])
    .expect("min-length inequality conflict");
    assert!(lean.contains("RegexThy.regex_len_min_conflict_le hm h"));
    assert!(lean.contains("decide (StringThy.len m ≤ 4)"));
}

/// `(> (str.len x) 4)` normalises to `5 ≤ len`, above `maxLen = 4`.
#[test]
fn emits_str_in_re_max_len_conflict_for_strict_lower_bound() {
    let lean = emit_in_re(&[r#"(str.in_re x (str.to_re "...."))"#, "(> (str.len x) 4)"])
        .expect("max-length inequality conflict");
    assert!(lean.contains("RegexThy.regex_len_max_conflict_ge (n := 4)"));
    assert!(lean.contains("decide (5 ≤ StringThy.len m)"));
}

/// SECTION-0 (O1). A membership asserted inside a `push` that is popped before
/// the reported `check-sat` is NOT part of that query. The frontend export
/// cannot express per-check-sat scoping, so the emitter declines outright on
/// any query that used push/pop or a second check-sat — even when the very same
/// assertion list would otherwise fire.
#[test]
fn declines_str_in_re_when_the_query_is_not_single_shot() {
    let asserts = [
        r#"(str.in_re x (re.+ (re.* (str.to_re ":{'hAa"))))"#,
        "(= 4 (str.len x))",
    ];
    assert!(emit_in_re(&asserts).is_some());
    assert!(emit_str_in_re_len_firewall_lean_from_parsed(&in_re_parsed(&asserts), false).is_none());
}

/// SECTION-0 (O3). The modular invariant has NO inequality form: `6 ∣ len x`
/// is compatible with `len x < 4` (namely `len x = 0`). Firing `Mod` on an
/// inequality would certify a falsehood, so the emitter must decline.
#[test]
fn declines_modular_tier_on_an_inequality_pin() {
    // `re.* (str.to_re "abcdef")` has minLen 0 and unbounded maxLen, so only the
    // modular tier could apply — and it must not, on an inequality.
    assert!(emit_in_re(&[
        r#"(str.in_re x (re.* (str.to_re "abcdef")))"#,
        "(< (str.len x) 4)",
    ])
    .is_none());
    assert!(emit_in_re(&[
        r#"(str.in_re x (re.* (str.to_re "abcdef")))"#,
        "(> (str.len x) 4)",
    ])
    .is_none());
    // The equality form of the same conflict DOES fire.
    assert!(emit_in_re(&[
        r#"(str.in_re x (re.* (str.to_re "abcdef")))"#,
        "(= (str.len x) 4)",
    ])
    .is_some());
}

/// SECTION-0 (O5). `re.loop` / `re.^` reach the parser as `IndexedApp`, and
/// `AySoundness.RegexThy` proves no invariant for bounded repetition (its
/// `n > m` case denotes the EMPTY language). The decline must be explicit, not
/// an accident of the matcher's shape. Same for `re.comp` / `re.diff`.
#[test]
fn declines_unproven_regex_constructors() {
    for regex in [
        "((_ re.loop 2 3) (str.to_re \"ab\"))",
        "((_ re.^ 3) (str.to_re \"ab\"))",
        "(re.comp (str.to_re \"ab\"))",
        "(re.diff (str.to_re \"ab\") (str.to_re \"cd\"))",
    ] {
        let asserts = [
            format!("(str.in_re x {regex})"),
            "(= (str.len x) 3)".to_string(),
        ];
        let refs: Vec<&str> = asserts.iter().map(String::as_str).collect();
        assert!(emit_in_re(&refs).is_none(), "must decline on {regex}");
    }
    // A declined constructor NESTED inside an otherwise-supported one still
    // declines the whole regex — there is no partial rendering.
    assert!(emit_in_re(&[
        "(str.in_re x (re.++ (str.to_re \"abcd\") (re.comp (str.to_re \"ab\"))))",
        "(= (str.len x) 3)",
    ])
    .is_none());
}

/// `re.range` is rendered as the ONE-SIDED `anyChar` over-approximation. Sound
/// for a refutation (the source assertion implies the rendered atom), but the
/// artifact must say so rather than present itself as a byte-mirror.
#[test]
fn renders_re_range_as_a_declared_over_approximation() {
    let lean = emit_in_re(&[
        r#"(str.in_re x (re.++ (re.range "a" "z") (re.range "0" "9")))"#,
        "(= (str.len x) 5)",
    ])
    .expect("max-length conflict through the anyChar over-approximation");
    assert!(lean.contains("RegexThy.Re.anyChar"));
    assert!(lean.contains("ONE-SIDED RENDERING"));
    assert!(lean.contains("RegexThy.regex_len_max_conflict (n := 2)"));
}

/// The pin and the membership must name the SAME symbol.
#[test]
fn declines_when_the_length_pin_names_a_different_symbol() {
    assert!(emit_in_re(&[
        r#"(str.in_re x (re.+ (str.to_re "ed")))"#,
        "(= (str.len y) 9)",
    ])
    .is_none());
    assert!(emit_in_re(&[
        r#"(str.in_re x (re.+ (str.to_re "ed")))"#,
        "(= (str.len x) 9)",
    ])
    .is_some());
}

/// No conflict, no artifact: a length the regex genuinely admits.
#[test]
fn declines_when_the_pinned_length_is_admissible() {
    assert!(emit_in_re(&[
        r#"(str.in_re x (re.+ (str.to_re "ed")))"#,
        "(= (str.len x) 8)",
    ])
    .is_none());
}

/// O2. String literals arrive pre-decoded by `ay_core::unescape_string_contents`
/// through the frontend s-expression reader, so the emitter counts exactly the
/// code points the SOLVER saw — there is no second decoder here to get out of
/// step with the one the verdict was computed from.
///
/// The three SMT-LIB 2.6 behaviours that a C-style decoder gets WRONG, each of
/// which would flip the modulus and so the verdict this emitter certifies:
///   * `\u{41}` is ONE code point (`A`), not six;
///   * `\t` is TWO characters (backslash, `t`) — a backslash is literal except
///     in the two unicode escapes;
///   * in `\\u{41}` the FIRST backslash is literal (the next character is not
///     `u`) and the SECOND opens a real escape, giving TWO characters (`\`,
///     `A`) — not one, and not seven.
#[test]
fn str_in_re_literal_length_follows_the_smtlib_escape_decoder() {
    // `\u{41}` decodes to "A": one code point, refuting a length-0 pin through
    // the minLen invariant.
    let one = emit_in_re(&[r#"(str.in_re x (str.to_re "\u{41}"))"#, "(= (str.len x) 0)"])
        .expect("single-code-point literal");
    assert!(one.contains("RegexThy.Re.lit [65]"));
    // `\t` is backslash + `t`, so `re.+` has modulus 2 and refutes len 5.
    let backslash_t = emit_in_re(&[
        r#"(str.in_re x (re.+ (str.to_re "\t")))"#,
        "(= (str.len x) 5)",
    ])
    .expect("literal backslash-t");
    assert!(backslash_t.contains("RegexThy.Re.lit [92, 116]"));
    assert!(backslash_t.contains("RegexThy.regex_len_mod_conflict (k := 2)"));
    // `\\u{41}` is a literal backslash followed by a REAL escape: `\`, `A`.
    let mixed = emit_in_re(&[
        r#"(str.in_re x (re.+ (str.to_re "\\u{41}")))"#,
        "(= (str.len x) 5)",
    ])
    .expect("literal backslash then escape");
    assert!(mixed.contains("RegexThy.Re.lit [92, 65]"));
    assert!(mixed.contains("RegexThy.regex_len_mod_conflict (k := 2)"));
}

/// Every operator name the emitter interprets must be RESERVED, so a user
/// `declare-fun` of that name cannot be conflated with the builtin. (The
/// emitter re-checks this at run time and fails closed; this pins the table.)
#[test]
fn str_in_re_interpreted_ops_are_all_reserved() {
    for name in REGEX_LEN_INTERPRETED_OPS {
        assert!(
            ay_frontend::is_reserved_op_name(name),
            "{name} must be reserved or the emitter would conflate a user function with it"
        );
    }
}

/// Text spliced into the emitted block comment must not be able to open a
/// nested comment (`/-`) or close the header early (`-/`).
#[test]
fn lean_comment_safe_neutralises_comment_delimiters() {
    let out = lean_comment_safe("a/-b-/c");
    assert!(!out.contains("/-"));
    assert!(!out.contains("-/"));
    assert_eq!(lean_comment_safe("plain_name"), "plain_name");
    // Non-printable / non-ASCII is replaced rather than emitted verbatim.
    assert_eq!(lean_comment_safe("a\nb\u{1F600}"), "a?b?");
}

/// The Rust length abstractions must agree with the Lean ones they mirror; a
/// disagreement only ever produces a file that fails to compile, but that is a
/// wasted artifact, so pin the arithmetic.
#[test]
fn regex_len_abstractions_mirror_the_lean_definitions() {
    let w6 = ReAst::Lit(vec![58, 123, 39, 104, 65, 97]);
    let plus_star = ReAst::Cat(
        Box::new(ReAst::Star(Box::new(w6.clone()))),
        Box::new(ReAst::Star(Box::new(ReAst::Star(Box::new(w6.clone()))))),
    );
    assert_eq!(plus_star.modulus(), 6);
    assert!(plus_star.kdvd(6));
    assert_eq!(plus_star.min_len(), Some(0));
    assert_eq!(plus_star.max_len(), None);
    // `star` of a language whose only member is ε is bounded by 0.
    let star_eps = ReAst::Star(Box::new(ReAst::Lit(Vec::new())));
    assert_eq!(star_eps.max_len(), Some(0));
    // `0 ∣ n` only for `n = 0`, matching Lean's `Nat.dvd`.
    assert!(divides(0, 0));
    assert!(!divides(0, 3));
    // `inter` is one-sided in BOTH directions.
    let inter = ReAst::Inter(Box::new(w6), Box::new(ReAst::Lit(vec![1, 2, 3, 4])));
    assert_eq!(inter.min_len(), Some(6));
    assert_eq!(inter.max_len(), Some(4));
    assert!(inter.kdvd(6));
    assert!(inter.kdvd(4));
}

/// The `re.+` desugaring DUPLICATES its operand, so `(re.+ (re.+ (re.+ …)))`
/// doubles the rendered node count at every level. Without a size check at each
/// construction point, a 40-deep nest would allocate `2^40` nodes before any
/// post-hoc cap could look at the result. The emitter must decline in bounded
/// time and bounded memory.
#[test]
fn str_in_re_declines_exponentially_blowing_up_nests_in_bounded_memory() {
    let mut regex = String::from(r#"(str.to_re "ab")"#);
    for _ in 0..40 {
        regex = format!("(re.+ {regex})");
    }
    let asserts = [
        format!("(str.in_re x {regex})"),
        "(= (str.len x) 3)".to_string(),
    ];
    let refs: Vec<&str> = asserts.iter().map(String::as_str).collect();
    assert!(emit_in_re(&refs).is_none());
    // A literal past the character cap is declined at the leaf, before it can
    // be duplicated by an enclosing `re.+`.
    let long = "a".repeat(REGEX_LEN_MAX_LITERAL_CHARS + 1);
    let asserts = [
        format!(r#"(str.in_re x (str.to_re "{long}"))"#),
        "(= (str.len x) 3)".to_string(),
    ];
    let refs: Vec<&str> = asserts.iter().map(String::as_str).collect();
    assert!(emit_in_re(&refs).is_none());
    // Just under the node cap still emits, so the guard is not vacuous.
    let mut small = String::from(r#"(str.to_re "ab")"#);
    for _ in 0..4 {
        small = format!("(re.+ {small})");
    }
    let asserts = [
        format!("(str.in_re x {small})"),
        "(= (str.len x) 3)".to_string(),
    ];
    let refs: Vec<&str> = asserts.iter().map(String::as_str).collect();
    assert!(emit_in_re(&refs).is_some());
}

// ==== APPENDED TESTS: euf_uflra (REAL-faithful ordered-field firewall) ====

/// The five assertions of `benchmarks/smt/QF_UFLRA/unsat_equality_propagation.smt2`.
fn ordfield_target_assertions() -> Vec<ay_frontend::command::Term> {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let dec = |d: &str| PTerm::Const(PConst::Decimal(d.to_string()));
    let app = |op: &str, a: Vec<PTerm>| PTerm::App(op.to_string(), a);
    vec![
        app(">=", vec![sym("x"), dec("5.0")]),
        app("<=", vec![sym("x"), dec("5.0")]),
        app("=", vec![sym("y"), dec("5.0")]),
        app("=", vec![app("f", vec![sym("x")]), dec("10.0")]),
        app("=", vec![app("f", vec![sym("y")]), dec("20.0")]),
    ]
}

#[test]
fn emits_euf_ordfield_congruence_from_parsed_real_assertions() {
    let real_context = cbr_typed_context(Sort::Real);
    let lean = emit_euf_ordfield_congruence_firewall_lean_from_parsed(
        &ordfield_target_assertions(),
        &real_context,
    )
    .expect("Real-sorted EUF congruence conflict should emit");
    // The header must list exactly the two allow-listed imports, in this order.
    assert!(lean.starts_with("import AySoundness.Firewall\nimport AySoundness.OrdField\n"));
    assert!(lean.contains("firewall_combined_unsat"));
    // The model is an ARBITRARY ordered field, never Int/Rat.
    assert!(lean.contains("structure Val (F : OrdField)"));
    assert!(lean.contains("f_f : F.carrier -> F.carrier"));
    assert!(!lean.contains(": Int"));
    // No integer reasoning survives into the CODE (the header prose mentions
    // `omega` only to say what it replaced).
    let code = lean.split_once("\n-/\n").expect("header block").1;
    assert!(!code.contains("omega"));
    // The only `Int` left is the LRAT hint list's element type, never a model
    // carrier: `: Int` (a field or ascription) must not appear at all.
    assert!(code.contains("List Int"));
    // The two ordered-field steps that replace `omega`.
    assert!(lean.contains("F.le_antisymm"));
    assert!(lean.contains("F.ofNat_ne"));
}

#[test]
fn euf_ordfield_firewall_declines_int_sorted_assertions() {
    // O1, direction A: an Int file must NEVER reach the ordered-field render.
    let int_context = cbr_typed_context(Sort::Int);
    assert!(
        emit_euf_ordfield_congruence_firewall_lean_from_parsed(
            &ordfield_target_assertions(),
            &int_context
        )
        .is_none(),
        "Int-sorted symbols must not route to the ordered-field emitter"
    );
}

#[test]
fn euf_lia_firewall_declines_real_sorted_assertions() {
    // O1, direction B: a Real file must NEVER reach the `omega`/Int render.
    let real_context = cbr_typed_context(Sort::Real);
    assert!(
        emit_euf_lia_congruence_firewall_lean_from_parsed(
            &ordfield_target_assertions(),
            &real_context
        )
        .is_none(),
        "Real-sorted symbols must not route to the Int emitter"
    );
}

#[test]
fn euf_ordfield_firewall_never_pins_from_strict_bounds() {
    // O1, the measured consequence: `x > 5 && x < 7` pins `x = 6` over Int but
    // leaves `x` free over ℝ, where the whole conjunction is SAT. The Int
    // emitter must fire on the Int analogue and the Real one must decline.
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let dec = |d: &str| PTerm::Const(PConst::Decimal(d.to_string()));
    let app = |op: &str, a: Vec<PTerm>| PTerm::App(op.to_string(), a);

    let real_parsed = vec![
        app(">", vec![sym("x"), dec("5.0")]),
        app("<", vec![sym("x"), dec("7.0")]),
        app("=", vec![sym("y"), dec("6.0")]),
        app("=", vec![app("f", vec![sym("x")]), dec("10.0")]),
        app("=", vec![app("f", vec![sym("y")]), dec("20.0")]),
    ];
    assert!(
        emit_euf_ordfield_congruence_firewall_lean_from_parsed(
            &real_parsed,
            &cbr_typed_context(Sort::Real)
        )
        .is_none(),
        "strict Real bounds pin nothing; this conjunction is SAT over ℝ"
    );

    let int_parsed = vec![
        app(">", vec![sym("x"), num("5")]),
        app("<", vec![sym("x"), num("7")]),
        app("=", vec![sym("y"), num("6")]),
        app("=", vec![app("f", vec![sym("x")]), num("10")]),
        app("=", vec![app("f", vec![sym("y")]), num("20")]),
    ];
    assert!(
        emit_euf_lia_congruence_firewall_lean_from_parsed(
            &int_parsed,
            &cbr_typed_context(Sort::Int)
        )
        .is_some(),
        "the Int analogue IS unsat and must keep its omega-discharged artifact"
    );
}

#[test]
fn euf_ordfield_firewall_declines_colliding_sanitized_symbols() {
    // O3: two distinct SMT symbols that sanitize onto one `Val` field would
    // silently force an equality, proving a MORE-CONSTRAINED formula.
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let dec = |d: &str| PTerm::Const(PConst::Decimal(d.to_string()));
    let app = |op: &str, a: Vec<PTerm>| PTerm::App(op.to_string(), a);

    let mut context = cbr_typed_context(Sort::Real);
    register_firewall_test_constant(&mut context, "p-q", Sort::Real);
    register_firewall_test_constant(&mut context, "p.q", Sort::Real);
    let parsed = vec![
        app("=", vec![sym("p-q"), dec("5.0")]),
        app("=", vec![sym("p.q"), dec("5.0")]),
        app("=", vec![app("f", vec![sym("p-q")]), dec("10.0")]),
        app("=", vec![app("f", vec![sym("p.q")]), dec("20.0")]),
    ];
    assert!(
        emit_euf_ordfield_congruence_firewall_lean_from_parsed(&parsed, &context).is_none(),
        "`p-q` and `p.q` both sanitize to `x_p_q` and must be declined"
    );
}

#[test]
fn euf_ordfield_firewall_declines_unrepresentable_literals() {
    // Only NON-NEGATIVE INTEGER-VALUED Real literals have an `F.ofNat` image.
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let dec = |d: &str| PTerm::Const(PConst::Decimal(d.to_string()));
    let app = |op: &str, a: Vec<PTerm>| PTerm::App(op.to_string(), a);
    let context = cbr_typed_context(Sort::Real);

    // A genuinely fractional decimal.
    let fractional = vec![
        app("=", vec![sym("x"), dec("2.5")]),
        app("=", vec![sym("y"), dec("2.5")]),
        app("=", vec![app("f", vec![sym("x")]), dec("10.0")]),
        app("=", vec![app("f", vec![sym("y")]), dec("20.0")]),
    ];
    assert!(
        emit_euf_ordfield_congruence_firewall_lean_from_parsed(&fractional, &context).is_none()
    );

    // A negated numeral is an arithmetic application, not a literal.
    let negative = vec![
        app("=", vec![sym("x"), app("-", vec![dec("5.0")])]),
        app("=", vec![sym("y"), app("-", vec![dec("5.0")])]),
        app("=", vec![app("f", vec![sym("x")]), dec("10.0")]),
        app("=", vec![app("f", vec![sym("y")]), dec("20.0")]),
    ];
    assert!(emit_euf_ordfield_congruence_firewall_lean_from_parsed(&negative, &context).is_none());

    // Any arithmetic operator at all: atoms are rendered directly, never
    // normalized, so no linear form (and no unrepresentable negative
    // coefficient) can ever arise.
    let arithmetic = vec![
        app("=", vec![app("+", vec![sym("x"), dec("1.0")]), dec("5.0")]),
        app("=", vec![sym("y"), dec("4.0")]),
        app("=", vec![app("f", vec![sym("x")]), dec("10.0")]),
        app("=", vec![app("f", vec![sym("y")]), dec("20.0")]),
    ];
    assert!(
        emit_euf_ordfield_congruence_firewall_lean_from_parsed(&arithmetic, &context).is_none()
    );
}

#[test]
fn euf_ordfield_firewall_declines_consistent_real_assertions() {
    // No congruence conflict and no empty interval: nothing to certify.
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let dec = |d: &str| PTerm::Const(PConst::Decimal(d.to_string()));
    let app = |op: &str, a: Vec<PTerm>| PTerm::App(op.to_string(), a);
    let parsed = vec![
        app(">=", vec![sym("x"), dec("5.0")]),
        app("<=", vec![sym("x"), dec("9.0")]),
        app("=", vec![app("f", vec![sym("x")]), dec("10.0")]),
        app("=", vec![app("f", vec![sym("y")]), dec("20.0")]),
    ];
    assert!(emit_euf_ordfield_congruence_firewall_lean_from_parsed(
        &parsed,
        &cbr_typed_context(Sort::Real)
    )
    .is_none());
}

#[test]
fn emits_euf_ordfield_bound_contradiction() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let dec = |d: &str| PTerm::Const(PConst::Decimal(d.to_string()));
    let app = |op: &str, a: Vec<PTerm>| PTerm::App(op.to_string(), a);
    let context = cbr_typed_context(Sort::Real);

    // Crossed weak bounds: `x >= 10 && x <= 5`.
    let crossed = vec![
        app(">=", vec![sym("x"), dec("10.0")]),
        app("<=", vec![sym("x"), dec("5.0")]),
    ];
    let lean = emit_euf_ordfield_congruence_firewall_lean_from_parsed(&crossed, &context)
        .expect("crossed Real bounds should emit");
    assert!(lean.contains("F.lt_le_absurd"));
    assert!(lean.contains("F.ofNat_lt_of_lt"));
    assert!(!lean
        .split_once("\n-/\n")
        .expect("header block")
        .1
        .contains("omega"));

    // Empty open interval: `x > 5 && x < 5`.
    let strict = vec![
        app(">", vec![sym("x"), dec("5.0")]),
        app("<", vec![sym("x"), dec("5.0")]),
    ];
    let lean = emit_euf_ordfield_congruence_firewall_lean_from_parsed(&strict, &context)
        .expect("empty open Real interval should emit");
    assert!(lean.contains("F.lt_le_absurd"));

    // NON-empty: `x >= 5 && x <= 5` is satisfiable (x = 5) and must decline.
    let pinned = vec![
        app(">=", vec![sym("x"), dec("5.0")]),
        app("<=", vec![sym("x"), dec("5.0")]),
    ];
    assert!(
        emit_euf_ordfield_congruence_firewall_lean_from_parsed(&pinned, &context).is_none(),
        "`x >= 5 && x <= 5` is SAT; a certificate here would be unsound"
    );

    // NON-empty open interval: `x > 5 && x < 7` is SAT over ℝ.
    let open = vec![
        app(">", vec![sym("x"), dec("5.0")]),
        app("<", vec![sym("x"), dec("7.0")]),
    ];
    assert!(
        emit_euf_ordfield_congruence_firewall_lean_from_parsed(&open, &context).is_none(),
        "`x > 5 && x < 7` is SAT over ℝ even though it is UNSAT over Int"
    );
}

/// The verifier's exact reproduction: Float32 symbols reachable only under `=`,
/// alongside a Float64 operand. Must decline.
#[test]
fn fp_gate_declines_float32_under_equality_verifier_repro() {
    let parsed = vec![
        parse_assertion("(= g h)"),
        parse_assertion("(fp.isNormal nx)"),
    ];
    let mut table = f64_formats();
    table.push(("g".to_string(), Some((8, 24))));
    table.push(("h".to_string(), Some((8, 24))));
    assert!(
        !parsed_fp_vocabulary_is_binary64(&parsed, &[], &table),
        "Float32 under `=` alongside a Float64 operand must decline"
    );
}

/// The emitted `str.in_re` artifact must carry a `maxRecDepth` that SCALES with
/// the rendered regex.
///
/// The rendered `Re` is one constructor per code point, so `decide`/`simp`
/// recurse once per character. Under Lean's default depth (512) a literal past
/// ~120 code points overflowed: the artifact failed to compile and reported
/// `sorryAx`. Measured cliff before the fix — 111 code points kernel-checked,
/// 130 did not — and an artifact that does not kernel-check is worse than
/// declining. The guard is SCALED, never disabled: proof size is
/// attacker-amplifiable, so it must move with the input rather than switch off.
#[test]
fn str_in_re_artifact_scales_max_rec_depth_with_the_regex() {
    let depth_for = |n: usize| -> usize {
        let lit = "a".repeat(n);
        let asserts = [
            format!(r#"(str.in_re x (re.++ (str.to_re "{lit}") (str.to_re "cd")))"#),
            "(= (str.len x) 3)".to_string(),
        ];
        let refs: Vec<&str> = asserts.iter().map(String::as_str).collect();
        let lean = emit_in_re(&refs).expect("emitter fires on the length-invariant shape");
        let tail = lean
            .split("set_option maxRecDepth ")
            .nth(1)
            .expect("emitted artifact must set maxRecDepth");
        tail.split_whitespace()
            .next()
            .expect("a numeric depth")
            .parse()
            .expect("a numeric depth")
    };

    let small = depth_for(2);
    let large = depth_for(400);
    assert!(
        small >= 4_096,
        "even a tiny regex gets the clamped floor, got {small}"
    );
    assert!(
        large > small,
        "depth must grow with the rendered regex: {small} -> {large}"
    );
    assert!(
        large <= 262_144,
        "and stay clamped so a hostile proof cannot demand an unbounded stack, got {large}"
    );
}

/// Atoms that defeat the nested-`by_cases` closing tactic must make the emitter
/// DECLINE, not write an artifact that fails to compile.
///
/// Both shapes were found by fuzzing and both produced a file that fails
/// `lake env lean` and reports `sorryAx` — strictly worse than declining, and a
/// REGRESSION against the previous behaviour of declining these inputs.
///
/// 1. A syntactically reflexive equality: `simp`'s `eq_self` rewrites the atom
///    to `True` before the branch hypothesis `¬(t = t)` can be used, so the goal
///    survives. Adding `(assert (= x x))` to the otherwise-clean frontier
///    benchmark was enough to turn a checking artifact into a `sorryAx` one.
/// 2. A disequality whose sides stand in an occurs relation: the closing branch
///    hands `h : y = g y` to `simp` as a rewrite rule, which loops to
///    "maximum recursion depth".
#[test]
fn ordfield_emitter_declines_atoms_that_defeat_the_closing_tactic() {
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let dec = |s: &str| PTerm::Const(PConst::Decimal(s.to_string()));
    let app = |op: &str, a: Vec<PTerm>| PTerm::App(op.to_string(), a);
    let real_context = cbr_typed_context(Sort::Real);

    // Control: the frontier target itself still emits.
    assert!(emit_euf_ordfield_congruence_firewall_lean_from_parsed(
        &ordfield_target_assertions(),
        &real_context
    )
    .is_some());

    // 1. The target plus a harmless reflexive equality must now DECLINE.
    let mut with_refl = ordfield_target_assertions();
    with_refl.push(app("=", vec![sym("x"), sym("x")]));
    assert!(
        emit_euf_ordfield_congruence_firewall_lean_from_parsed(&with_refl, &real_context).is_none(),
        "a reflexive equality atom defeats the closing tactic and must decline"
    );

    // A reflexive equality between two renderings of the same numeral likewise.
    let mut with_num_refl = ordfield_target_assertions();
    with_num_refl.push(app("=", vec![dec("5.0"), dec("5.0")]));
    assert!(
        emit_euf_ordfield_congruence_firewall_lean_from_parsed(&with_num_refl, &real_context)
            .is_none(),
        "a reflexive numeral equality must decline too"
    );

    // 2. A disequality whose sides stand in an occurs relation must DECLINE.
    let mut with_occurs = ordfield_target_assertions();
    with_occurs.push(app(
        "not",
        vec![app("=", vec![sym("y"), app("f", vec![sym("y")])])],
    ));
    assert!(
        emit_euf_ordfield_congruence_firewall_lean_from_parsed(&with_occurs, &real_context)
            .is_none(),
        "an occurs-relation disequality loops the closing `simp` and must decline"
    );
}

/// The same guard on the Int emitter this one was modelled on — the reflexive
/// class was present there first and was copied along with the closing tactic.
#[test]
fn euf_lia_emitter_declines_reflexive_equality_atoms() {
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let num = |s: &str| PTerm::Const(PConst::Numeral(s.to_string()));
    let app = |op: &str, a: Vec<PTerm>| PTerm::App(op.to_string(), a);
    let int_context = cbr_typed_context(Sort::Int);

    let base = vec![
        app(">=", vec![sym("a"), num("3")]),
        app("<=", vec![sym("a"), num("3")]),
        app("=", vec![sym("b"), num("3")]),
        app("=", vec![app("f", vec![sym("a")]), num("10")]),
        app("=", vec![app("f", vec![sym("b")]), num("20")]),
    ];
    assert!(emit_euf_lia_congruence_firewall_lean_from_parsed(&base, &int_context).is_some());

    let mut with_refl = base;
    with_refl.push(app("=", vec![sym("a"), sym("a")]));
    assert!(
        emit_euf_lia_congruence_firewall_lean_from_parsed(&with_refl, &int_context).is_none(),
        "the Int emitter must decline the same reflexive shape"
    );
}
