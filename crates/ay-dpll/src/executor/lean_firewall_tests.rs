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

// ==== APPENDED TESTS: lia ====
#[test]
fn emits_lia_linear_conflict_from_parsed() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    // (> x 5) ∧ (< x 3): jointly integer-UNSAT bound conflict.
    let parsed = vec![
        PTerm::App(">".to_string(), vec![sym("x"), num("5")]),
        PTerm::App("<".to_string(), vec![sym("x"), num("3")]),
    ];
    let lean = emit_lia_firewall_lean_from_parsed(&parsed)
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
    let lean2 = emit_lia_firewall_lean_from_parsed(&multi)
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
    assert!(emit_lia_firewall_lean_from_parsed(&nonlinear).is_none());
    // Declines non-arithmetic propositional structure (`or`).
    let prop = vec![PTerm::App("or".to_string(), vec![sym("p"), sym("q")])];
    assert!(emit_lia_firewall_lean_from_parsed(&prop).is_none());
}

// ==== APPENDED TESTS: euf_uflia ====
#[test]
fn emits_euf_lia_congruence_from_parsed_assertions() {
    use ay_frontend::command::{Constant as PConst, Term as PTerm};
    let sym = |s: &str| PTerm::Symbol(s.to_string());
    let num = |n: &str| PTerm::Const(PConst::Numeral(n.to_string()));
    let app = |op: &str, a: Vec<PTerm>| PTerm::App(op.to_string(), a);

    // POSITIVE: a>=3, a<=3, b=3, f(a)=10, f(b)=20 -> a=b=3 forces f(a)=f(b), 10!=20.
    let parsed = vec![
        app(">=", vec![sym("a"), num("3")]),
        app("<=", vec![sym("a"), num("3")]),
        app("=", vec![sym("b"), num("3")]),
        app("=", vec![app("f", vec![sym("a")]), num("10")]),
        app("=", vec![app("f", vec![sym("b")]), num("20")]),
    ];
    let lean = emit_euf_lia_congruence_firewall_lean_from_parsed(&parsed)
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
    assert!(emit_euf_lia_congruence_firewall_lean_from_parsed(&parsed3).is_some());

    // NEGATIVE (no implied equality): a and b unconstrained, f(a)=10, f(b)=20 --
    // no LIA fact forces a=b, so no congruence conflict -> decline.
    let no_eq = vec![
        app("=", vec![app("f", vec![sym("a")]), num("10")]),
        app("=", vec![app("f", vec![sym("b")]), num("20")]),
    ];
    assert!(emit_euf_lia_congruence_firewall_lean_from_parsed(&no_eq).is_none());

    // NEGATIVE (consistent values): a=b but f(a)=10, f(b)=10 -- no conflict.
    let consistent = vec![
        app("=", vec![sym("a"), num("3")]),
        app("=", vec![sym("b"), num("3")]),
        app("=", vec![app("f", vec![sym("a")]), num("10")]),
        app("=", vec![app("f", vec![sym("b")]), num("10")]),
    ];
    assert!(emit_euf_lia_congruence_firewall_lean_from_parsed(&consistent).is_none());

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
    assert!(emit_euf_lia_congruence_firewall_lean_from_parsed(&real).is_none());
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
