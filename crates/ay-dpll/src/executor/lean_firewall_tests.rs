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
        "namespace AySoundness.Emitted.Color",
        "inductive T where",
        "  | red",
        "  | green",
        "  | blue",
        "decide (c = T.red)",
        "decide (c = T.green)",
        "firewall_combined_unsat",
        "theorem no_model",
    ] {
        assert!(lean.contains(needle), "emitted Lean missing: {needle}");
    }
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
