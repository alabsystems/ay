// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_LRA(+Bool) proof interpolation end to end through the public API, in
//! the fail-closed `InterpolantMode::Explicit` mode
//! (`Solver::get_interpolants_for_masks`). Every served interpolant is
//! Craig-checked by a fresh solver (`A ∧ ¬I` and `I ∧ B` UNSAT, symbols of
//! `I` shared). Workstream D Rung 1 (`DESIGN_lra_interp_tpa.md` §4.1),
//! owner WP-D1-P.

use std::collections::HashSet;

use ay_dpll::api::{
    split_leading_set_logic, InterpolantFailure, InterpolantMode, InterpolantStrength, Logic,
    Solver, Term, TermKind,
};

const ALL: [InterpolantStrength; 3] = [
    InterpolantStrength::Strongest,
    InterpolantStrength::Default,
    InterpolantStrength::Weakest,
];

/// A query: declarations plus asserts, group by group.
struct Query {
    decls: &'static str,
    groups: Vec<Vec<&'static str>>,
}

impl Query {
    fn script(&self) -> String {
        let mut s = String::from("(set-logic QF_LRA)\n");
        s.push_str(self.decls);
        for g in &self.groups {
            for a in g {
                s.push_str(&format!("(assert {a})\n"));
            }
        }
        s
    }

    /// Solve with interpolation proofs (the mode the CHC engines use for
    /// QF_LRA); returns the solver and the parsed groups.
    fn solve(&self) -> (Solver, Vec<Vec<Term>>) {
        let script = self.script();
        let (logic, body) = split_leading_set_logic(&script, Logic::QfLra);
        let mut solver = Solver::try_new(logic).expect("QF_LRA solver");
        solver.set_interpolation_proofs(10_000_000);
        solver.set_option(":ay-proof-no-varsubst", "true");
        let asserts = solver.parse_smtlib2(&body).expect("query parses");
        let mut groups = Vec::new();
        let mut at = 0;
        for g in &self.groups {
            groups.push(asserts[at..at + g.len()].to_vec());
            at += g.len();
        }
        assert_eq!(at, asserts.len(), "one term per assert");
        let result = solver.check_sat_internal_query();
        assert!(result.is_unsat(), "query must be UNSAT, got {result:?}");
        (solver, groups)
    }

    fn side_asserts(&self, mask: u128, a_side: bool) -> Vec<&'static str> {
        self.groups
            .iter()
            .enumerate()
            .filter(|(g, _)| (mask & (1u128 << g) != 0) == a_side)
            .flat_map(|(_, asserts)| asserts.iter().copied())
            .collect()
    }

    fn verdict(&self, asserts: &[&str], extra: &str) -> &'static str {
        let mut s = String::from("(set-logic QF_LRA)\n");
        s.push_str(self.decls);
        for a in asserts {
            s.push_str(&format!("(assert {a})\n"));
        }
        s.push_str(&format!("(assert {extra})\n"));
        let (logic, body) = split_leading_set_logic(&s, Logic::QfLra);
        let mut solver = Solver::try_new(logic).expect("QF_LRA solver");
        solver.parse_smtlib2(&body).expect("check script parses");
        let r = solver.check_sat();
        if r.is_unsat() {
            "unsat"
        } else if r.is_sat() {
            "sat"
        } else {
            "unknown"
        }
    }

    /// The three Craig conditions for `itp` (SMT-LIB text) and `mask`.
    fn assert_craig(&self, mask: u128, itp: &str, vars: &HashSet<String>, what: &str) {
        let a = self.side_asserts(mask, true);
        let b = self.side_asserts(mask, false);
        assert_eq!(
            self.verdict(&a, &format!("(not {itp})")),
            "unsat",
            "{what}: A must entail I = {itp}"
        );
        assert_eq!(
            self.verdict(&b, itp),
            "unsat",
            "{what}: I ∧ B must be UNSAT, I = {itp}"
        );
        let shared = self.shared_names(mask);
        assert!(
            vars.is_subset(&shared),
            "{what}: I = {itp} mentions non-shared {:?}",
            vars.difference(&shared).collect::<Vec<_>>()
        );
    }

    /// Declared names occurring on both sides (by token scan of the text).
    fn shared_names(&self, mask: u128) -> HashSet<String> {
        let names: Vec<String> = self
            .decls
            .lines()
            .filter_map(|l| l.split_whitespace().nth(1).map(str::to_string))
            .collect();
        let mentions = |asserts: &[&str], n: &str| {
            asserts.iter().any(|a| {
                a.split(|c: char| c == '(' || c == ')' || c.is_whitespace())
                    .any(|tok| tok == n)
            })
        };
        let a = self.side_asserts(mask, true);
        let b = self.side_asserts(mask, false);
        names
            .into_iter()
            .filter(|n| mentions(&a, n) && mentions(&b, n))
            .collect()
    }
}

fn term_vars(solver: &Solver, t: Term, out: &mut HashSet<String>) {
    let mut stack = vec![t];
    let mut seen = HashSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match solver.term_kind(t) {
            TermKind::Var { name } => {
                out.insert(name);
            }
            TermKind::Const => {}
            _ => stack.extend(solver.term_children(t)),
        }
    }
}

fn explicit(
    solver: &mut Solver,
    groups: &[Vec<Term>],
    masks: &[u128],
    strength: InterpolantStrength,
) -> Result<Vec<Term>, InterpolantFailure> {
    let slices: Vec<&[Term]> = groups.iter().map(Vec::as_slice).collect();
    solver.get_interpolants_for_masks(&slices, masks, strength, InterpolantMode::Explicit)
}

fn serve_and_check(q: &Query, mask: u128, strength: InterpolantStrength) -> String {
    let (mut solver, groups) = q.solve();
    let itp = explicit(&mut solver, &groups, &[mask], strength)
        .unwrap_or_else(|e| panic!("{strength:?}: explicit extraction failed: {e}"))[0];
    let text = solver.format_term(itp);
    let mut vars = HashSet::new();
    term_vars(&solver, itp, &mut vars);
    q.assert_craig(mask, &text, &vars, &format!("{strength:?}"));
    text
}

const XYZ: &str = "(declare-const x Real)\n(declare-const y Real)\n(declare-const z Real)\n";

#[test]
fn strict_real_rows_are_not_tightened() {
    let q = Query {
        decls: XYZ,
        groups: vec![vec!["(< x y)", "(< y z)"], vec!["(<= z x)"]],
    };
    for strength in ALL {
        let itp = serve_and_check(&q, 0b01, strength);
        // A tightened (integer) row `x + 1 <= z` would refute x = 0, z = 1/2.
        assert_eq!(
            q.verdict(&["(= x 0.0)", "(= z 0.5)"], &itp),
            "sat",
            "{strength:?}: Real strict row must stay strict and untightened: {itp}"
        );
    }
}

#[test]
fn mcmillan_on_a_disjunction() {
    let q = Query {
        decls: "(declare-const p Bool)\n(declare-const q Bool)\n",
        groups: vec![vec!["(or p q)"], vec!["(not p)", "(not q)"]],
    };
    serve_and_check(&q, 0b01, InterpolantStrength::Strongest);
}

#[test]
fn shared_composite_subterm() {
    let q = Query {
        decls: "(declare-const p Bool)\n(declare-const q Bool)\n(declare-const x Real)\n",
        groups: vec![
            vec!["(and p q)", "(=> p (> x 0.0))"],
            vec!["(not (and p q))"],
        ],
    };
    for strength in ALL {
        serve_and_check(&q, 0b01, strength);
    }
}

#[test]
fn four_group_path_interpolants_have_the_sequence_property() {
    let q = Query {
        decls: "(declare-const x0 Real)\n(declare-const x1 Real)\n(declare-const x2 Real)\n",
        groups: vec![
            vec!["(= x0 0.0)"],
            vec!["(= x1 (+ x0 1.0))"],
            vec!["(= x2 (+ x1 1.0))"],
            vec!["(> x2 5.0)"],
        ],
    };
    let (mut solver, groups) = q.solve();
    let itps = explicit(
        &mut solver,
        &groups,
        &[0b0001, 0b0011, 0b0111],
        InterpolantStrength::Strongest,
    )
    .unwrap_or_else(|e| panic!("path interpolants failed: {e}"));
    assert_eq!(itps.len(), 3);
    let texts: Vec<String> = itps.iter().map(|&t| solver.format_term(t)).collect();
    for (i, (&itp, text)) in itps.iter().zip(&texts).enumerate() {
        let mask = (1u128 << (i + 1)) - 1;
        let mut vars = HashSet::new();
        term_vars(&solver, itp, &mut vars);
        q.assert_craig(mask, text, &vars, &format!("cut {i}"));
    }
    // Sequence property: I_i ∧ G_{i+1} ⊨ I_{i+1}.
    for i in 0..2 {
        let g = &q.groups[i + 1];
        let mut asserts: Vec<&str> = g.clone();
        asserts.push(&texts[i]);
        assert_eq!(
            q.verdict(&asserts, &format!("(not {})", texts[i + 1])),
            "unsat",
            "I{} ∧ G{} must entail I{}",
            i + 1,
            i + 2,
            i + 2
        );
    }
}

#[test]
fn ite_transition_in_two_copies_is_served() {
    // 2 Bool + 3 Real state vars, two unrolled copies of an ITE transition;
    // IMC cut after the first copy. x never exceeds 2 after two steps. The
    // QF_LRA lane Shannon-lifts every arithmetic `ite`, so each transition
    // leaf of the refutation is a preprocessed assertion: it must be
    // attributed to its group through the recorded sources, not refused.
    let q = Query {
        decls: "(declare-const p0 Bool)\n(declare-const q0 Bool)\n\
                (declare-const x0 Real)\n(declare-const y0 Real)\n(declare-const z0 Real)\n\
                (declare-const p1 Bool)\n(declare-const q1 Bool)\n\
                (declare-const x1 Real)\n(declare-const y1 Real)\n(declare-const z1 Real)\n\
                (declare-const p2 Bool)\n(declare-const q2 Bool)\n\
                (declare-const x2 Real)\n(declare-const y2 Real)\n(declare-const z2 Real)\n",
        groups: vec![
            vec![
                "(= x0 0.0)",
                "(= y0 0.0)",
                "(= z0 0.0)",
                "p0",
                "q0",
                "(= x1 (ite p0 (+ x0 1.0) x0))",
                "(= y1 (ite q0 (+ y0 x0) y0))",
                "(= z1 z0)",
                "(= p1 (not p0))",
                "(= q1 q0)",
            ],
            vec![
                "(= x2 (ite p1 (+ x1 1.0) x1))",
                "(= y2 (ite q1 (+ y1 x1) y1))",
                "(= z2 z1)",
                "(= p2 (not p1))",
                "(= q2 q1)",
                "(>= x2 3.0)",
            ],
        ],
    };
    for strength in ALL {
        serve_and_check(&q, 0b01, strength);
    }
}

#[test]
fn guarded_ite_update_inside_a_disjunction_is_served() {
    // The oral_messages transition shape: an arithmetic `ite` selected by a
    // mode variable, inside one disjunct of the transition. Both copies are
    // preprocessed (split equality, Shannon lift) before the core sees them.
    let q = Query {
        decls: "(declare-const p0 Bool)\n(declare-const p1 Bool)\n\
                (declare-const m0 Real)\n(declare-const m1 Real)\n\
                (declare-const x0 Real)\n(declare-const x1 Real)\n(declare-const x2 Real)\n",
        groups: vec![
            vec![
                "(= x0 0.0)",
                "(= m0 1.0)",
                "(or (and p0 (= x1 (ite (= m0 1.0) (+ x0 1.0) x0))) (and (not p0) (= x1 x0)))",
                "(= m1 m0)",
            ],
            vec![
                "(or (and p1 (= x2 (ite (= m1 1.0) (+ x1 1.0) x1))) (and (not p1) (= x2 x1)))",
                "(> x2 2.0)",
            ],
        ],
    };
    for strength in ALL {
        serve_and_check(&q, 0b01, strength);
    }
}

#[test]
fn real_constants_print_in_the_pinned_forms() {
    // `ay-chc`'s `proof_script::parse_const_text` parses exactly these forms.
    let q = Query {
        decls: XYZ,
        groups: vec![
            vec!["(= x (/ 3 2))", "(= y (- 5.0))"],
            vec!["(= z (- (/ 3 2)))", "(> (+ x y z) 7.0)"],
        ],
    };
    let script = q.script();
    let (logic, body) = split_leading_set_logic(&script, Logic::QfLra);
    let mut solver = Solver::try_new(logic).expect("QF_LRA solver");
    let asserts = solver.parse_smtlib2(&body).expect("parses");
    let mut consts = Vec::new();
    let mut stack: Vec<Term> = asserts;
    while let Some(t) = stack.pop() {
        match solver.term_kind(t) {
            TermKind::Const => consts.push(solver.format_term(t)),
            TermKind::Var { .. } => {}
            _ => stack.extend(solver.term_children(t)),
        }
    }
    for c in &consts {
        let ok = c.ends_with(".0")
            || c.ends_with(".0)")
            || (c.starts_with("(/ ") || c.starts_with("(- (/ "));
        assert!(ok, "unpinned Real constant form: {c}");
    }
    assert!(consts.iter().any(|c| c == "(/ 3 2)" || c == "(- (/ 3 2))"));
}

#[test]
fn malformed_masks_and_missing_proofs_are_reported() {
    let q = Query {
        decls: XYZ,
        groups: vec![vec!["(< x y)"], vec!["(< y x)"]],
    };
    let (mut solver, groups) = q.solve();
    for mask in [0u128, 0b11, 0b100] {
        assert_eq!(
            explicit(&mut solver, &groups, &[mask], InterpolantStrength::Default),
            Err(InterpolantFailure::InvalidGroups),
            "mask {mask:#b}"
        );
    }
    // Without proof production there is no proof to read.
    let script = q.script();
    let (logic, body) = split_leading_set_logic(&script, Logic::QfLra);
    let mut plain = Solver::try_new(logic).expect("QF_LRA solver");
    let asserts = plain.parse_smtlib2(&body).expect("parses");
    assert!(plain.check_sat().is_unsat());
    let groups = vec![vec![asserts[0]], vec![asserts[1]]];
    assert_eq!(
        explicit(&mut plain, &groups, &[0b01], InterpolantStrength::Default),
        Err(InterpolantFailure::NoProof)
    );
}
