// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
//! SUBSET_PROBE_MARKER_v1
//!
//! Hand-built minimal proofs, each judged by AY's INTERNAL checkers on the IR
//! AND written out as the matching Alethe document + SMT-LIB problem so the
//! SAME derivation can be handed to carcara. One IR in, two artefacts out —
//! no re-solve, no drift.
//!
//!   cargo run -p ay-proof --example subset_probe --release -- OUTDIR
//!
//! Prints one TSV line per probe: name, ay_nonstrict, ay_strict, ay_partial.

use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, Symbol, TermData, TermId, TermStore};
use std::collections::BTreeSet;

const MARKER: &str = "SUBSET_PROBE_MARKER_v1";

struct Probe {
    name: std::borrow::Cow<'static, str>,
    note: &'static str,
    terms: TermStore,
    proof: Proof,
    /// Problem assertions (usually the assume terms).
    assertions: Vec<TermId>,
}

fn collect_vars(terms: &TermStore, t: TermId, out: &mut BTreeSet<(String, &'static str)>) {
    match terms.get(t) {
        TermData::Var(name, _id) => {
            let s = match terms.sort(t) {
                Sort::Int => "Int",
                Sort::Real => "Real",
                _ => "Bool",
            };
            out.insert((name.to_string(), s));
        }
        TermData::Not(inner) => collect_vars(terms, *inner, out),
        TermData::App(_, args) => {
            for a in args.iter() {
                collect_vars(terms, *a, out);
            }
        }
        _ => {}
    }
}

fn emit(p: &Probe, outdir: &str) {
    // AY internal verdicts on the IR.
    let ns = match ay_proof::check_proof(&p.proof, &p.terms) {
        Ok(()) => "ACCEPT".to_string(),
        Err(e) => format!("reject({e})"),
    };
    let st = match ay_proof::check_proof_strict(&p.proof, &p.terms) {
        Ok(_) => "ACCEPT".to_string(),
        Err(e) => format!("reject({e})"),
    };
    let (_pp, perr) = ay_proof::check_proof_partial(&p.proof, &p.terms);
    let pa = match perr {
        None => "ACCEPT".to_string(),
        Some(e) => format!("reject({e})"),
    };
    println!("{}\t{}\t{}\t{}\t{}", p.name, pa, ns, st, p.note);

    // Alethe document, from the SAME IR.
    let doc = match ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &p.proof,
        &p.terms,
        &p.assertions,
        None,
    ) {
        Ok(s) => s,
        Err(e) => format!("; EXPORT ERROR: {e}\n"),
    };
    let _ = std::fs::write(format!("{outdir}/{}.alethe", p.name), doc);

    // Matching SMT-LIB problem.
    let mut vars: BTreeSet<(String, &'static str)> = BTreeSet::new();
    for step in &p.proof.steps {
        match step {
            ProofStep::Assume(t) => collect_vars(&p.terms, *t, &mut vars),
            ProofStep::Step { clause, args, .. } => {
                for t in clause.iter().chain(args.iter()) {
                    collect_vars(&p.terms, *t, &mut vars);
                }
            }
            _ => {}
        }
    }
    for a in &p.assertions {
        collect_vars(&p.terms, *a, &mut vars);
    }
    let mut smt = String::from("(set-logic QF_UF)\n");
    for (n, s) in &vars {
        smt.push_str(&format!("(declare-const {n} {s})\n"));
    }
    for a in &p.assertions {
        smt.push_str(&format!(
            "(assert {})\n",
            ay_proof::format_term_alethe(&p.terms, *a)
        ));
    }
    smt.push_str("(check-sat)\n(exit)\n");
    let _ = std::fs::write(format!("{outdir}/{}.smt2", p.name), smt);
}

/// Shorthand: a proof over a fresh store of Bool vars a,b,c,r,s.
struct V {
    t: TermStore,
    a: TermId,
    b: TermId,
    c: TermId,
    r: TermId,
    s: TermId,
}
impl V {
    fn new() -> Self {
        let mut t = TermStore::new();
        let a = t.mk_var("a", Sort::Bool);
        let b = t.mk_var("b", Sort::Bool);
        let c = t.mk_var("c", Sort::Bool);
        let r = t.mk_var("r", Sort::Bool);
        let s = t.mk_var("s", Sort::Bool);
        Self { t, a, b, c, r, s }
    }
    fn not(&mut self, x: TermId) -> TermId {
        self.t.mk_not(x)
    }
    fn or(&mut self, xs: Vec<TermId>) -> TermId {
        self.t.mk_app(Symbol::Named("or".into()), xs, Sort::Bool)
    }
    fn and(&mut self, xs: Vec<TermId>) -> TermId {
        self.t.mk_app(Symbol::Named("and".into()), xs, Sort::Bool)
    }
}

fn res(clause: Vec<TermId>, premises: Vec<usize>, args: Vec<TermId>) -> ProofStep {
    ProofStep::Step {
        rule: AletheRule::Resolution,
        clause,
        premises: premises.into_iter().map(|i| ProofId(i as u32)).collect(),
        args,
    }
}
fn orstep(clause: Vec<TermId>, premise: usize) -> ProofStep {
    ProofStep::Step {
        rule: AletheRule::Or,
        clause,
        premises: vec![ProofId(premise as u32)],
        args: vec![],
    }
}

fn main() {
    eprintln!("{MARKER}");
    let outdir = std::env::args().nth(1).unwrap_or_else(|| ".".to_string());
    let _ = std::fs::create_dir_all(&outdir);
    let mut probes: Vec<Probe> = Vec::new();

    // ============ A: :args on the resolution path ============================
    // Chain {p}, {not p, q}, {not q} |- {} carrying a JUNK one-term :args.
    for (name, args_kind, note) in [
        ("A0_nary_noargs", 0u8, "control: no args"),
        ("A1_nary_junk1arg", 1, "ONE arg on a 2-link chain"),
        (
            "A2_nary_wrongpivot",
            2,
            "args name a pivot not in the clause",
        ),
        ("A3_nary_nonsense", 3, "args are unrelated terms"),
    ] {
        // Shape: assume a; assume (or (not a) b); assume (not b).
        let mut v2 = V::new();
        let (a2, b2, c2) = (v2.a, v2.b, v2.c);
        let na2 = v2.not(a2);
        let nb2 = v2.not(b2);
        let na2_or_b2 = v2.or(vec![na2, b2]);
        let mut p2 = Proof::new();
        p2.add_step(ProofStep::Assume(a2)); // 0
        p2.add_step(ProofStep::Assume(na2_or_b2)); // 1
        p2.add_step(ProofStep::Assume(nb2)); // 2
        p2.add_step(orstep(vec![na2, b2], 1)); // 3
        let args = match args_kind {
            0 => vec![],
            1 => vec![a2],
            2 => vec![b2, a2],
            _ => vec![c2, c2],
        };
        p2.add_step(res(vec![], vec![0, 3, 2], args)); // 4
        probes.push(Probe {
            name: name.into(),
            note,
            assertions: vec![a2, na2_or_b2, nb2],
            terms: v2.t,
            proof: p2,
        });
    }

    // Binary resolution with a one-term :args (AY's internal pivot form).
    {
        let mut v = V::new();
        let (a, b) = (v.a, v.b);
        let na = v.not(a);
        let nb = v.not(b);
        let na_or_b = v.or(vec![na, b]);
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(a));
        p.add_step(ProofStep::Assume(na_or_b));
        p.add_step(ProofStep::Assume(nb));
        p.add_step(orstep(vec![na, b], 1)); // 3
        p.add_step(res(vec![b], vec![0, 3], vec![a])); // 4
        p.add_step(res(vec![], vec![4, 2], vec![b])); // 5
        probes.push(Probe {
            name: "A4_binary_1arg".into(),
            note: "binary res with ONE arg",
            assertions: vec![a, na_or_b, nb],
            terms: v.t,
            proof: p,
        });
    }
    // Binary with junk arg (pivot not present at all).
    {
        let mut v = V::new();
        let (a, b, c) = (v.a, v.b, v.c);
        let na = v.not(a);
        let nb = v.not(b);
        let na_or_b = v.or(vec![na, b]);
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(a));
        p.add_step(ProofStep::Assume(na_or_b));
        p.add_step(ProofStep::Assume(nb));
        p.add_step(orstep(vec![na, b], 1));
        p.add_step(res(vec![b], vec![0, 3], vec![c])); // junk pivot c
        p.add_step(res(vec![], vec![4, 2], vec![b]));
        probes.push(Probe {
            name: "A5_binary_junkpivot".into(),
            note: "binary res, pivot term absent from both premises",
            assertions: vec![a, na_or_b, nb],
            terms: v.t,
            proof: p,
        });
    }

    // ============ B: De Morgan complement pairing ============================
    // {(and a b), not r}, {(or (not a)(not b)), s}, {r} |- {s}, then {not s}.
    {
        let mut v = V::new();
        let (a, b, r, s) = (v.a, v.b, v.r, v.s);
        let na = v.not(a);
        let nb = v.not(b);
        let nr = v.not(r);
        let ns = v.not(s);
        let and_ab = v.and(vec![a, b]);
        let or_nanb = v.or(vec![na, nb]);
        let c0 = v.or(vec![and_ab, nr]);
        let c1 = v.or(vec![or_nanb, s]);
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(c0)); // 0
        p.add_step(ProofStep::Assume(c1)); // 1
        p.add_step(ProofStep::Assume(r)); // 2
        p.add_step(ProofStep::Assume(ns)); // 3
        p.add_step(orstep(vec![and_ab, nr], 0)); // 4
        p.add_step(orstep(vec![or_nanb, s], 1)); // 5
        p.add_step(res(vec![], vec![4, 5, 2, 3], vec![])); // 6 n-ary
        probes.push(Probe {
            name: "B0_demorgan_nary".into(),
            note: "(and a b) vs (or (not a)(not b)) as complements, n-ary",
            assertions: vec![c0, c1, r, ns],
            terms: v.t,
            proof: p,
        });
    }
    {
        let mut v = V::new();
        let (a, b, r, s) = (v.a, v.b, v.r, v.s);
        let na = v.not(a);
        let nb = v.not(b);
        let nr = v.not(r);
        let ns = v.not(s);
        let and_ab = v.and(vec![a, b]);
        let or_nanb = v.or(vec![na, nb]);
        let c0 = v.or(vec![and_ab, nr]);
        let c1 = v.or(vec![or_nanb, s]);
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(c0));
        p.add_step(ProofStep::Assume(c1));
        p.add_step(ProofStep::Assume(r));
        p.add_step(ProofStep::Assume(ns));
        p.add_step(orstep(vec![and_ab, nr], 0)); // 4
        p.add_step(orstep(vec![or_nanb, s], 1)); // 5
        p.add_step(res(vec![nr, s], vec![4, 5], vec![])); // 6 BINARY
        p.add_step(res(vec![s], vec![6, 2], vec![])); // 7
        p.add_step(res(vec![], vec![7, 3], vec![])); // 8
        probes.push(Probe {
            name: "B1_demorgan_binary".into(),
            note: "same pairing on the BINARY path",
            assertions: vec![c0, c1, r, ns],
            terms: v.t,
            proof: p,
        });
    }
    // B2: permuted De Morgan — (and a b) vs (or (not b)(not a)).
    {
        let mut v = V::new();
        let (a, b, r, s) = (v.a, v.b, v.r, v.s);
        let na = v.not(a);
        let nb = v.not(b);
        let nr = v.not(r);
        let ns = v.not(s);
        let and_ab = v.and(vec![a, b]);
        let or_nbna = v.or(vec![nb, na]);
        let c0 = v.or(vec![and_ab, nr]);
        let c1 = v.or(vec![or_nbna, s]);
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(c0));
        p.add_step(ProofStep::Assume(c1));
        p.add_step(ProofStep::Assume(r));
        p.add_step(ProofStep::Assume(ns));
        p.add_step(orstep(vec![and_ab, nr], 0));
        p.add_step(orstep(vec![or_nbna, s], 1));
        p.add_step(res(vec![], vec![4, 5, 2, 3], vec![]));
        probes.push(Probe {
            name: "B2_demorgan_permuted".into(),
            note: "(and a b) vs (or (not b)(not a)) — order-insensitive pairing",
            assertions: vec![c0, c1, r, ns],
            terms: v.t,
            proof: p,
        });
    }
    // B3: (or a b) vs (and (not a)(not b)) — the mirror direction.
    {
        let mut v = V::new();
        let (a, b, r, s) = (v.a, v.b, v.r, v.s);
        let na = v.not(a);
        let nb = v.not(b);
        let nr = v.not(r);
        let ns = v.not(s);
        let or_ab = v.or(vec![a, b]);
        let and_nanb = v.and(vec![na, nb]);
        let c0 = v.or(vec![or_ab, nr]);
        let c1 = v.or(vec![and_nanb, s]);
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(c0));
        p.add_step(ProofStep::Assume(c1));
        p.add_step(ProofStep::Assume(r));
        p.add_step(ProofStep::Assume(ns));
        p.add_step(orstep(vec![or_ab, nr], 0));
        p.add_step(orstep(vec![and_nanb, s], 1));
        p.add_step(res(vec![], vec![4, 5, 2, 3], vec![]));
        probes.push(Probe {
            name: "B3_demorgan_mirror".into(),
            note: "(or a b) vs (and (not a)(not b))",
            assertions: vec![c0, c1, r, ns],
            terms: v.t,
            proof: p,
        });
    }

    // ============ C: empty-accumulator absorption (reverse cell) =============
    {
        let mut v = V::new();
        let (a, b) = (v.a, v.b);
        let na = v.not(a);
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(a)); // 0
        p.add_step(ProofStep::Assume(na)); // 1
        p.add_step(ProofStep::Assume(b)); // 2
        p.add_step(res(vec![], vec![0, 1, 2], vec![])); // 3
        probes.push(Probe {
            name: "C0_absorb_after_empty".into(),
            note: "carcara absorbs the trailing premise; does AY?",
            assertions: vec![a, na, b],
            terms: v.t,
            proof: p,
        });
    }
    // C1: absorption where the trailing premise is a REPEAT of an earlier one.
    {
        let mut v = V::new();
        let (a, b) = (v.a, v.b);
        let na = v.not(a);
        let nb = v.not(b);
        let na_or_b = v.or(vec![na, b]);
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(a)); // 0
        p.add_step(ProofStep::Assume(na_or_b)); // 1
        p.add_step(ProofStep::Assume(nb)); // 2
        p.add_step(orstep(vec![na, b], 1)); // 3
        p.add_step(res(vec![], vec![0, 3, 2, 0], vec![])); // 4 trailing repeat
        probes.push(Probe {
            name: "C1_absorb_repeat".into(),
            note: "chain reaches empty, then one more premise",
            assertions: vec![a, na_or_b, nb],
            terms: v.t,
            proof: p,
        });
    }

    // ============ D: double negation =========================================
    {
        let mut v = V::new();
        let a = v.a;
        let na = v.not(a);
        let nna = v.not(na);
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(nna)); // 0
        p.add_step(ProofStep::Assume(na)); // 1
        p.add_step(res(vec![], vec![0, 1], vec![])); // 2
        probes.push(Probe {
            name: "D0_double_negation".into(),
            note: "(not (not a)) vs (not a)",
            assertions: vec![nna, na],
            terms: v.t,
            proof: p,
        });
    }

    // ============ E: tautological / duplicate-literal shapes =================
    {
        let mut v = V::new();
        let a = v.a;
        let na = v.not(a);
        let a_or_a = v.or(vec![a, a]);
        let na_or_na = v.or(vec![na, na]);
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(a_or_a)); // 0
        p.add_step(ProofStep::Assume(na_or_na)); // 1
        p.add_step(orstep(vec![a, a], 0)); // 2
        p.add_step(orstep(vec![na, na], 1)); // 3
        p.add_step(res(vec![], vec![2, 3], vec![])); // 4
        probes.push(Probe {
            name: "E0_duplicate_literals".into(),
            note: "(cl a a) x (cl (not a)(not a)) |- (cl)",
            assertions: vec![a_or_a, na_or_na],
            terms: v.t,
            proof: p,
        });
    }
    // E1: resolvent that keeps a tautological pair {a, not a}.
    {
        let mut v = V::new();
        let (a, b) = (v.a, v.b);
        let na = v.not(a);
        let nb = v.not(b);
        let a_or_b = v.or(vec![a, b]);
        let na_or_nb = v.or(vec![na, nb]);
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(a_or_b)); // 0
        p.add_step(ProofStep::Assume(na_or_nb)); // 1
        p.add_step(orstep(vec![a, b], 0)); // 2
        p.add_step(orstep(vec![na, nb], 1)); // 3
        p.add_step(res(vec![b, nb], vec![2, 3], vec![])); // 4 tautological resolvent
        probes.push(Probe {
            name: "E1_tautological_resolvent".into(),
            note: "resolvent {b, not b}",
            assertions: vec![a_or_b, na_or_nb],
            terms: v.t,
            proof: p,
        });
    }

    // ============ F: `or` clausification order ===============================
    {
        let mut v = V::new();
        let (a, b) = (v.a, v.b);
        let na = v.not(a);
        let nb = v.not(b);
        let a_or_b = v.or(vec![a, b]);
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(a_or_b)); // 0
        p.add_step(ProofStep::Assume(na)); // 1
        p.add_step(ProofStep::Assume(nb)); // 2
        p.add_step(orstep(vec![b, a], 0)); // 3 PERMUTED
        p.add_step(res(vec![], vec![3, 1, 2], vec![])); // 4
        probes.push(Probe {
            name: "F0_or_permuted".into(),
            note: "`or` conclusion permuted vs the premise disjunct order",
            assertions: vec![a_or_b, na, nb],
            terms: v.t,
            proof: p,
        });
    }
    {
        let mut v = V::new();
        let (a, b) = (v.a, v.b);
        let na = v.not(a);
        let nb = v.not(b);
        let a_or_b = v.or(vec![a, b]);
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(a_or_b));
        p.add_step(ProofStep::Assume(na));
        p.add_step(ProofStep::Assume(nb));
        p.add_step(orstep(vec![a, b], 0));
        p.add_step(res(vec![], vec![3, 1, 2], vec![]));
        probes.push(Probe {
            name: "F1_or_inorder".into(),
            note: "control",
            assertions: vec![a_or_b, na, nb],
            terms: v.t,
            proof: p,
        });
    }
    // F2: `or` conclusion drops a duplicate disjunct.
    {
        let mut v = V::new();
        let a = v.a;
        let na = v.not(a);
        let a_or_a = v.or(vec![a, a]);
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(a_or_a)); // 0
        p.add_step(ProofStep::Assume(na)); // 1
        p.add_step(orstep(vec![a], 0)); // 2 DEDUPED conclusion
        p.add_step(res(vec![], vec![2, 1], vec![])); // 3
        probes.push(Probe {
            name: "F2_or_deduped".into(),
            note: "`or` on (or a a) concluding (cl a)",
            assertions: vec![a_or_a, na],
            terms: v.t,
            proof: p,
        });
    }

    // ============ G: n-ary arity sweep =======================================
    for n in [2usize, 3, 5, 8, 40] {
        // Chain: (cl x0), (cl (not x0) x1), ..., (cl (not x_{n-1})) |- (cl)
        let mut t = TermStore::new();
        let xs: Vec<TermId> = (0..n)
            .map(|i| t.mk_var(&format!("x{i}"), Sort::Bool))
            .collect();
        let nxs: Vec<TermId> = xs.iter().map(|&x| t.mk_not(x)).collect();
        let mut p = Proof::new();
        let mut assertions = Vec::new();
        p.add_step(ProofStep::Assume(xs[0]));
        assertions.push(xs[0]);
        let mut prem: Vec<usize> = vec![0];
        let mut idx = 1usize;
        for i in 1..n {
            let o = t.mk_app(
                Symbol::Named("or".into()),
                vec![nxs[i - 1], xs[i]],
                Sort::Bool,
            );
            p.add_step(ProofStep::Assume(o));
            assertions.push(o);
            idx += 1;
        }
        p.add_step(ProofStep::Assume(nxs[n - 1]));
        assertions.push(nxs[n - 1]);
        let last_assume = idx;
        idx += 1;
        for i in 1..n {
            p.add_step(ProofStep::Step {
                rule: AletheRule::Or,
                clause: vec![nxs[i - 1], xs[i]],
                premises: vec![ProofId(i as u32)],
                args: vec![],
            });
            prem.push(idx);
            idx += 1;
        }
        prem.push(last_assume);
        p.add_step(res(vec![], prem, vec![]));
        probes.push(Probe {
            name: format!("G{n}_chain_arity").into(),
            note: "arity sweep",
            assertions,
            terms: t,
            proof: p,
        });
    }

    // ============ H: bogus n-ary that reaches the target by luck =============
    // {a, b}, {not a, b}, {not b} |- (cl) — genuinely valid, needs b twice.
    {
        let mut v = V::new();
        let (a, b) = (v.a, v.b);
        let na = v.not(a);
        let nb = v.not(b);
        let a_or_b = v.or(vec![a, b]);
        let na_or_b = v.or(vec![na, b]);
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(a_or_b)); // 0
        p.add_step(ProofStep::Assume(na_or_b)); // 1
        p.add_step(ProofStep::Assume(nb)); // 2
        p.add_step(orstep(vec![a, b], 0)); // 3
        p.add_step(orstep(vec![na, b], 1)); // 4
        p.add_step(res(vec![], vec![3, 4, 2], vec![])); // 5
        probes.push(Probe {
            name: "H0_merge_literal".into(),
            note: "chain where the merged literal b survives one link",
            assertions: vec![a_or_b, na_or_b, nb],
            terms: v.t,
            proof: p,
        });
    }

    // ============ J: Boolean constants as resolution atoms ===================
    {
        let mut v = V::new();
        let a = v.a;
        let na = v.not(a);
        let ff = v.t.mk_bool(false);
        let a_or_false = v.or(vec![a, ff]);
        let na_or_false = v.or(vec![na, ff]);
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(a_or_false)); // 0
        p.add_step(ProofStep::Assume(na_or_false)); // 1
        p.add_step(orstep(vec![a, ff], 0)); // 2
        p.add_step(orstep(vec![na, ff], 1)); // 3
        p.add_step(res(vec![ff, ff], vec![2, 3], vec![])); // 4
        probes.push(Probe {
            name: "J0_false_literal_survives".into(),
            note: "resolvent keeps two `false` literals",
            assertions: vec![a_or_false, na_or_false],
            terms: v.t,
            proof: p,
        });
    }
    // J1: resolve directly ON the Boolean constants true/false.
    {
        let mut v = V::new();
        let a = v.a;
        let tt = v.t.mk_bool(true);
        let ff = v.t.mk_bool(false);
        let a_or_true = v.or(vec![a, tt]);
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(a_or_true)); // 0
        p.add_step(ProofStep::Assume(ff)); // 1
        p.add_step(orstep(vec![a, tt], 0)); // 2
        p.add_step(res(vec![a], vec![2, 1], vec![])); // 3 pivot true/false
        probes.push(Probe {
            name: "J1_true_false_pivot".into(),
            note: "resolve `true` against `false` as complements",
            assertions: vec![a_or_true, ff],
            terms: v.t,
            proof: p,
        });
    }

    // ============ I: assume vs the PROBLEM ===================================
    // `check_proof_partial` takes no problem assertions at all, so it cannot
    // police the assume<->premise correspondence carcara enforces. These probes
    // keep the emitted .smt2 DIFFERENT from the assume terms on purpose.
    {
        // I0: assume a CONJUNCT of a top-level (and p q) assertion.
        let mut v = V::new();
        let (a, b) = (v.a, v.b);
        let na = v.not(a);
        let and_ab = v.and(vec![a, b]);
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(a)); // 0
        p.add_step(ProofStep::Assume(na)); // 1
        p.add_step(res(vec![], vec![0, 1], vec![])); // 2
        probes.push(Probe {
            name: "I0_assume_conjunct".into(),
            note: "problem asserts (and a b); proof assumes a",
            assertions: vec![and_ab, na],
            terms: v.t,
            proof: p,
        });
    }
    {
        // I1: assume a term that is NOWHERE in the problem.
        let mut v = V::new();
        let (a, b) = (v.a, v.b);
        let na = v.not(a);
        let nb = v.not(b);
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(b)); // 0
        p.add_step(ProofStep::Assume(nb)); // 1
        p.add_step(res(vec![], vec![0, 1], vec![])); // 2
        probes.push(Probe {
            name: "I1_assume_ghost".into(),
            note: "problem asserts a / (not a); proof assumes b / (not b)",
            assertions: vec![a, na],
            terms: v.t,
            proof: p,
        });
    }

    println!("name\tay_partial\tay_nonstrict\tay_strict\tnote");
    for p in &probes {
        emit(p, &outdir);
    }
}
