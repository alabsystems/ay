// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
//! Minimal hand-built proofs that isolate each suspected divergence between
//! AY's INTERNAL proof checker and carcara 1.1.0.
//!
//! Each probe builds the proof IR directly, runs `check_proof` (non-strict, the
//! gate behind `proof.rs`'s re-derivation) and `check_proof_strict` (the
//! shipped strict boundary), and prints the verdict. The matching Alethe TEXT
//! for each probe lives beside this file in the harness and is fed to carcara
//! separately, so both checkers judge the SAME derivation.
//!
//!   cargo run -p ay-proof --example carcara_divergence_probe --release

use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, Symbol, TermStore};

fn verdicts(name: &str, note: &str, proof: &Proof, terms: &TermStore) {
    let ns = match ay_proof::check_proof(proof, terms) {
        Ok(()) => "ACCEPT".to_string(),
        Err(e) => format!("reject({e})"),
    };
    let st = match ay_proof::check_proof_strict(proof, terms) {
        Ok(_) => "ACCEPT".to_string(),
        Err(e) => format!("reject({e})"),
    };
    let (_p, perr) = ay_proof::check_proof_partial(proof, terms);
    let pa = match perr {
        None => "ACCEPT".to_string(),
        Some(e) => format!("reject({e})"),
    };
    println!("{name:<28} nonstrict={ns:<24} strict={st:<44} partial={pa:<24} :: {note}");
}

fn main() {
    // ---------------------------------------------------------------- setup
    // Shared vocabulary: a, b, c : Bool.
    let mut t = TermStore::new();
    let a = t.mk_var("a", Sort::Bool);
    let b = t.mk_var("b", Sort::Bool);
    let c = t.mk_var("c", Sort::Bool);
    let na = t.mk_not(a);
    let nb = t.mk_not(b);
    let nc = t.mk_not(c);
    let a_or_b = t.mk_app(Symbol::Named("or".into()), [a, b], Sort::Bool);
    let na_or_c = t.mk_app(Symbol::Named("or".into()), [na, c], Sort::Bool);

    // ============================================================== PROBE A
    // `:args` on the RESOLUTION path.
    //
    // IR: h0..h3 assumes; t0/t1 `or` clausification; then ONE n-ary
    // `Step { rule: Resolution, premises: [t0,h2,t1,h3], args: [pivot] }`.
    // AY's chain path ignores `args` entirely; AY's PRINTER emits every arg
    // verbatim, so the document carries one term where carcara wants 2 per
    // link.
    {
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(a_or_b)); // 0 h0
        p.add_step(ProofStep::Assume(na_or_c)); // 1 h1
        p.add_step(ProofStep::Assume(nb)); // 2 h2
        p.add_step(ProofStep::Assume(nc)); // 3 h3
        p.add_step(ProofStep::Step {
            rule: AletheRule::Or,
            clause: vec![a, b],
            premises: vec![ProofId(0)],
            args: vec![],
        }); // 4 t0
        p.add_step(ProofStep::Step {
            rule: AletheRule::Or,
            clause: vec![na, c],
            premises: vec![ProofId(1)],
            args: vec![],
        }); // 5 t1
        p.add_step(ProofStep::Step {
            rule: AletheRule::Resolution,
            clause: vec![],
            premises: vec![ProofId(4), ProofId(2), ProofId(5), ProofId(3)],
            args: vec![b], // ONE arg for a 3-link chain
        }); // 6
        verdicts(
            "A2 nary_onearg",
            "carcara: expected 6 arguments, got 1 -> INVALID",
            &p,
            &t,
        );
    }

    // A3: BINARY resolution steps each carrying ONE term arg (the internal
    // pivot). carcara wants (pivot, polarity).
    {
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(a_or_b)); // 0
        p.add_step(ProofStep::Assume(na_or_c)); // 1
        p.add_step(ProofStep::Assume(nb)); // 2
        p.add_step(ProofStep::Assume(nc)); // 3
        p.add_step(ProofStep::Step {
            rule: AletheRule::Or,
            clause: vec![a, b],
            premises: vec![ProofId(0)],
            args: vec![],
        }); // 4
        p.add_step(ProofStep::Step {
            rule: AletheRule::Or,
            clause: vec![na, c],
            premises: vec![ProofId(1)],
            args: vec![],
        }); // 5
        p.add_step(ProofStep::Step {
            rule: AletheRule::Resolution,
            clause: vec![a],
            premises: vec![ProofId(4), ProofId(2)],
            args: vec![b],
        }); // 6
        p.add_step(ProofStep::Step {
            rule: AletheRule::Resolution,
            clause: vec![c],
            premises: vec![ProofId(6), ProofId(5)],
            args: vec![a],
        }); // 7
        p.add_step(ProofStep::Step {
            rule: AletheRule::Resolution,
            clause: vec![],
            premises: vec![ProofId(7), ProofId(3)],
            args: vec![c],
        }); // 8
        verdicts(
            "A3 binary_onearg",
            "carcara: expected 2 arguments, got 1 -> INVALID",
            &p,
            &t,
        );
    }

    // A5: an n-ary chain whose DECLARED args name pivots in the wrong order.
    // AY ignores them and re-infers; carcara follows them and fails.
    {
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(a_or_b));
        p.add_step(ProofStep::Assume(na_or_c));
        p.add_step(ProofStep::Assume(nb));
        p.add_step(ProofStep::Assume(nc));
        p.add_step(ProofStep::Step {
            rule: AletheRule::Or,
            clause: vec![a, b],
            premises: vec![ProofId(0)],
            args: vec![],
        });
        p.add_step(ProofStep::Step {
            rule: AletheRule::Or,
            clause: vec![na, c],
            premises: vec![ProofId(1)],
            args: vec![],
        });
        p.add_step(ProofStep::Step {
            rule: AletheRule::Resolution,
            clause: vec![],
            premises: vec![ProofId(4), ProofId(2), ProofId(5), ProofId(3)],
            // "c true a true b true": wrong pivot on the first link.
            args: vec![c, a, b],
        });
        verdicts(
            "A5 nary_wrong_pivots",
            "carcara: pivot was not found in clause: 'c' -> INVALID",
            &p,
            &t,
        );
    }

    // ============================================================== PROBE B
    // De Morgan complement matching: AY pairs `(and a b)` with
    // `(or (not a) (not b))` as complementary resolution literals.
    {
        let mut t2 = TermStore::new();
        let a = t2.mk_var("a", Sort::Bool);
        let b = t2.mk_var("b", Sort::Bool);
        let na = t2.mk_not(a);
        let nb = t2.mk_not(b);
        let and_ab = t2.mk_app(Symbol::Named("and".into()), [a, b], Sort::Bool);
        let or_nanb = t2.mk_app(Symbol::Named("or".into()), [na, nb], Sort::Bool);

        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(and_ab)); // 0
        p.add_step(ProofStep::Assume(or_nanb)); // 1
        p.add_step(ProofStep::Step {
            rule: AletheRule::Resolution,
            clause: vec![],
            premises: vec![ProofId(0), ProofId(1)],
            args: vec![],
        }); // 2
        verdicts(
            "B1 demorgan_binary",
            "carcara: pivot was not eliminated: '(and a b)' -> INVALID",
            &p,
            &t2,
        );

        // Same, but through the n-ary chain path (3 premises).
        let mut p3 = Proof::new();
        p3.add_step(ProofStep::Assume(and_ab));
        p3.add_step(ProofStep::Assume(or_nanb));
        p3.add_step(ProofStep::Assume(or_nanb));
        p3.add_step(ProofStep::Step {
            rule: AletheRule::Resolution,
            clause: vec![],
            premises: vec![ProofId(0), ProofId(1), ProofId(2)],
            args: vec![],
        });
        verdicts(
            "B2 demorgan_nary",
            "carcara: pivot was not eliminated -> INVALID",
            &p3,
            &t2,
        );

        // B3 CONTROL: permuted De Morgan -- (and a b) vs (or (not b) (not a)).
        let or_nbna = t2.mk_app(Symbol::Named("or".into()), [nb, na], Sort::Bool);
        let mut p4 = Proof::new();
        p4.add_step(ProofStep::Assume(and_ab));
        p4.add_step(ProofStep::Assume(or_nbna));
        p4.add_step(ProofStep::Step {
            rule: AletheRule::Resolution,
            clause: vec![],
            premises: vec![ProofId(0), ProofId(1)],
            args: vec![],
        });
        verdicts(
            "B3 demorgan_permuted",
            "greedy multiset match; sound but carcara-INVALID",
            &p4,
            &t2,
        );
    }

    // ============================================================== PROBE C
    // Absorption: carcara silently absorbs premises once the accumulator is
    // empty; AY's chain path is documented as REJECTING that. Verify AY's
    // direction (this is the incompleteness cell, not the dangerous one).
    {
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(a)); // 0
        p.add_step(ProofStep::Assume(na)); // 1
        p.add_step(ProofStep::Assume(b)); // 2
        p.add_step(ProofStep::Step {
            rule: AletheRule::Resolution,
            clause: vec![],
            premises: vec![ProofId(1), ProofId(0), ProofId(2)],
            args: vec![],
        }); // 3
        verdicts(
            "C1 absorb_after_empty",
            "carcara ACCEPTS this; AY documented to reject",
            &p,
            &t,
        );
    }

    // ============================================================== PROBE D
    // Does AY's checker care about the `:args` count on a rule where carcara
    // demands a specific arity? `and_pos` index arg.
    {
        let mut t3 = TermStore::new();
        let a = t3.mk_var("a", Sort::Bool);
        let b = t3.mk_var("b", Sort::Bool);
        let and_ab = t3.mk_app(Symbol::Named("and".into()), [a, b], Sort::Bool);
        let n_and = t3.mk_not(and_ab);
        let na = t3.mk_not(a);

        // and_pos with index 0 concluding (cl (not (and a b)) a) -- correct.
        let mut p = Proof::new();
        p.add_step(ProofStep::Step {
            rule: AletheRule::AndPos(0),
            clause: vec![n_and, a],
            premises: vec![],
            args: vec![and_ab],
        }); // 0
        p.add_step(ProofStep::Assume(and_ab)); // 1
        p.add_step(ProofStep::Assume(na)); // 2
        p.add_step(ProofStep::Step {
            rule: AletheRule::Resolution,
            clause: vec![],
            premises: vec![ProofId(0), ProofId(1), ProofId(2)],
            args: vec![],
        }); // 3
        verdicts("D1 and_pos_ok", "control: should be carcara-valid", &p, &t3);
    }
    probe_e();
}

// ============================================================== PROBE E
// Appended by the differential-testing phase: the LIVE divergences found on
// the real corpus. Each is paired with an Alethe text twin fed to carcara.
#[allow(dead_code)]
fn probe_e() {
    use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, Symbol, TermStore};
    let mut t = TermStore::new();
    let a = t.mk_var("a", Sort::Bool);
    let b = t.mk_var("b", Sort::Bool);
    let na = t.mk_not(a);
    let nb = t.mk_not(b);
    let a_or_b = t.mk_app(Symbol::Named("or".into()), [a, b], Sort::Bool);

    // E1: `or` clausification with the conclusion literals PERMUTED relative
    // to the premise disjunct order. AY: clause_matches_unordered -> accept.
    // carcara: `or` is order-sensitive -> invalid.
    {
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(a_or_b)); // 0 h0
        p.add_step(ProofStep::Assume(na)); // 1 h1
        p.add_step(ProofStep::Assume(nb)); // 2 h2
        p.add_step(ProofStep::Step {
            rule: AletheRule::Or,
            clause: vec![b, a], // PERMUTED: premise is (or a b)
            premises: vec![ProofId(0)],
            args: vec![],
        }); // 3 t3
        p.add_step(ProofStep::Step {
            rule: AletheRule::Resolution,
            clause: vec![],
            premises: vec![ProofId(3), ProofId(1), ProofId(2)],
            args: vec![],
        }); // 4 t4
        verdicts(
            "E1 or_permuted",
            "carcara: 'or' order-sensitive -> INVALID",
            &p,
            &t,
        );
    }

    // E0 CONTROL: same proof, in-order.
    {
        let mut p = Proof::new();
        p.add_step(ProofStep::Assume(a_or_b));
        p.add_step(ProofStep::Assume(na));
        p.add_step(ProofStep::Assume(nb));
        p.add_step(ProofStep::Step {
            rule: AletheRule::Or,
            clause: vec![a, b],
            premises: vec![ProofId(0)],
            args: vec![],
        });
        p.add_step(ProofStep::Step {
            rule: AletheRule::Resolution,
            clause: vec![],
            premises: vec![ProofId(3), ProofId(1), ProofId(2)],
            args: vec![],
        });
        verdicts("E0 or_inorder", "control: carcara VALID", &p, &t);
    }
}
