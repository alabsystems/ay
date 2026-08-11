// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
//! Differential-test harness support: solve one .smt2, record AY's INTERNAL
//! proof-checker verdicts on the in-memory proof, and write the SAME proof out
//! as Alethe text for an external checker (carcara).
//!
//! Both verdicts come from ONE proof object in ONE process, so the internal and
//! external checkers see the identical derivation — no re-solve, no drift.
//!
//!   cargo run -p ay-dpll --example proof_diff --release -- FILE.smt2 OUT.alethe [TIMEOUT_MS]
//!
//! Prints one JSON object on stdout.

use std::io::Write;

const MARKER: &str = "AY_PROOF_DIFF_HARNESS_v1";

fn jesc(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 8);
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

fn main() {
    let _ = MARKER;
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: proof_diff <file.smt2> <out.alethe> [timeout_ms]");
        std::process::exit(2);
    }
    let path = &args[1];
    let out_path = &args[2];
    let timeout_ms: u64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(20_000);

    let input = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            println!(
                "{{\"status\":\"read_error\",\"detail\":\"{}\"}}",
                jesc(&e.to_string())
            );
            return;
        }
    };
    let commands = match ay_frontend::parse(&input) {
        Ok(c) => c,
        Err(e) => {
            println!(
                "{{\"status\":\"parse_error\",\"detail\":\"{}\"}}",
                jesc(&format!("{e:?}"))
            );
            return;
        }
    };

    let mut exec = ay_dpll::Executor::new();
    exec.set_produce_proofs(true);
    // Mirror the CLI's timeout wiring exactly (crates/ay/src/run.rs::new_executor):
    // relative timeout + cooperative wall-clock deadline + interrupt watchdog.
    exec.set_timeout(Some(std::time::Duration::from_millis(timeout_ms)));
    let start = std::time::Instant::now();
    if let Some(deadline) = start.checked_add(std::time::Duration::from_millis(timeout_ms)) {
        exec.set_deadline(Some(deadline));
    }
    let interrupt = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    exec.set_interrupt(interrupt.clone());
    {
        let flag = interrupt.clone();
        std::thread::spawn(move || {
            std::thread::sleep(std::time::Duration::from_millis(timeout_ms));
            flag.store(true, std::sync::atomic::Ordering::SeqCst);
        });
    }

    let mut verdict = String::from("none");
    for cmd in &commands {
        match exec.execute(cmd) {
            Ok(Some(o)) => {
                if matches!(o.as_str(), "sat" | "unsat" | "unknown") {
                    verdict = o;
                }
            }
            Ok(None) => {}
            Err(e) => {
                println!(
                    "{{\"status\":\"exec_error\",\"detail\":\"{}\"}}",
                    jesc(&format!("{e:?}"))
                );
                return;
            }
        }
    }

    if verdict != "unsat" {
        println!(
            "{{\"status\":\"not_unsat\",\"verdict\":\"{}\"}}",
            jesc(&verdict)
        );
        return;
    }

    let Some(proof) = exec.last_proof() else {
        println!("{{\"status\":\"no_proof\",\"verdict\":\"unsat\"}}");
        return;
    };
    let terms = exec.terms();

    // AY's INTERNAL checkers, on the in-memory proof.
    let nonstrict = ay_proof::check_proof(proof, terms);
    let strict = ay_proof::check_proof_strict(proof, terms);
    let (quality, _q_err) = {
        match ay_proof::check_proof_with_quality(proof, terms) {
            Ok(q) => (Some(q), None),
            Err(e) => (None, Some(format!("{e}"))),
        }
    };
    let (partial, partial_err) = ay_proof::check_proof_partial(proof, terms);

    let nonstrict_s = match &nonstrict {
        Ok(()) => "accept".to_string(),
        Err(e) => format!("reject: {e}"),
    };
    let strict_s = match &strict {
        Ok(_) => "accept".to_string(),
        Err(e) => format!("reject: {e}"),
    };
    let partial_s = match &partial_err {
        None => "accept".to_string(),
        Some(e) => format!("reject: {e}"),
    };

    // Same proof, rendered to Alethe for carcara.
    let mut buf: Vec<u8> = Vec::new();
    let render = exec.try_export_last_proof_alethe_for_problem_scope_to(&mut buf);
    let render_s = match render {
        Some(Ok(())) => "ok".to_string(),
        Some(Err(e)) => format!("error: {e}"),
        None => "none".to_string(),
    };
    let wrote = if matches!(render_s.as_str(), "ok") {
        match std::fs::File::create(out_path).and_then(|mut f| f.write_all(&buf)) {
            Ok(()) => true,
            Err(_) => false,
        }
    } else {
        false
    };

    let (t, h, tot, thl, other) = quality
        .as_ref()
        .map(|q| {
            (
                q.trust_count,
                q.hole_count,
                q.total_steps,
                q.theory_lemma_count,
                q.other_rule_count,
            )
        })
        .unwrap_or((0, 0, 0, 0, 0));

    // Printed-document facts (what carcara actually sees).
    let text = String::from_utf8_lossy(&buf);
    let printed_holes = text.matches(":rule hole").count();
    let printed_trust = text.matches(":rule trust").count();
    let printed_resolution_args = text.matches(":rule resolution").count();

    // Step-shape histogram of the IR (what AY's checker actually sees).
    let mut ir: std::collections::BTreeMap<String, u32> = std::collections::BTreeMap::new();
    for step in &proof.steps {
        let key = match step {
            ay_core::ProofStep::Assume(_) => "Assume".to_string(),
            ay_core::ProofStep::Resolution { .. } => "Resolution(binary)".to_string(),
            ay_core::ProofStep::TheoryLemma { kind, .. } => format!("TheoryLemma:{kind:?}"),
            ay_core::ProofStep::Step { rule, premises, .. } => {
                format!("Step:{}:np{}", rule.name(), premises.len().min(9))
            }
            ay_core::ProofStep::Anchor { .. } => "Anchor".to_string(),
            _ => "Other".to_string(),
        };
        *ir.entry(key).or_default() += 1;
    }
    let ir_str = ir
        .iter()
        .map(|(k, v)| format!("\"{}\":{}", jesc(k), v))
        .collect::<Vec<_>>()
        .join(",");

    println!(
        "{{\"status\":\"ok\",\"verdict\":\"unsat\",\"ay_nonstrict\":\"{}\",\"ay_strict\":\"{}\",\"ay_partial\":\"{}\",\"render\":\"{}\",\"wrote\":{},\"trust\":{},\"hole\":{},\"theory_lemma\":{},\"other_rule\":{},\"steps\":{},\"partial_checked\":{},\"partial_total\":{},\"printed_holes\":{},\"printed_trust\":{},\"printed_resolutions\":{},\"bytes\":{},\"ir\":{{{}}}}}",
        jesc(&nonstrict_s),
        jesc(&strict_s),
        jesc(&partial_s),
        jesc(&render_s),
        wrote,
        t,
        h,
        thl,
        other,
        tot,
        partial.checked_steps,
        partial.total_steps,
        printed_holes,
        printed_trust,
        printed_resolution_args,
        buf.len(),
        ir_str,
    );
}
