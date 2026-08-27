// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// VeriPB v3 EMITTER CONFORMANCE, checked by the OFFICIAL checker.
//
// These tests pin two conformance classes that unit tests over the emitted
// text cannot catch on their own, because both failures live in the checker,
// not in the string:
//
//   1. OPERAND KIND. `pol <id> <var> w` takes a bare VARIABLE. VeriPB 3.0.2
//      hard-REJECTS a literal operand (`~x2 w`) with a parse error, which
//      voids the whole proof file. `ProofStep::Weaken` therefore emits the
//      variable regardless of the stored literal's polarity.
//
//   2. ID ALLOCATION. A step allocates a constraint ID iff its rule is a v3
//      `output_rule` / `top_output_rule`. Any over-allocation (the classic
//      example being `obju`, a bare `top_rule` that allocates NOTHING) shifts
//      every later reference by one; each test therefore also runs a
//      deliberately shifted twin and asserts the checker REJECTS it, so a
//      regression cannot hide behind a checker that ignores stale ids.
//
// Gated on the checker being present (VERIPB_BIN env, `veripb` on PATH, or the
// cert_ci.sh cache path); without it the run degrades to text-shape checks.

use std::path::{Path, PathBuf};
use std::process::Command;

use ay_pb::proof::{ConstraintId, ProofStep, VeriPbWriter};
use ay_pb::PbLit;

fn veripb_bin() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("VERIPB_BIN") {
        let p = PathBuf::from(p);
        if p.exists() {
            return Some(p);
        }
    }
    if let Ok(out) = Command::new("which").arg("veripb").output() {
        if out.status.success() {
            let path = String::from_utf8_lossy(&out.stdout).trim().to_string();
            if !path.is_empty() {
                return Some(PathBuf::from(path));
            }
        }
    }
    let cache = std::env::var_os("XDG_CACHE_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".cache")))?;
    let default = cache.join("ay-veripb/VeriPB/target/release/veripb");
    default.exists().then_some(default)
}

/// Runs the official checker and returns its `s <VERDICT>` line, or a
/// `REJECTED: ...` marker carrying the checker's own diagnosis.
fn veripb_verdict(veripb: &Path, opb: &str, pbp: &str, label: &str) -> String {
    let dir = std::env::temp_dir().join(format!(
        "ay_emitter_conformance_{label}_{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let opb_path = dir.join("instance.opb");
    let pbp_path = dir.join("proof.pbp");
    std::fs::write(&opb_path, opb).expect("write opb");
    std::fs::write(&pbp_path, pbp).expect("write pbp");

    let output = Command::new(veripb)
        .arg(&opb_path)
        .arg(&pbp_path)
        .output()
        .expect("run veripb");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let _ = std::fs::remove_dir_all(&dir);

    stdout
        .lines()
        .find(|l| l.starts_with("s "))
        .map(str::to_string)
        .unwrap_or_else(|| format!("REJECTED: {}", stderr.replace('\n', " ").trim()))
}

fn lit(var: u32, negated: bool) -> PbLit {
    PbLit { var, negated }
}

fn cid(value: u64) -> ConstraintId {
    ConstraintId::new(value).expect("proof IDs are 1-indexed")
}

/// Shifts every `pol` operand and the UNSAT conclusion id up by one, modelling
/// exactly what an over-allocating step (e.g. an `obju` arm that wrongly calls
/// `allocate_constraint_id`) does to the rest of the proof.
fn shift_ids_by_one(pbp: &str) -> String {
    pbp.lines()
        .map(|line| {
            if let Some(rest) = line.strip_prefix("pol ") {
                let bumped: Vec<String> = rest
                    .split(' ')
                    .map(|tok| match tok.parse::<u64>() {
                        Ok(n) => (n + 1).to_string(),
                        Err(_) => tok.to_string(),
                    })
                    .collect();
                format!("pol {}", bumped.join(" "))
            } else if let Some(rest) = line.strip_prefix("conclusion UNSAT : ") {
                let id: u64 = rest
                    .trim_end_matches(';')
                    .parse()
                    .expect("conclusion carries a numeric id");
                format!("conclusion UNSAT : {};", id + 1)
            } else {
                line.to_string()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
        + "\n"
}

/// `+1 x1 +1 x2 >= 2` with `+1 ~x1 >= 1` is UNSAT. Weakening `x2` away from
/// row 1 leaves `+1 x1 >= 1`; adding row 2 cancels the complementary pair and
/// leaves the empty `>= 1` contradiction.
const WEAKEN_OPB: &str = "* #variable= 2 #constraint= 2\n+1 x1 +1 x2 >= 2 ;\n+1 ~x1 >= 1 ;\n";

fn build_weaken_proof(weakened: PbLit) -> String {
    let mut writer = VeriPbWriter::new(Vec::<u8>::new(), 2).expect("header writes to a Vec");
    let weakened_row = writer
        .log_step(ProofStep::Weaken(cid(1), weakened))
        .expect("weaken is logged");
    let contradiction = writer
        .log_step(ProofStep::Addition(weakened_row, cid(2)))
        .expect("addition is logged");
    writer
        .conclude_unsat(contradiction)
        .expect("contradiction concludes the refutation");
    String::from_utf8(writer.into_inner()).expect("proof output is valid UTF-8")
}

#[test]
fn test_weaken_operand_is_a_variable_and_the_official_checker_accepts_it() {
    // The polarity stored in the step must NOT reach the proof text.
    let positive = build_weaken_proof(lit(2, false));
    let negated = build_weaken_proof(lit(2, true));
    assert_eq!(
        positive, negated,
        "weaken must render identically for both polarities of the same variable",
    );
    assert!(
        positive.contains("pol 1 x2 w ;"),
        "weaken must emit a bare variable operand:\n{positive}"
    );
    assert!(
        !positive.contains("~x2 w"),
        "a negated weaken operand is a VeriPB parse error:\n{positive}"
    );
    // Weaken is an output rule: it allocated id 3, so the addition references
    // 3 (not 2, and not 4).
    assert!(
        positive.contains("pol 3 2 + ;") && positive.contains("conclusion UNSAT : 4;"),
        "weaken must allocate exactly one id:\n{positive}"
    );

    let Some(veripb) = veripb_bin() else {
        eprintln!("VeriPB checker not present; text-shape checks only");
        return;
    };

    let verdict = veripb_verdict(&veripb, WEAKEN_OPB, &positive, "weaken_ok");
    assert_eq!(
        verdict, "s VERIFIED UNSATISFIABLE",
        "official checker rejected the emitted weaken proof:\n{positive}"
    );

    // The historical defect, spelled out, must still be a hard parse error —
    // this is what makes the assertion above load-bearing rather than
    // cosmetic.
    let defective = positive.replace("pol 1 x2 w ;", "pol 1 ~x2 w ;");
    let defective_verdict = veripb_verdict(&veripb, WEAKEN_OPB, &defective, "weaken_lit");
    assert!(
        defective_verdict.starts_with("REJECTED"),
        "a literal weaken operand must be rejected, got: {defective_verdict}"
    );

    // Over-allocation regression twin.
    let shifted = shift_ids_by_one(&positive);
    let shifted_verdict = veripb_verdict(&veripb, WEAKEN_OPB, &shifted, "weaken_shift");
    assert!(
        shifted_verdict.starts_with("REJECTED"),
        "an id shifted by one must be rejected, got: {shifted_verdict}"
    );
}

/// `+1 x1 >= 1` and `+1 ~x1 >= 1` is UNSAT. The chain exercises every
/// id-allocating `pol`/`rup` arm plus `del` (which must allocate NOTHING).
const CHAIN_OPB: &str = "* #variable= 2 #constraint= 2\n+1 x1 >= 1 ;\n+1 ~x1 >= 1 ;\n";

#[test]
fn test_pol_chain_ids_line_up_with_the_official_checker_database() {
    let mut writer = VeriPbWriter::new(Vec::<u8>::new(), 2).expect("header writes to a Vec");
    let sum = writer
        .log_step(ProofStep::Addition(cid(1), cid(2)))
        .expect("addition is logged");
    let doubled = writer
        .log_step(ProofStep::Multiply(sum, 2))
        .expect("multiply is logged");
    let halved = writer
        .log_step(ProofStep::Divide(doubled, 2))
        .expect("divide is logged");
    let saturated = writer
        .log_step(ProofStep::Saturate(halved))
        .expect("saturate is logged");
    // `del` is a top_rule: it must not consume an id, so the RUP below still
    // lands on `saturated + 1`.
    let deleted = writer
        .log_step(ProofStep::Delete(doubled))
        .expect("deletion is logged");
    assert_eq!(deleted, doubled, "delete echoes the id it removed");
    let contradiction = writer
        .log_step(ProofStep::Rup(String::from(">= 1 ;")))
        .expect("rup is logged");
    assert_eq!(
        contradiction.get(),
        saturated.get() + 1,
        "delete must not consume a constraint id",
    );
    writer
        .conclude_unsat(contradiction)
        .expect("contradiction concludes the refutation");
    let pbp = String::from_utf8(writer.into_inner()).expect("proof output is valid UTF-8");

    let Some(veripb) = veripb_bin() else {
        eprintln!("VeriPB checker not present; text-shape checks only");
        return;
    };

    let verdict = veripb_verdict(&veripb, CHAIN_OPB, &pbp, "chain_ok");
    assert_eq!(
        verdict, "s VERIFIED UNSATISFIABLE",
        "official checker rejected the emitted pol chain:\n{pbp}"
    );

    let shifted = shift_ids_by_one(&pbp);
    let shifted_verdict = veripb_verdict(&veripb, CHAIN_OPB, &shifted, "chain_shift");
    assert!(
        shifted_verdict.starts_with("REJECTED"),
        "an id shifted by one must be rejected, got: {shifted_verdict}"
    );
}

/// `soli` is a `top_output_rule`: it logs the solution AND adds exactly ONE
/// objective-improving constraint. Its id must be usable immediately.
const SOLI_OPB: &str = "* #variable= 2 #constraint= 1\nmin: +1 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n";

#[test]
fn test_soli_allocates_exactly_one_id_against_the_official_checker() {
    let mut writer = VeriPbWriter::new(Vec::<u8>::new(), 1).expect("header writes to a Vec");
    let improving = writer
        .log_step(ProofStep::SolutionImproving(String::from("x1 x2")))
        .expect("soli is logged");
    assert_eq!(improving.get(), 2, "soli allocates exactly one id");
    // Referencing the soli id is what proves the allocation count: an
    // over-allocation makes this an out-of-bounds database access.
    writer
        .log_step(ProofStep::Saturate(improving))
        .expect("saturating the objective-improving row is logged");
    writer
        .set_opt_bounds(0, 2)
        .expect("0 <= obj <= 2 is a valid interval");
    writer
        .conclude_opt_hinted(None, Some("x1 x2"))
        .expect("hinted OPT conclusion is written");
    let pbp = String::from_utf8(writer.into_inner()).expect("proof output is valid UTF-8");
    assert!(pbp.contains("soli x1 x2;\npol 2 s ;"), "{pbp}");

    let Some(veripb) = veripb_bin() else {
        eprintln!("VeriPB checker not present; text-shape checks only");
        return;
    };

    let verdict = veripb_verdict(&veripb, SOLI_OPB, &pbp, "soli_ok");
    assert_eq!(
        verdict, "s VERIFIED BOUNDS 0 <= obj <= 2",
        "official checker rejected the emitted soli proof:\n{pbp}"
    );

    let shifted = pbp.replace("pol 2 s ;", "pol 3 s ;");
    let shifted_verdict = veripb_verdict(&veripb, SOLI_OPB, &shifted, "soli_shift");
    assert!(
        shifted_verdict.starts_with("REJECTED"),
        "soli over-allocation must be rejected, got: {shifted_verdict}"
    );
}

/// `conclusion SAT` is DECISION-only: VeriPB rejects it against an OPB that
/// declares an objective. The solution-only route must therefore withhold the
/// certificate on optimization instances instead of shipping a rejected proof.
#[test]
fn test_solution_only_sat_proof_withholds_on_objective_instances() {
    let decision =
        ay_pb::parse_opb("* #variable= 2 #constraint= 1\n+1 x1 +1 x2 >= 1 ;\n").expect("parse");
    let with_objective = ay_pb::parse_opb(SOLI_OPB).expect("parse");

    let decision_proof = ay_pb::proof::solution_only_sat_proof(&decision, &[true, true])
        .expect("decision instances get a solution-only certificate");
    assert!(
        decision_proof.contains("conclusion SAT : x1 x2;"),
        "{decision_proof}"
    );
    assert!(
        ay_pb::proof::solution_only_sat_proof(&with_objective, &[true, true]).is_none(),
        "an objective instance must NOT get a `conclusion SAT` certificate",
    );

    let Some(veripb) = veripb_bin() else {
        eprintln!("VeriPB checker not present; text-shape checks only");
        return;
    };

    let decision_opb = "* #variable= 2 #constraint= 1\n+1 x1 +1 x2 >= 1 ;\n";
    assert_eq!(
        veripb_verdict(&veripb, decision_opb, &decision_proof, "sat_decision"),
        "s VERIFIED SATISFIABLE",
        "the decision certificate must verify:\n{decision_proof}"
    );
    // The same text against the objective instance is what the guard prevents.
    let verdict = veripb_verdict(&veripb, SOLI_OPB, &decision_proof, "sat_objective");
    assert!(
        verdict.starts_with("REJECTED"),
        "`conclusion SAT` on an objective instance must be rejected, got: {verdict}"
    );
}
