// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeMap as HashMap;
use std::io::{self, Write};

use super::{format_constraint, format_cp_constraint, format_lit, ProofError, VeriPbWriter};
use crate::{
    proof::{ConstraintId, ProofStep},
    CpConstraint, PbLit,
};

fn lit(var: u32) -> PbLit {
    PbLit {
        var,
        negated: false,
    }
}

fn neg(var: u32) -> PbLit {
    PbLit { var, negated: true }
}

fn cp(entries: &[(PbLit, i128)], degree: i128) -> CpConstraint {
    let coeffs = entries.iter().copied().collect::<HashMap<_, _>>();
    CpConstraint::new(coeffs, degree)
}

#[derive(Default)]
struct FailingWriter {
    fail_on_write: bool,
    fail_on_flush: bool,
    sink: Vec<u8>,
}

impl Write for FailingWriter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if self.fail_on_write {
            Err(io::Error::other("injected write failure"))
        } else {
            self.sink.extend_from_slice(buf);
            Ok(buf.len())
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        if self.fail_on_flush {
            Err(io::Error::other("injected flush failure"))
        } else {
            Ok(())
        }
    }
}

#[test]
fn test_format_lit_uses_opb_literal_syntax() {
    assert_eq!(format_lit(lit(1)), "x1");
    assert_eq!(format_lit(neg(4)), "~x4");
}

#[test]
fn test_format_constraint_renders_signed_terms_and_semicolon() {
    let formatted = format_constraint(&[(lit(1), 3), (neg(2), -2)], 5);

    assert_eq!(formatted, "+3 x1 -2 ~x2 >= 5 ;");
}

#[test]
fn test_format_constraint_handles_empty_or_zero_lhs() {
    assert_eq!(format_constraint(&[], 7), ">= 7 ;");
    assert_eq!(format_constraint(&[(lit(1), 0)], 2), ">= 2 ;");
}

#[test]
fn test_format_cp_constraint_sorts_hash_map_entries() {
    let constraint = cp(&[(neg(2), 2), (lit(1), 3)], 4);

    assert_eq!(format_cp_constraint(&constraint), "+3 x1 +2 ~x2 >= 4");
}

#[test]
fn test_new_writes_header_and_log_step_allocates_next_id() {
    let mut writer =
        VeriPbWriter::new(Vec::new(), 2).expect("header writes to an in-memory buffer");

    let derived = writer
        .log_step(ProofStep::Addition(
            ConstraintId::new(1).expect("proof IDs are 1-indexed"),
            ConstraintId::new(2).expect("proof IDs are 1-indexed"),
        ))
        .expect("addition allocates a derived ID");

    assert_eq!(derived.get(), 3);
    assert_eq!(
        String::from_utf8(writer.writer).expect("proof output is valid UTF-8"),
        "pseudo-Boolean proof version 3.0\nf 2 ;\npol 1 2 + ;\n",
    );
}

#[test]
fn test_delete_does_not_consume_constraint_ids() {
    let mut writer =
        VeriPbWriter::new(Vec::new(), 1).expect("header writes to an in-memory buffer");

    let deleted = writer
        .log_step(ProofStep::Delete(
            ConstraintId::new(1).expect("proof IDs are 1-indexed"),
        ))
        .expect("deletion is logged");
    let derived = writer
        .log_step(ProofStep::Rup(String::from("+1 x1 >= 1 ;")))
        .expect("RUP allocates the next derived ID");

    assert_eq!(deleted.get(), 1);
    assert_eq!(derived.get(), 2);
    assert_eq!(
        String::from_utf8(writer.writer).expect("proof output is valid UTF-8"),
        "pseudo-Boolean proof version 3.0\nf 1 ;\ndel id 1 ;\nrup +1 x1 >= 1 ;\n",
    );
}

#[test]
fn test_solution_improving_advances_derived_id_sequence() {
    let mut writer =
        VeriPbWriter::new(Vec::new(), 0).expect("header writes to an in-memory buffer");

    let soli_id = writer
        .log_step(ProofStep::SolutionImproving(String::from("x1 ~x2")))
        .expect("solution-improving rule consumes a proof-line ID");
    let rup_id = writer
        .log_step(ProofStep::Rup(String::from("+1 x2 >= 1 ;")))
        .expect("RUP allocates the next derived ID");

    assert_eq!(soli_id.get(), 1);
    assert_eq!(rup_id.get(), 2);
    assert_eq!(
        String::from_utf8(writer.writer).expect("proof output is valid UTF-8"),
        "pseudo-Boolean proof version 3.0\nf 0 ;\nsoli x1 ~x2;\nrup +1 x2 >= 1 ;\n",
    );
}

#[test]
fn test_polynomial_expression_allocates_derived_id() {
    let mut writer =
        VeriPbWriter::new(Vec::new(), 2).expect("header writes to an in-memory buffer");

    let derived = writer
        .log_step(ProofStep::Polynomial(String::from(
            "1 3 * ~x1 + x3 2 * + ;",
        )))
        .expect("polynomial expression allocates a derived ID");

    assert_eq!(derived.get(), 3);
    assert_eq!(
        String::from_utf8(writer.writer).expect("proof output is valid UTF-8"),
        "pseudo-Boolean proof version 3.0\nf 2 ;\npol 1 3 * ~x1 + x3 2 * + ;\n",
    );
}

#[test]
fn test_red_writes_veripb_v3_colon_witness_form() {
    let mut writer =
        VeriPbWriter::new(Vec::new(), 1).expect("header writes to an in-memory buffer");

    let derived = writer
        .log_step(ProofStep::Red(
            String::from("+1 x1 >= 1"),
            String::from("x1 -> 1 ;"),
        ))
        .expect("RED allocates a derived ID");

    assert_eq!(derived.get(), 2);
    assert_eq!(
        String::from_utf8(writer.writer).expect("proof output is valid UTF-8"),
        "pseudo-Boolean proof version 3.0\nf 1 ;\nred +1 x1 >= 1: x1 -> 1 ;\n",
    );
}

#[test]
fn test_weaken_emits_a_bare_variable_for_both_polarities() {
    // VeriPB v3 `pol_constraint ::= ... | pol_constraint, skip,
    // (variable | aux_variable), skip, "w"` (the development design notes:1076): the
    // weaken operand is a VARIABLE, never a literal. Emitting `~x2 w` is a
    // hard PARSE error in VeriPB 3.0.2 ("...but found `w` (there are 2
    // elements on the stack)"), which voids the whole proof file, so the
    // negated literal must render exactly like the positive one.
    for lit in [lit(2), neg(2)] {
        let mut writer =
            VeriPbWriter::new(Vec::new(), 1).expect("header writes to an in-memory buffer");

        let derived = writer
            .log_step(ProofStep::Weaken(
                ConstraintId::new(1).expect("proof IDs are 1-indexed"),
                lit,
            ))
            .expect("weakening allocates a derived ID");

        assert_eq!(derived.get(), 2, "weaken is an output rule: it allocates 1");
        let text = String::from_utf8(writer.writer).expect("proof output is valid UTF-8");
        assert_eq!(
            text, "pseudo-Boolean proof version 3.0\nf 1 ;\npol 1 x2 w ;\n",
            "weaken operand must be the bare variable, got: {text}"
        );
        assert!(
            !text.contains('~'),
            "a negated weaken operand is a VeriPB parse error: {text}"
        );
    }
}

/// VeriPB's ID-allocation contract, restated independently of the writer: a
/// step allocates a constraint ID **iff** its rule is an `output_rule` /
/// `top_output_rule` in the v3 grammar (the development design notes:1014-1046).
///
/// The match is deliberately EXHAUSTIVE. Adding a `ProofStep` variant must
/// not compile until its allocation behaviour is decided here — in
/// particular `obju`, which is a bare `top_rule` (grammar.tex:1003) and
/// allocates NOTHING; treating it as allocating shifts every later ID by
/// one and the checker then reports either "Accessing the database out of
/// bound" or, worse, silently uses the wrong constraint.
fn rule_allocates_constraint_id(step: &ProofStep) -> bool {
    match step {
        // `output_rule`: pol / rup / red all add a constraint.
        ProofStep::Addition(..)
        | ProofStep::Multiply(..)
        | ProofStep::Divide(..)
        | ProofStep::Saturate(..)
        | ProofStep::Polynomial(..)
        | ProofStep::Weaken(..)
        | ProofStep::Rup(..)
        | ProofStep::Red(..) => true,
        // `top_output_rule`: soli logs the solution AND adds exactly one
        // objective-improving constraint (verified against VeriPB 3.0.2).
        ProofStep::SolutionImproving(..) => true,
        // `top_rule`, not an output rule: deletion adds nothing.
        ProofStep::Delete(..) => false,
    }
}

#[test]
fn test_every_step_matches_the_veripb_id_allocation_contract() {
    let id = ConstraintId::new(1).expect("proof IDs are 1-indexed");
    let steps = [
        ProofStep::Addition(id, id),
        ProofStep::Multiply(id, 3),
        ProofStep::Divide(id, 2),
        ProofStep::Saturate(id),
        ProofStep::Polynomial(String::from("1 ;")),
        ProofStep::Weaken(id, neg(1)),
        ProofStep::Rup(String::from("+1 x1 >= 1 ;")),
        ProofStep::Red(String::from("+1 x1 >= 1"), String::from("x1 -> 1 ;")),
        ProofStep::Delete(id),
        ProofStep::SolutionImproving(String::from("x1")),
    ];

    for step in steps {
        let mut writer =
            VeriPbWriter::new(Vec::new(), 1).expect("header writes to an in-memory buffer");
        let before = writer
            .allocated_constraint_count()
            .expect("id space is not exhausted");

        let expected_allocation = rule_allocates_constraint_id(&step);
        let returned = writer.log_step(step.clone()).expect("step is logged");

        let after = writer
            .allocated_constraint_count()
            .expect("id space is not exhausted");
        let allocated = after - before;

        assert_eq!(
            allocated,
            u64::from(expected_allocation),
            "{step:?} allocated {allocated} ids, contract says {expected_allocation}",
        );
        if expected_allocation {
            assert_eq!(returned.get(), after, "{step:?} must return the new id");
        } else {
            assert_eq!(
                returned.get(),
                1,
                "{step:?} must echo the referenced id, not a fresh one",
            );
        }
    }
}

#[test]
fn test_conclude_unsat_writes_veripb_v3_footer() {
    let mut writer =
        VeriPbWriter::new(Vec::new(), 3).expect("header writes to an in-memory buffer");

    writer
        .conclude_unsat(ConstraintId::new(2).expect("proof IDs are 1-indexed"))
        .expect("contradiction line is written");

    assert_eq!(
        String::from_utf8(writer.writer).expect("proof output is valid UTF-8"),
        "pseudo-Boolean proof version 3.0\nf 3 ;\noutput NONE;\nconclusion UNSAT : 2;\nend pseudo-Boolean proof;\n",
    );
}

#[test]
fn test_conclude_opt_requires_bounds_and_writes_them() {
    let mut writer =
        VeriPbWriter::new(Vec::new(), 0).expect("header writes to an in-memory buffer");

    let err = writer
        .conclude_opt()
        .expect_err("OPT proofs need concrete lower and upper bounds");
    assert!(matches!(err, ProofError::MissingOptimizationBounds));

    writer
        .set_opt_bounds(4, 4)
        .expect("equal lower and upper bounds are valid");
    writer
        .conclude_opt()
        .expect("writer now has concrete optimization bounds");

    assert_eq!(
        String::from_utf8(writer.writer).expect("proof output is valid UTF-8"),
        "pseudo-Boolean proof version 3.0\nf 0 ;\noutput NONE;\nconclusion BOUNDS 4 4;\nend pseudo-Boolean proof;\n",
    );
}

#[test]
fn test_conclude_opt_hinted_writes_lower_id_and_upper_witness() {
    let mut writer =
        VeriPbWriter::new(Vec::new(), 2).expect("header writes to an in-memory buffer");

    writer
        .set_opt_bounds(10, 10)
        .expect("equal lower and upper bounds are valid");
    writer
        .conclude_opt_hinted(
            Some(ConstraintId::new(40).expect("proof IDs are 1-indexed")),
            Some("x1 ~x2 x3"),
        )
        .expect("hinted OPT conclusion should be valid");

    assert_eq!(
        String::from_utf8(writer.writer).expect("proof output is valid UTF-8"),
        "pseudo-Boolean proof version 3.0\nf 2 ;\noutput NONE;\nconclusion BOUNDS 10 : 40 10 : x1 ~x2 x3;\nend pseudo-Boolean proof;\n",
    );
}

#[test]
fn test_conclude_opt_hinted_omits_empty_witness_and_missing_hint() {
    let mut writer =
        VeriPbWriter::new(Vec::new(), 0).expect("header writes to an in-memory buffer");

    writer
        .set_opt_bounds(4, 7)
        .expect("lower below upper is valid");
    writer
        .conclude_opt_hinted(None, Some(""))
        .expect("hint-free conclusion stays valid");

    assert_eq!(
        String::from_utf8(writer.writer).expect("proof output is valid UTF-8"),
        "pseudo-Boolean proof version 3.0\nf 0 ;\noutput NONE;\nconclusion BOUNDS 4 7;\nend pseudo-Boolean proof;\n",
    );
}

#[test]
fn test_conclude_opt_infeasible_writes_infinite_bounds() {
    let mut writer =
        VeriPbWriter::new(Vec::new(), 0).expect("header writes to an in-memory buffer");

    writer
        .conclude_opt_infeasible()
        .expect("infeasible optimization conclusion should be valid");

    assert_eq!(
        String::from_utf8(writer.writer).expect("proof output is valid UTF-8"),
        "pseudo-Boolean proof version 3.0\nf 0 ;\noutput NONE;\nconclusion BOUNDS INF INF;\nend pseudo-Boolean proof;\n",
    );
}

#[test]
fn test_conclude_sat_writes_full_assignment_footer() {
    let mut writer =
        VeriPbWriter::new(Vec::new(), 2).expect("header writes to an in-memory buffer");

    writer
        .conclude_sat(&[true, false])
        .expect("SAT conclusion should succeed");

    assert_eq!(
        String::from_utf8(writer.writer).expect("proof output is valid UTF-8"),
        "pseudo-Boolean proof version 3.0\nf 2 ;\noutput NONE;\nconclusion SAT : x1 ~x2;\nend pseudo-Boolean proof;\n",
    );
}

#[test]
fn test_set_opt_bounds_rejects_invalid_interval() {
    let mut writer =
        VeriPbWriter::new(Vec::new(), 0).expect("header writes to an in-memory buffer");

    let err = writer
        .set_opt_bounds(5, 4)
        .expect_err("lower bound cannot exceed upper bound");

    assert!(matches!(
        err,
        ProofError::InvalidOptimizationBounds { lower: 5, upper: 4 }
    ));
}

#[test]
fn test_log_step_rejects_non_positive_scalars_and_divisors() {
    let mut writer =
        VeriPbWriter::new(Vec::new(), 1).expect("header writes to an in-memory buffer");
    let id = ConstraintId::new(1).expect("proof IDs are 1-indexed");

    let mul_err = writer
        .log_step(ProofStep::Multiply(id, 0))
        .expect_err("multiply requires a positive scalar");
    assert!(matches!(mul_err, ProofError::NonPositiveMultiplier(0)));

    let div_err = writer
        .log_step(ProofStep::Divide(id, -2))
        .expect_err("divide requires a positive divisor");
    assert!(matches!(div_err, ProofError::NonPositiveDivisor(-2)));
}

#[test]
fn test_constraint_id_overflow_is_reported() {
    let mut writer = VeriPbWriter::new(Vec::new(), u64::MAX)
        .expect("the header itself still fits in the output stream");
    let err = writer
        .log_step(ProofStep::Rup(String::from("+1 x1 >= 1 ;")))
        .expect_err("no derived IDs are available after u64::MAX inputs");

    assert!(matches!(err, ProofError::ConstraintIdOverflow));
}

#[test]
fn test_writer_propagates_io_errors_from_write_and_flush() {
    let write_result = VeriPbWriter::new(
        FailingWriter {
            fail_on_write: true,
            ..FailingWriter::default()
        },
        0,
    );
    assert!(matches!(write_result, Err(ProofError::Io(_))));

    let mut writer = VeriPbWriter::new(
        FailingWriter {
            fail_on_flush: true,
            ..FailingWriter::default()
        },
        0,
    )
    .expect("header writes before flush is requested");
    let flush_err = writer
        .flush()
        .expect_err("flush failure should be surfaced");
    assert!(matches!(flush_err, ProofError::Io(_)));
}
