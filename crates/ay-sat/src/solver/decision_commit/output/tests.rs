// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::test_owner;

#[test]
fn diagnostic_bytes_match_ordinary_formats_at_all_numeric_and_pass_extremes() {
    let mut s = Solver::new(1);
    s.num_conflicts = u64::MAX;
    let lit = Literal::negative(Variable::new((u32::MAX >> 1) - 1));
    for pass in DiagnosticPass::BY_CODE {
        s.cold.diagnostic_pass = pass;
        let owner = test_owner((3 * OUTPUT_CAPACITY) as u64, OUTPUT_CAPACITY);
        let plan = PreparedOutput::prepare_with(
            &s,
            lit,
            u32::MAX,
            Some(lit.variable().index() + 1),
            Logging::Enabled,
            &owner,
        )
        .unwrap()
        .unwrap();
        let expected = format!(
            "TRIAGE_ASSIGN: lit_idx={} level={} pass={:?} reason NONE\n[SAT d{}c{}] assign {} at level {} (dl={}) reason None\n[SAT d{}c{}] decide {}@{}+1 level {}\n",
            lit.index(), u32::MAX, pass, u32::MAX, u64::MAX, lit.to_dimacs(), u32::MAX, u32::MAX,
            u32::MAX, u64::MAX, lit.to_dimacs(), u32::MAX, u32::MAX,
        );
        assert_eq!(plan.bytes(), expected.as_bytes());
        assert!(plan.len < OUTPUT_CAPACITY);
        assert_eq!(owner.usage().unwrap().work_remaining, 0);
        assert_eq!(owner.usage().unwrap().storage_remaining, 0);
    }
}

#[test]
fn each_output_cost_is_paid_before_fixed_buffer_construction() {
    let s = Solver::new(1);
    let lit = Literal::positive(Variable::new(0));
    for logging in [Logging::Disabled, Logging::Enabled] {
        for (work, storage, admitted) in [
            ((3 * OUTPUT_CAPACITY) as u64, OUTPUT_CAPACITY, true),
            ((3 * OUTPUT_CAPACITY - 1) as u64, OUTPUT_CAPACITY, false),
            ((3 * OUTPUT_CAPACITY) as u64, OUTPUT_CAPACITY - 1, false),
        ] {
            let owner = test_owner(work, storage);
            assert_eq!(
                PreparedOutput::prepare_with(&s, lit, 1, Some(1), logging, &owner).is_ok(),
                admitted
            );
        }
    }
    assert!(
        PreparedOutput::prepare_with(&s, lit, 1, None, Logging::Disabled, &test_owner(0, 0))
            .unwrap()
            .is_none()
    );
}

#[test]
fn fixed_diagnostic_buffer_refuses_overflow_without_partial_append() {
    let mut plan = PreparedOutput {
        bytes: [0; OUTPUT_CAPACITY],
        len: OUTPUT_CAPACITY - 1,
    };
    assert!(fmt::Write::write_str(&mut plan, "xx").is_err());
    assert_eq!(plan.len, OUTPUT_CAPACITY - 1);
    assert_eq!(plan.bytes[OUTPUT_CAPACITY - 1], 0);
}

#[cfg(ay_logging)]
#[test]
fn actual_borrowed_literal_label_matches_assigned_and_unassigned_logging() {
    let mut s = Solver::new(1);
    let lit = Literal::negative(Variable::new(0));
    assert_eq!(s.fmt_lit(lit).to_string(), "-1@0?");
    s.decide(lit);
    assert_eq!(s.fmt_lit(lit).to_string(), "-1@1+1");
    assert_eq!(s.fmt_lit(lit.negated()).to_string(), "1@1+0");
}
