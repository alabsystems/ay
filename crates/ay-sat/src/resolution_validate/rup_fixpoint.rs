// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! FIXPOINT driver for bounded RUP hint replay.

use super::{
    scan_hint, HintScan, ResolutionDagValidateError, ResolutionValidationError, WorkMeter,
};
use crate::literal::Literal;
use crate::resolution_dag::RupStep;
use std::collections::HashMap;

pub(super) fn replay_hints_to_fixpoint(
    step: &RupStep,
    db: &HashMap<u64, &[Literal]>,
    assign: &mut [Option<bool>],
    trail: &mut Vec<usize>,
    fixed_variables: &[u8],
    meter: &mut WorkMeter<'_>,
) -> Result<(), ResolutionValidationError> {
    let mut last_nonunit: Option<u64> = None;
    loop {
        let mut progressed = false;
        let mut saw_nonunit = false;
        for &hint in &step.rup_hints {
            meter.charge(1)?;
            let Some(hint_clause) = db.get(&hint) else {
                return Err(ResolutionDagValidateError::UnknownHint {
                    step: step.id,
                    hint,
                }
                .into());
            };
            match scan_hint(hint_clause, assign, fixed_variables, meter)? {
                HintScan::Conflict => return Ok(()),
                HintScan::Propagate(lit) => {
                    let var = lit.variable().index();
                    assign[var] = Some(lit.is_positive());
                    trail.push(var);
                    progressed = true;
                }
                HintScan::SatisfiedUnit | HintScan::FixedPremiseSatisfied => {}
                HintScan::NonUnit => {
                    saw_nonunit = true;
                    last_nonunit = Some(hint);
                }
            }
        }
        if !progressed {
            // Preserve the historical error payload at a stalled fixpoint.
            if saw_nonunit {
                if let Some(hint) = last_nonunit {
                    return Err(ResolutionDagValidateError::HintNotUnit {
                        step: step.id,
                        hint,
                    }
                    .into());
                }
            }
            break;
        }
    }
    Err(ResolutionDagValidateError::NoConflict { step: step.id }.into())
}

#[cfg(test)]
mod tests {
    use super::super::{
        ResolutionDagValidateError, ResolutionValidationError, ResolutionValidationLimits,
    };
    use crate::literal::{Literal, Variable};
    use crate::resolution_dag::{ResolutionDag, RupStep};

    #[test]
    fn bounded_replay_accepts_hints_that_reach_conflict_at_fixpoint() {
        let a = Variable::new(0);
        let b = Variable::new(1);
        let dag = ResolutionDag {
            num_vars: 2,
            original_clauses: vec![
                (1, vec![Literal::positive(a), Literal::positive(b)]),
                (2, vec![Literal::negative(a)]),
                (3, vec![Literal::negative(b)]),
            ],
            derived: vec![RupStep {
                id: 4,
                clause: Vec::new(),
                rup_hints: vec![1, 2, 3],
            }],
            empty_clause_id: 4,
        };

        assert_eq!(
            dag.validate_with_limits(&ResolutionValidationLimits::unbounded()),
            Ok(())
        );
    }

    #[test]
    fn bounded_replay_reports_last_nonunit_hint_at_stalled_fixpoint() {
        let a = Variable::new(0);
        let b = Variable::new(1);
        let c = Variable::new(2);
        let d = Variable::new(3);
        let dag = ResolutionDag {
            num_vars: 4,
            original_clauses: vec![
                (1, vec![Literal::positive(a), Literal::positive(b)]),
                (2, vec![Literal::positive(c), Literal::positive(d)]),
            ],
            derived: vec![RupStep {
                id: 3,
                clause: Vec::new(),
                rup_hints: vec![1, 2],
            }],
            empty_clause_id: 3,
        };

        assert_eq!(
            dag.validate_with_limits(&ResolutionValidationLimits::unbounded()),
            Err(ResolutionValidationError::Invalid(
                ResolutionDagValidateError::HintNotUnit { step: 3, hint: 2 }
            ))
        );
    }
}
