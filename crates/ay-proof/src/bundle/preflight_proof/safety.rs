// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checker-specific reachability bounds; source signatures are checked elsewhere.

use std::collections::BTreeSet;

use crate::checker::{is_exact_nan_identity, NanIdentityView};

use super::*;

enum Evaluator {
    BoundedBitVector,
    ProofProducingBitVector,
    FloatingPoint,
}

pub(super) fn validate(
    entries: &[(TermData, Sort)],
    step: usize,
    clause: &[TermId],
    kind: &TheoryLemmaKind,
    meter: &mut ProofMeter<'_>,
) -> Result<(), ProofCheckError> {
    let evaluator = match kind {
        TheoryLemmaKind::BvBitBlast | TheoryLemmaKind::BvBitBlastGate { .. } => {
            Evaluator::ProofProducingBitVector
        }
        TheoryLemmaKind::BoolTautology => Evaluator::BoundedBitVector,
        TheoryLemmaKind::FpClassification { .. } => Evaluator::FloatingPoint,
        _ => return Ok(()),
    };
    // The full snapshot/signature/source preflight still runs. Skip only the
    // bounded evaluator's reachability walk after independently establishing
    // this exact, width-independent theorem over borrowed snapshot entries.
    if matches!(evaluator, Evaluator::FloatingPoint)
        && is_exact_nan_identity(
            &mut SnapshotView {
                entries,
                step,
                meter,
            },
            clause,
        )?
    {
        return Ok(());
    }
    let mut seen = BTreeSet::new();
    let mut stack = Vec::new();
    for &literal in clause {
        meter.push(&mut stack, literal)?;
    }
    let mut assignment_bits = 0u32;
    while let Some(term) = stack.pop() {
        // Pay for ALL popped edges, including repeated references to a node.
        meter.charge(1, 0)?;
        if !meter.seen(&mut seen, term)? {
            continue;
        }
        let (data, sort) = meter.term(entries, term, step, "reachable term")?;
        match evaluator {
            Evaluator::BoundedBitVector => validate_bv(entries, data, sort, step, meter)?,
            // Bit-blast clauses have an independently replayed proof-producing
            // route. Its own width/work bounds remain authoritative. The
            // exhaustive classifier rejects widths and signed operations it
            // cannot safely evaluate before enumerating any assignment.
            // Keep traversing/charging every source node here; only the
            // bounded-only evaluator restriction belongs to BoolTautology.
            Evaluator::ProofProducingBitVector => {}
            Evaluator::FloatingPoint => {
                validate_fp(data, sort, step, &mut assignment_bits, meter)?;
            }
        }
        push_term_children(data, &mut stack, step, meter)?;
    }
    meter.charge(0, 0)
}

fn push_term_children(
    data: &TermData,
    stack: &mut Vec<TermId>,
    step: usize,
    meter: &mut ProofMeter<'_>,
) -> Result<(), ProofCheckError> {
    match data {
        TermData::App(_, args) => {
            for &arg in args {
                meter.push(stack, arg)?;
            }
        }
        TermData::Let(bindings, body) => {
            for (_, value) in bindings {
                meter.push(stack, *value)?;
            }
            meter.push(stack, *body)?;
        }
        TermData::Not(inner) => meter.push(stack, *inner)?,
        TermData::Ite(condition, then_branch, else_branch) => {
            for term in [*condition, *then_branch, *else_branch] {
                meter.push(stack, term)?;
            }
        }
        TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
            meter.push(stack, *body)?;
            for trigger in triggers {
                // Empty trigger sets still require traversal work.
                meter.charge(1, 0)?;
                for &term in trigger {
                    meter.push(stack, term)?;
                }
            }
        }
        TermData::Const(_) | TermData::Var(..) => {}
        _ => return meter.invalid(step, "reaches an unsupported term variant"),
    }
    Ok(())
}

fn validate_bv(
    entries: &[(TermData, Sort)],
    data: &TermData,
    sort: &Sort,
    step: usize,
    meter: &mut ProofMeter<'_>,
) -> Result<(), ProofCheckError> {
    if matches!(sort, Sort::BitVec(bv) if bv.width > MAX_BOUNDED_CHECKER_BV_WIDTH) {
        return meter.invalid(
            step,
            "reaches a bit-vector term wider than the bounded checker's 64-bit evaluator",
        );
    }
    let (args, message) = match data {
        TermData::App(Symbol::Named(name), args) => {
            // Seven comparisons with fixed names, each at most name.len()+1.
            meter.charge(meter::mul(meter::add(name.len(), 1)?, 7)?, 0)?;
            if !matches!(
                name.as_str(),
                "bvslt" | "bvsle" | "bvsgt" | "bvsge" | "bvsdiv" | "bvsrem" | "bvsmod"
            ) {
                return Ok(());
            }
            (
                args,
                "reaches a signed bit-vector operation at the bounded checker's unsafe 64-bit width",
            )
        }
        TermData::App(Symbol::Indexed(name, _), args) => {
            meter.charge(meter::add(name.len(), 1)?, 0)?;
            if name != "repeat" {
                return Ok(());
            }
            (
                args,
                "reaches `repeat` with an operand too wide for the bounded checker",
            )
        }
        _ => return Ok(()),
    };
    let Some(&operand) = args.first() else {
        return meter.invalid(
            step,
            "reaches a bit-vector operation with a missing operand",
        );
    };
    let (_, operand_sort) = meter.term(entries, operand, step, "bit-vector operand")?;
    if matches!(operand_sort, Sort::BitVec(bv) if bv.width >= u64::BITS) {
        return meter.invalid(step, message);
    }
    Ok(())
}

fn validate_fp(
    data: &TermData,
    sort: &Sort,
    step: usize,
    assignment_bits: &mut u32,
    meter: &mut ProofMeter<'_>,
) -> Result<(), ProofCheckError> {
    let Sort::FloatingPoint(exponent, significand) = sort else {
        return Ok(());
    };
    if *exponent > MAX_FP_CHECKER_EXPONENT_WIDTH {
        return meter.invalid(
            step,
            "reaches floating-point term with exponent width above the checker-safe limit 64",
        );
    }
    if matches!(data, TermData::Var(..)) {
        let Some(width) = exponent.checked_add(*significand) else {
            return meter.invalid(step, "overflows its floating-point assignment width");
        };
        let Some(total) = assignment_bits.checked_add(width) else {
            return meter.invalid(step, "overflows its floating-point assignment budget");
        };
        *assignment_bits = total;
        if total > MAX_FP_CHECKER_ASSIGNMENT_BITS {
            return meter.invalid(
                step,
                "exceeds the bounded floating-point checker's 16-bit assignment budget",
            );
        }
    }
    // NaN is one abstract value. The concrete decoder uses payload one and
    // never shifts a u64 by the significand width to construct it.
    Ok(())
}

struct SnapshotView<'entries, 'meter, 'progress> {
    entries: &'entries [(TermData, Sort)],
    step: usize,
    meter: &'meter mut ProofMeter<'progress>,
}

impl<'entries> NanIdentityView<'entries> for SnapshotView<'entries, '_, '_> {
    fn term(
        &mut self,
        id: TermId,
    ) -> Result<(&'entries TermData, &'entries Sort), ProofCheckError> {
        let entry = self
            .meter
            .term(self.entries, id, self.step, "NaN identity term")?;
        Ok((&entry.0, &entry.1))
    }

    fn charge(&mut self, work: usize) -> Result<(), ProofCheckError> {
        self.meter.charge(work, 0)
    }
}
