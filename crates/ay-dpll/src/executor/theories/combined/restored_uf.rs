// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Transactional recovery of current UF applications under final typed values.
//!
//! Table rows are samples, not a complete occurrence inventory. In particular
//! an original application restored after preprocessing can have been omitted
//! by extraction's raw-key deduplication. Only CURRENT root/kernel occurrences
//! enter this transaction; scanning the whole TermStore would revive old scopes.
//! No equality discovered here is asserted back into the live solver.

use crate::combined_solvers::TheoryCombiner;
use crate::executor::model::CandidateOwner;
use crate::executor::Executor;
use crate::executor_types::UnknownOrigin;
use ay_core::{Sort, TermId};
use ay_euf::EufModel;
use ay_lia::LiaModel;
use num_bigint::BigInt;

mod evaluate;
mod inventory;
mod observation;
use observation::Probe;
#[cfg(test)]
mod tests;
mod transaction;
mod writeback;

type Pay<'a> = dyn FnMut(usize, usize) -> Result<(), UnknownOrigin> + 'a;
#[derive(Debug, PartialEq, Eq)]
enum Refusal {
    Unsupported,
    Conflict,
    Stopped(UnknownOrigin),
}
impl From<UnknownOrigin> for Refusal {
    fn from(value: UnknownOrigin) -> Self {
        Self::Stopped(value)
    }
}
type Checked<T> = Result<T, Refusal>;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Atom {
    Int(BigInt),
    Bool(bool),
    Carrier(String),
}
fn total(parts: &[usize]) -> Checked<usize> {
    parts.iter().try_fold(0usize, |sum, &part| {
        sum.checked_add(part).ok_or(Refusal::Unsupported)
    })
}
fn charge(pay: &mut Pay<'_>, work: &[usize], bytes: &[usize]) -> Checked<()> {
    pay(total(work)?, total(bytes)?)?;
    Ok(())
}
fn integer_bytes(value: &BigInt) -> Checked<usize> {
    let bits = usize::try_from(value.bits()).map_err(|_| Refusal::Unsupported)?;
    total(&[bits.checked_add(7).ok_or(Refusal::Unsupported)? / 8, 64])
}
impl Atom {
    fn payload(&self) -> Checked<usize> {
        match self {
            Self::Int(value) => integer_bytes(value),
            Self::Bool(_) => Ok(1),
            Self::Carrier(value) => Ok(value.len()),
        }
    }
    fn copy(&self, pay: &mut Pay<'_>) -> Checked<Self> {
        let bytes = self.payload()?;
        charge(pay, &[1, bytes], &[bytes, 64])?;
        Ok(match self {
            Self::Int(value) => Self::Int(value.clone()),
            Self::Bool(value) => Self::Bool(*value),
            Self::Carrier(value) => Self::Carrier(value.as_str().to_owned()),
        })
    }
    fn same(&self, other: &Self, pay: &mut Pay<'_>) -> Checked<bool> {
        charge(pay, &[1, self.payload()?, other.payload()?], &[])?;
        Ok(self == other)
    }
    fn render(&self, pay: &mut Pay<'_>) -> Checked<String> {
        // Decimal digits <= bit count + sign/parentheses. Charge before format.
        let bound = match self {
            Self::Int(value) => total(&[
                usize::try_from(value.bits()).map_err(|_| Refusal::Unsupported)?,
                8,
            ])?,
            Self::Bool(_) => 5,
            Self::Carrier(value) => value.len(),
        };
        charge(pay, &[bound, 1], &[bound, 32])?;
        Ok(match self {
            Self::Int(value) => crate::executor_format::format_bigint(value),
            Self::Bool(value) => value.to_string(),
            Self::Carrier(value) => value.clone(),
        })
    }
}

fn entries(pay: &mut Pay<'_>, count: usize) -> Checked<()> {
    let bytes = count.checked_mul(256).ok_or(Refusal::Unsupported)?;
    pay(count, bytes)?;
    Ok(())
}
fn same_sort(a: &Sort, b: &Sort, pay: &mut Pay<'_>) -> Checked<bool> {
    // Only scalar/free nominal sorts are admitted, so this cannot recurse into
    // an unmetered Array/Datatype tree or use a rendered sort as identity.
    let bytes = |sort: &Sort| match sort {
        Sort::Uninterpreted(name) => name.len(),
        _ => 1,
    };
    charge(pay, &[1, bytes(a), bytes(b)], &[])?;
    Ok(a == b)
}

pub(super) fn recover(
    exec: &Executor,
    theory: &TheoryCombiner<'_>,
    roots: &[TermId],
    euf: &mut EufModel,
    lia: &mut Option<LiaModel>,
) {
    let probe = Probe::new(ay_core::misc_cli_flags().model_reject_dump);
    let mut owner = match CandidateOwner::capture(exec) {
        Ok(owner) => owner,
        Err(origin) => {
            probe.emit(exec, &Err(Refusal::Stopped(origin)));
            return;
        }
    };
    let mut pay = |work, bytes| {
        if let Some(origin) = theory.model_recovery_phase_stop() {
            return Err(owner.refuse(origin));
        }
        owner.pay(work, bytes)
    };
    // An optional repair is never a publication certificate. Unsupported or
    // conflicting candidates remain byte-for-byte untouched; a stop stays
    // latched in the original attempt. All existing outer gates still run.
    let result = run_observed(
        &exec.ctx,
        theory.euf_for_model_recovery(),
        roots,
        euf,
        lia,
        &mut pay,
        &probe,
    );
    probe.emit(exec, &result);
}

#[cfg(test)]
fn run(
    ctx: &ay_frontend::Context,
    live: &ay_euf::EufSolver<'_>,
    roots: &[TermId],
    euf: &mut EufModel,
    lia: &mut Option<LiaModel>,
    pay: &mut Pay<'_>,
) -> Checked<()> {
    run_observed(ctx, live, roots, euf, lia, pay, &Probe::new(false))
}

fn run_observed(
    ctx: &ay_frontend::Context,
    live: &ay_euf::EufSolver<'_>,
    roots: &[TermId],
    euf: &mut EufModel,
    lia: &mut Option<LiaModel>,
    pay: &mut Pay<'_>,
    probe: &Probe,
) -> Checked<()> {
    probe.phase("capture");
    let inventory = inventory::capture(ctx, live, roots, euf, lia.as_ref(), pay, probe)?;
    probe.captured(
        inventory.nodes.len(),
        inventory.apps.len(),
        inventory.completed_outputs,
    );
    probe.phase("closure");
    let closure = transaction::close(&inventory, pay, probe)?;
    probe.closed();
    // This pass repairs an actual inconsistency in current own values. Missing
    // sampled rows alone do not authorize rewriting an already coherent model.
    // Existing table-collision/validation gates retain their independent role.
    probe.phase("no-op-check");
    let changed = closure.changes_value(&inventory, pay)?;
    probe.changed(changed);
    // A newly completed output still needs atomic materialization even when
    // congruence did not further change its proposed false value. Ordinary
    // already-captured coherent models retain the cheap no-op path.
    if !changed && inventory.completed_outputs == 0 {
        return Ok(());
    }
    probe.phase("writeback");
    let result = writeback::commit(&inventory, &closure, euf, lia, pay, probe);
    if result.is_ok() {
        probe.committed();
    }
    result
}
