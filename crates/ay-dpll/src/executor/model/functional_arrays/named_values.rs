// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private complete-data extraction; the public caller owns accepted-SAT checks.

use crate::executor_types::UnknownOrigin;

use super::*;

impl Executor {
    /// Borrow one installed model and retain its original cumulative owner.
    /// None means that this model has no selected functional entry for the
    /// exact term; any source/type/resource refusal is an error, not a fallback.
    pub(crate) fn functional_array_snapshots_for_named_values(
        &self,
        terms: &[TermId],
    ) -> Result<Vec<Option<Arc<ArraySnapshot>>>, String> {
        self.check_evaluation_read()?;
        if terms.len() > 4096 || !self.produce_models_enabled() {
            return Err("complete named-value batch unavailable or over request limit".to_owned());
        }
        let model = self
            .last_model
            .as_ref()
            .ok_or_else(|| "complete named-value native model is unavailable".to_owned())?;
        // The original producer has at most its 1M work census of entries.
        // Thirty-two records per request covers binary-search comparisons and
        // the fixed vector/Arc operations; full stamp/root work is paid below.
        let work = terms
            .len()
            .checked_mul(32)
            .and_then(|work| work.checked_add(1))
            .ok_or_else(|| "complete named-value work overflow".to_owned())?;
        model.charge_functional_array_work(self, work)?;
        model.validate_functional_array_source(self)?;
        let mut values = Vec::new();
        values
            .try_reserve_exact(terms.len())
            .map_err(|_| self.complete_named_value_allocation_refused())?;
        for &term in terms {
            self.check_evaluation_read()?;
            if self.ctx.terms.entry_stamp(term).is_none() {
                return Err("complete named-value term is not live".to_owned());
            }
            let value = model.functional_array_value(self, term)?;
            if let Some(value) = &value {
                if value.sort() != self.ctx.terms.sort(term)
                    || !matches!(self.ctx.terms.get(term), ay_core::TermData::Var(..))
                {
                    return Err("complete named-value snapshot carrier/sort mismatch".to_owned());
                }
            }
            values.push(value);
        }
        model.validate_functional_array_source(self)?;
        self.check_evaluation_read()?;
        Ok(values)
    }

    pub(crate) fn complete_named_value_allocation_refused(&self) -> String {
        // Preserve an already-live original stop before observing this refusal.
        let _ = self.poll_evaluation_stop();
        self.record_evaluation_stop(UnknownOrigin::MemoryBudget);
        "complete named-value batch allocation refused".to_owned()
    }
}
