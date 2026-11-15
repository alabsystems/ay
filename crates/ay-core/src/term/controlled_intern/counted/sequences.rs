// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Closed sequence constructors; never run the eager sequence rewriter.
use super::*;

fn copy_sort(sort: &Sort, owner: &dyn TermConstructionAdmission) -> Result<Sort> {
    let priced = crate::term::snapshot::meter_sort(sort, 0, &mut |work, bytes| {
        owner.admit(work, bytes).is_ok()
    });
    owner.check()?;
    priced.map_err(|_| CountedTermError::Unsupported)?;
    Ok(sort.clone())
}

impl<O: TermConstructionAdmission> CountedTermBuilder<'_, '_, O> {
    /// Copy a UTF-8 literal only after its occupied bytes are admitted.
    pub fn string(&mut self, value: &str) -> Result<TermId> {
        self.owner.admit(value.len(), value.len())?;
        let mut output = String::new();
        output
            .try_reserve_exact(value.len())
            .map_err(|_| storage::storage(self.owner))?;
        output.push_str(value);
        self.owner.check()?;
        self.publish_sequence(
            TermData::Const(Constant::String(output)),
            Sort::String,
            Some(false),
        )
    }

    /// The empty word of the same sequence sort as an existing live term.
    pub fn sequence_empty(&mut self, source: TermId) -> Result<TermId> {
        self.owner.admit(1, 0)?;
        let sort = self
            .store
            .terms
            .get(source.index())
            .ok_or(CountedTermError::InvalidInput)?;
        // A known negative source fact proves its result sort field-free.
        // Otherwise retain unknown rather than invoking a separate census.
        let presence = (sort.field_presence == Some(false)).then_some(false);
        let sort = copy_sort(&sort.sort, self.owner)?;
        let term = match &sort {
            Sort::String => TermData::Const(Constant::String(String::new())),
            Sort::Seq(_) => payload::named("seq.empty", &[], self.owner)?,
            _ => return Err(CountedTermError::InvalidInput),
        };
        self.publish_sequence(term, sort, presence)
    }

    /// Binary concatenation with exact operand-sort checks and no flattening.
    pub fn sequence_concat(&mut self, left: TermId, right: TermId) -> Result<TermId> {
        self.owner.admit(2, 0)?;
        let a = self
            .store
            .terms
            .get(left.index())
            .ok_or(CountedTermError::InvalidInput)?;
        let b = self
            .store
            .terms
            .get(right.index())
            .ok_or(CountedTermError::InvalidInput)?;
        if !inspection::sort_equal(&a.sort, &b.sort, self.owner)? {
            return Err(CountedTermError::InvalidInput);
        }
        let name = match &a.sort {
            Sort::String => "str.++",
            Sort::Seq(_) => "seq.++",
            _ => return Err(CountedTermError::InvalidInput),
        };
        let presence = (a.field_presence == Some(false)).then_some(false);
        let sort = copy_sort(&a.sort, self.owner)?;
        let term = payload::named(name, &[left, right], self.owner)?;
        self.publish_sequence(term, sort, presence)
    }

    /// Materialize a literal repetition only after its actual UTF-8 output is
    /// admitted. The count comes from the caller's rewriting rule, not a grant.
    pub fn string_repeat(&mut self, source: TermId, count: u32) -> Result<TermId> {
        self.owner.admit(1, 0)?;
        let entry = self
            .store
            .terms
            .get(source.index())
            .ok_or(CountedTermError::InvalidInput)?;
        let TermData::Const(Constant::String(value)) = &entry.term else {
            return Err(CountedTermError::InvalidInput);
        };
        if entry.sort != Sort::String {
            return Err(CountedTermError::InvalidInput);
        }
        if value.is_empty() {
            self.owner.check()?;
            return Ok(source);
        }
        let count = usize::try_from(count).map_err(|_| storage::storage(self.owner))?;
        let bytes = value
            .len()
            .checked_mul(count)
            .ok_or_else(|| storage::storage(self.owner))?;
        self.owner.admit(bytes, bytes)?;
        let mut output = String::new();
        output
            .try_reserve_exact(bytes)
            .map_err(|_| storage::storage(self.owner))?;
        for _ in 0..count {
            self.owner.admit(value.len().max(1), 0)?;
            output.push_str(value);
        }
        self.owner.check()?;
        self.publish_sequence(
            TermData::Const(Constant::String(output)),
            Sort::String,
            Some(false),
        )
    }

    fn publish_sequence(
        &mut self,
        term: TermData,
        sort: Sort,
        presence: Option<bool>,
    ) -> Result<TermId> {
        self.check_generated_head(&term)?;
        // These closed constructors validated their sequence operand/result
        // sorts above. Reuse the generic snapshot-priced native interner;
        // the separate closed Boolean/BV/FP vocabulary remains unchanged.
        let result = self.intern_typed_data(term, sort, presence);
        self.owner.check()?;
        result
    }
}
