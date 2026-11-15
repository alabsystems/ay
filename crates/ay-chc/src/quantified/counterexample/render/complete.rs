// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-generated assertion ranges, never a parser for retained/model text.

use super::*;
use std::ops::Range;

pub(super) enum Payloads {
    None,
    Retained(Vec<Range<usize>>),
}

impl Payloads {
    pub(super) fn retain(
        &mut self,
        start: usize,
        end: usize,
        control: &SourceControl<'_>,
    ) -> Result<()> {
        let Self::Retained(ranges) = self else {
            return Ok(());
        };
        // The source renderer itself just emitted `(assert PAYLOAD)\n`.
        // No string search, arbitrary command parsing or input authority here.
        let start = start.checked_add(8).ok_or_else(refused)?;
        let end = end
            .checked_sub(2)
            .filter(|end| start < *end)
            .ok_or_else(refused)?;
        control.charge(1).ok_or_else(refused)?;
        // Growing by one can move every prior record as well as allocate the
        // new backing. Prepay both logical populations before reserve.
        let records = ranges
            .len()
            .checked_mul(2)
            .and_then(|count| count.checked_add(1))
            .ok_or_else(refused)?
            .max(2);
        let bytes = records
            .checked_mul(std::mem::size_of::<Range<usize>>())
            .ok_or_else(refused)?;
        control.bytes(bytes).ok_or_else(refused)?;
        ranges.try_reserve_exact(1).map_err(|_| refused())?;
        ranges.push(start..end);
        Ok(())
    }
}

pub(in crate::quantified::counterexample) struct CompleteRendered<'a> {
    pub(in crate::quantified::counterexample) original: Rendered<'a>,
    pub(in crate::quantified::counterexample) assertions: Vec<Range<usize>>,
    pub(in crate::quantified::counterexample) prefix_end: usize,
}

pub(in crate::quantified::counterexample) fn render<'a>(
    problem: &'a QuantifiedChcProblem,
    indices: &[usize],
    edges: &[Vec<usize>],
    control: &SourceControl<'_>,
) -> Result<CompleteRendered<'a>> {
    let mut payloads = Payloads::Retained(Vec::new());
    let (obligation, scopes, functions) =
        render_inner(problem, indices, edges, control, &mut payloads)?;
    let original = manifest::retain(obligation, scopes, functions, control)?;
    let Payloads::Retained(assertions) = payloads else {
        return Err(refused());
    };
    let prefix_end = assertions
        .first()
        .and_then(|range| range.start.checked_sub(8))
        .ok_or_else(refused)?;
    control.poll().ok_or_else(refused)?;
    Ok(CompleteRendered {
        original,
        assertions,
        prefix_end,
    })
}

pub(in crate::quantified::counterexample) fn names(
    problem: &QuantifiedChcProblem,
    original: &Rendered<'_>,
    count: usize,
    control: &SourceControl<'_>,
) -> Result<Vec<String>> {
    if count > 8192 {
        return Err(refused());
    }
    let mut census = Names::new(problem, control)?;
    // Regenerate source names in their exact original order. This also avoids
    // every occurrence-local declaration, not only global source spellings.
    for binding in &original.bindings {
        control.charge(1).ok_or_else(refused)?;
        if census.fresh(control)? != binding.symbol {
            return Err(refused());
        }
    }
    control
        .bytes(
            count
                .checked_mul(std::mem::size_of::<String>())
                .ok_or_else(refused)?,
        )
        .ok_or_else(refused)?;
    let mut names = Vec::new();
    names.try_reserve_exact(count).map_err(|_| refused())?;
    for _ in 0..count {
        names.push(census.fresh(control)?);
    }
    control.poll().ok_or_else(refused)?;
    Ok(names)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CancellationToken;
    use ay_core::time::Instant;
    use std::time::Duration;

    #[test]
    fn complete_range_growth_prepays_prior_records_and_refuses_without_partial_admission() {
        let token = CancellationToken::new();
        let control = SourceControl::new(Instant::now() + Duration::from_secs(20), &token);
        let original: Vec<_> = (0..8).map(|index| index * 16..index * 16 + 1).collect();
        let mut payloads = Payloads::Retained(original.clone());
        let records = (2 * original.len() + 1).max(2);
        let growth = records * std::mem::size_of::<Range<usize>>();
        // Keep the charge(1) allowance plus one byte too little for the full
        // relocation. The obsolete fixed two-record prepayment would pass.
        control.bytes(64 * 1024 * 1024 - (64 + growth - 1)).unwrap();
        assert!(payloads.retain(128, 143, &control).is_err());
        let Payloads::Retained(ranges) = &payloads else {
            panic!("retained fixture");
        };
        assert_eq!(ranges, &original);
        assert!(control.debit(0, 0).is_none());
        assert!(payloads.retain(128, 143, &control).is_err());
        let Payloads::Retained(ranges) = &payloads else {
            panic!("retained fixture");
        };
        assert_eq!(ranges, &original);
    }
}
