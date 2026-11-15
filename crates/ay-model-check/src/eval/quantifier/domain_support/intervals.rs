// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sorted, disjoint half-open integer intervals, with explicit infinities.

use super::{charge, QuantifierRejection};
use crate::eval::Evaluator;
use num_bigint::BigInt;

const MAX_SUPPORT_INTERVALS: usize = 256;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Bound {
    NegativeInfinity,
    Finite(BigInt),
    PositiveInfinity,
}

impl Bound {
    fn words(&self) -> usize {
        match self {
            Self::Finite(value) => value.bits().div_ceil(64).max(1) as usize,
            _ => 1,
        }
    }
}

pub(super) struct Interval {
    pub(super) lower: Bound,
    pub(super) upper: Bound,
}

pub(super) struct Intervals(pub(super) Vec<Interval>);

impl Intervals {
    pub(super) fn empty() -> Self {
        Self(Vec::new())
    }

    pub(super) fn whole() -> Self {
        Self::between(Bound::NegativeInfinity, Bound::PositiveInfinity)
    }

    pub(super) fn between(lower: Bound, upper: Bound) -> Self {
        if lower < upper {
            Self(vec![Interval { lower, upper }])
        } else {
            Self::empty()
        }
    }

    fn scale(&self) -> usize {
        self.0
            .iter()
            .map(|interval| interval.lower.words().max(interval.upper.words()))
            .max()
            .unwrap_or(1)
    }

    fn combined_work(&self, other: &Self) -> Result<(usize, usize), QuantifierRejection> {
        let count = self
            .0
            .len()
            .checked_add(other.0.len())
            .ok_or(QuantifierRejection::EvaluationBudget)?;
        if count > MAX_SUPPORT_INTERVALS {
            return Err(QuantifierRejection::EvaluationBudget);
        }
        // A quadratic bound also covers sorting comparisons and BigInt limb
        // comparisons; charge before allocating or sorting temporary storage.
        let work = count
            .max(1)
            .checked_mul(count.max(1))
            .and_then(|work| work.checked_mul(self.scale().max(other.scale())))
            .ok_or(QuantifierRejection::EvaluationBudget)?;
        Ok((count, work))
    }

    pub(super) fn union(
        mut self,
        other: Self,
        evaluator: &Evaluator<'_>,
    ) -> Result<Self, QuantifierRejection> {
        let (count, work) = self.combined_work(&other)?;
        charge(evaluator, work)?;
        self.0
            .try_reserve(other.0.len())
            .map_err(|_| QuantifierRejection::EvaluationBudget)?;
        self.0.extend(other.0);
        self.0.sort_unstable_by(|a, b| a.lower.cmp(&b.lower));
        let mut merged: Vec<Interval> = Vec::new();
        merged
            .try_reserve(count)
            .map_err(|_| QuantifierRejection::EvaluationBudget)?;
        for interval in self.0 {
            if let Some(previous) = merged.last_mut() {
                if interval.lower <= previous.upper {
                    if interval.upper > previous.upper {
                        previous.upper = interval.upper;
                    }
                    continue;
                }
            }
            merged.push(interval);
        }
        Ok(Self(merged))
    }

    pub(super) fn intersection(
        self,
        other: Self,
        evaluator: &Evaluator<'_>,
    ) -> Result<Self, QuantifierRejection> {
        let (count, work) = self.combined_work(&other)?;
        charge(evaluator, work)?;
        let mut output = Vec::new();
        output
            .try_reserve(count)
            .map_err(|_| QuantifierRejection::EvaluationBudget)?;
        let (mut left, mut right) = (0, 0);
        while let (Some(a), Some(b)) = (self.0.get(left), other.0.get(right)) {
            let lower = a.lower.clone().max(b.lower.clone());
            let upper = a.upper.clone().min(b.upper.clone());
            if lower < upper {
                output.push(Interval { lower, upper });
            }
            if a.upper < b.upper {
                left += 1;
            } else {
                right += 1;
            }
        }
        Ok(Self(output))
    }
}
