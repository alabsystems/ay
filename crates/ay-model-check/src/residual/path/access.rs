// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Keep the legacy field-only storage until an actual inner index is seen.

use super::*;

pub(super) enum ReversePath {
    Fields(Vec<String>),
    Access(Vec<AccessStep>),
}

impl Default for ReversePath {
    fn default() -> Self {
        Self::Fields(Vec::new())
    }
}

impl ReversePath {
    pub(super) fn len(&self) -> usize {
        match self {
            Self::Fields(fields) => fields.len(),
            Self::Access(steps) => steps.len(),
        }
    }

    pub(super) fn push_field(
        &mut self,
        name: &str,
        spend: &mut impl FnMut(usize) -> bool,
    ) -> Option<()> {
        let storage = match self {
            Self::Fields(_) => 1, // preserve the old field-only work schedule
            Self::Access(_) => std::mem::size_of::<AccessStep>(),
        };
        if !spend(name.len().checked_add(storage)?) {
            return None;
        }
        match self {
            Self::Fields(fields) => {
                fields.try_reserve(1).ok()?;
                fields.push(name.to_owned());
            }
            Self::Access(steps) => {
                steps.try_reserve(1).ok()?;
                steps.push(AccessStep::Field(name.to_owned()));
            }
        }
        Some(())
    }

    pub(super) fn push_index(
        &mut self,
        key: ModelValue,
        spend: &mut impl FnMut(usize) -> bool,
    ) -> Option<()> {
        if let Self::Fields(fields) = self {
            let count = fields.len().checked_add(1)?;
            if !spend(count.checked_mul(std::mem::size_of::<AccessStep>())?) {
                return None;
            }
            let mut steps = Vec::new();
            steps.try_reserve(count).ok()?;
            steps.extend(std::mem::take(fields).into_iter().map(AccessStep::Field));
            steps.push(AccessStep::Index(key));
            *self = Self::Access(steps);
        } else if let Self::Access(steps) = self {
            if !spend(std::mem::size_of::<AccessStep>()) {
                return None;
            }
            steps.try_reserve(1).ok()?;
            steps.push(AccessStep::Index(key));
        }
        Some(())
    }

    pub(super) fn finish(self) -> Option<Slot> {
        match self {
            Self::Fields(mut fields) => {
                fields.reverse();
                match fields.len() {
                    0 => Some(Slot::Whole),
                    1 => Some(Slot::Field(fields.pop()?)),
                    _ => Some(Slot::Path(fields)),
                }
            }
            Self::Access(mut steps) => {
                steps.reverse();
                Some(Slot::Access(steps))
            }
        }
    }
}
