// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Allocation policy shared by the existing constructor and its counted entry.
//! The ordinary policy cannot fail; the counted policy never invokes its
//! ordinary-constructor closure. All counted errors latch the original owner.

use ay_core::original_query::{CountedAdmission, CountedAdmissionError, QueryError};
use std::convert::Infallible;

pub(super) trait Construction {
    type Error;
    fn choose<T>(
        &self,
        ordinary: impl FnOnce() -> T,
        counted: impl FnOnce(&CountedAdmission) -> Result<T, CountedAdmissionError>,
    ) -> Result<T, Self::Error>;
    fn boxed<T>(&self, value: T) -> Result<Box<T>, Self::Error>;

    fn metadata<T>(&self) -> Result<(), Self::Error> {
        self.choose(|| (), |owner| owner.admit(size_of::<T>().max(1), 0))
    }

    fn unsupported(&self, condition: bool, why: &'static str) -> Result<(), Self::Error> {
        self.choose(
            || (),
            |owner| {
                if condition {
                    Err(owner.refuse(CountedAdmissionError::Original(
                        QueryError::Invalid(why).into(),
                    )))
                } else {
                    owner.check()
                }
            },
        )
    }

    fn filled<T: Clone>(&self, len: usize, value: T) -> Result<Vec<T>, Self::Error> {
        self.choose(
            || vec![value.clone(); len],
            |owner| crate::counted_storage::try_vec_with(owner, len, |_| value.clone()),
        )
    }

    fn indexed<T>(&self, len: usize, make: impl Fn(usize) -> T) -> Result<Vec<T>, Self::Error> {
        self.choose(
            || (0..len).map(&make).collect(),
            |owner| crate::counted_storage::try_vec_with(owner, len, &make),
        )
    }

    fn reserved<T>(&self, capacity: usize) -> Result<Vec<T>, Self::Error> {
        self.choose(
            || Vec::with_capacity(capacity),
            |owner| {
                let bytes = capacity
                    .checked_mul(size_of::<T>())
                    .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
                owner.admit(capacity.max(1), bytes)?;
                let mut values = Vec::new();
                values
                    .try_reserve_exact(capacity)
                    .map_err(|_| owner.refuse(CountedAdmissionError::Memory))?;
                Ok(values)
            },
        )
    }
}

pub(super) struct Ordinary;

impl Construction for Ordinary {
    type Error = Infallible;
    fn choose<T>(
        &self,
        ordinary: impl FnOnce() -> T,
        _: impl FnOnce(&CountedAdmission) -> Result<T, CountedAdmissionError>,
    ) -> Result<T, Infallible> {
        Ok(ordinary())
    }
    fn boxed<T>(&self, value: T) -> Result<Box<T>, Infallible> {
        Ok(Box::new(value))
    }
}

pub(super) struct Counted<'a>(pub(super) &'a CountedAdmission);

impl Construction for Counted<'_> {
    type Error = CountedAdmissionError;
    fn choose<T>(
        &self,
        _: impl FnOnce() -> T,
        counted: impl FnOnce(&CountedAdmission) -> Result<T, CountedAdmissionError>,
    ) -> Result<T, Self::Error> {
        counted(self.0)
    }
    fn boxed<T>(&self, value: T) -> Result<Box<T>, Self::Error> {
        let bytes = size_of::<T>();
        self.0.admit(bytes.max(1), bytes)?;
        Box::try_new(value).map_err(|_| self.0.refuse(CountedAdmissionError::Memory))
    }
}
