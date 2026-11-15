// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Counted-slice sizing seam for eager-persistent determinism tests.

/// What a round's counted slice is divided by: 1 in a production build, and
/// whatever a determinism test set (at least 1) under the seam.
#[inline]
#[must_use]
pub fn slice_divisor() -> u64 {
    #[cfg(any(test, feature = "determinism-seams"))]
    {
        super::test_seams::round_slice_divisor()
    }
    #[cfg(not(any(test, feature = "determinism-seams")))]
    {
        1
    }
}
