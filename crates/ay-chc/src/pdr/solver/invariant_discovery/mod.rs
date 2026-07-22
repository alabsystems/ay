// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proactive invariant discovery routines.

use super::*;

mod array_content;
mod bounds;
mod bv_group;
mod conditional;
mod counting;
mod exit_value;
mod parity;

#[cfg(test)]
mod tests;
