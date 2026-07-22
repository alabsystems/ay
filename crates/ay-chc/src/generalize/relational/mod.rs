// Copyright 2026 Andrew Yates
// Author: Andrew Yates
//
// Licensed under the Apache License, Version 2.0

//! Relational lemma generalizers for CHC solving.
//!
//! Split into submodules by generalizer type:
//! - `constant_sum`: Sum invariant discovery (x + y = k)
//! - `equality`: Equality/disequality/offset patterns
//! - `implication`: Conditional invariants ((pc=2) => (lock=1))
//! - `template`: Template-based generalization from CHC problem structure

mod constant_sum;
mod equality;
mod implication;
mod template;

pub(crate) use constant_sum::ConstantSumGeneralizer;
pub(crate) use equality::RelationalEqualityGeneralizer;
pub(crate) use implication::ImplicationGeneralizer;
pub(crate) use template::TemplateGeneralizer;
