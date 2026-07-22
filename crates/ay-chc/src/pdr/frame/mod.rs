// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Frame and lemma types for PDR solver.

use std::cell::RefCell;

use crate::smt::{SmtContext, SmtResult};
use crate::{ChcExpr, ChcOp, ChcSort, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

use super::reach_fact::ReachFactId;

/// PDR result type — alias for the unified ChcEngineResult (#2791).
pub type PdrResult = crate::engine_result::ChcEngineResult;

mod core;
mod lemma;
mod must_summaries;
mod subsumption;
#[cfg(test)]
mod tests;
#[cfg(kani)]
mod verification;

pub(crate) use self::core::Frame;
pub(crate) use self::core::MAX_GLOBAL_LEMMAS;
pub(crate) use lemma::Lemma;
pub(crate) use must_summaries::MustSummaries;
