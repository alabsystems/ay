// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QSAT with model-based projection for quantified linear arithmetic
//! (roadmap component QS).
//!
//! A PURE search engine over a host kernel: [`prenex::build_game`] turns the
//! authored roots into a prenex game over fresh engine variables,
//! [`game::solve`] plays it, and [`mbp::project`] is the projection that
//! generalizes each lost position. Nothing here publishes: every verdict is
//! a hint that a publication route re-derives (the quantified model gate for
//! `sat`, an authored-scope proof for `unsat`).

pub(crate) mod eval;
pub(crate) mod formula;
pub(crate) mod game;
pub(crate) mod lin;
pub(crate) mod mbp;
pub(crate) mod prenex;
pub(crate) mod strategy;
pub(crate) mod strategy_check;
pub(crate) mod subst;

#[cfg(test)]
mod tests;

pub(crate) use game::{solve, Caps, KernelAnswer, Outcome, QsatHost, Run};
pub(crate) use lin::Val;
pub(crate) use prenex::{build_game, Game};
