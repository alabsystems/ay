// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authored Boolean clauses feeding the existing proof-producing UF closure.
//! Only forced units are derived. Every source is an initial fact with an
//! `assume`/`and_pos` derivation, followed by `or`/`implies` and resolution.

use super::facts::FactReason;
use super::instances::{ClauseOrigin, InstanceClause, InstanceShape};
use super::*;

const MAX_AUTHORED_CLAUSES: usize = 64;
const MAX_CLAUSE_LITERALS: usize = 64;

impl Executor {
    pub(super) fn seed_authored_ground_clauses(&mut self, search: &mut GroundSearch) -> Option<()> {
        // Capture only initial facts. A clause never depends on a unit it
        // itself propagated, even if the latter has the same surface shape.
        let initial = search.facts.facts().len();
        let mut clauses = 0usize;
        for index in 0..initial {
            let fact = search.facts.facts().get(index)?;
            if !matches!(
                fact.reason,
                FactReason::Root | FactReason::Conjunct { .. } | FactReason::SubConjunct { .. }
            ) {
                continue;
            }
            let instance = fact.literal;
            let TermData::App(symbol, args) = self.ctx.terms.get(instance) else {
                continue;
            };
            if !matches!((symbol.name(), args.len()), ("or", 2..) | ("=>", 2)) {
                continue;
            }
            if clauses >= MAX_AUTHORED_CLAUSES {
                return Some(());
            }
            if args.len() > MAX_CLAUSE_LITERALS {
                continue;
            }
            if self.ctx.terms.sort(instance) != &Sort::Bool
                || args
                    .iter()
                    .any(|&arg| self.ctx.terms.sort(arg) != &Sort::Bool)
            {
                return None;
            }
            let (shape, literals) = self.instance_literals(instance);
            if shape == InstanceShape::Unit {
                return None;
            }
            for &literal in &literals {
                self.register_literal_operands(&mut search.closure, literal)?;
            }
            search.facts.push_clause(InstanceClause {
                origin: ClauseOrigin::AuthoredFact(index),
                instance,
                shape,
                literals,
            });
            clauses += 1;
        }
        Some(())
    }
}
