// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The model's own value of the leaves a ground array definition's operands
//! read but the BV leaf evaluator cannot fold.
//!
//! `store_chain_operand_value` recomputes an operand from its leaves and never
//! trusts a cached compound value (#store-chain-dead-node). Two leaf kinds have
//! no BV bits of their own to recompute from, so every definition mentioning
//! one stayed unresolved and withheld its variable:
//!
//! - an array read `(select a i)` over an array variable `a`, Bool- or
//!   BV-element (a Bool-element read is a SAT atom with no BV bits at all);
//! - an uninterpreted application `(f x)` over BV/Bool arguments.
//!
//! Each is seeded with the value the final model itself gives it, from the
//! same source the model evaluator reads: `a`'s interpretation at `i`'s value
//! for a read (resolved like a store base, so a withheld `a` refuses), and the
//! application's own SAT value for `(f x)`. The definition then resolves to
//! exactly the cells the model's evaluator computes for its operands. This is
//! model data only; the complete original-root validation still judges it.

use super::*;

impl Executor {
    /// Seed `memo` with the model's value of every array read over an array
    /// variable and every uninterpreted application inside `operand`, inner
    /// leaves first, so the leaf evaluator folds the operand around them.
    /// Leaves without such a value are left unseeded and the operand stays
    /// unresolved, exactly as before.
    pub(super) fn seed_definition_operand_leaves(
        terms: &TermStore,
        bv_model: &BvModel,
        operand: TermId,
        array_model: &mut ArrayModel,
        memo: &mut BvEvalMemo,
    ) {
        const MAX_NODES: usize = 4096;
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack = vec![(operand, false)];
        while let Some((term, children_done)) = stack.pop() {
            if children_done {
                Self::seed_definition_operand_leaf(terms, bv_model, term, array_model, memo);
                continue;
            }
            if seen.len() >= MAX_NODES || !seen.insert(term) {
                continue;
            }
            stack.push((term, true));
            match terms.get(term) {
                TermData::App(_, args) => stack.extend(args.iter().map(|&arg| (arg, false))),
                TermData::Not(inner) => stack.push((*inner, false)),
                TermData::Ite(cond, then_term, else_term) => {
                    stack.extend([(*cond, false), (*then_term, false), (*else_term, false)]);
                }
                _ => {}
            }
        }
    }

    fn seed_definition_operand_leaf(
        terms: &TermStore,
        bv_model: &BvModel,
        term: TermId,
        array_model: &mut ArrayModel,
        memo: &mut BvEvalMemo,
    ) {
        if memo.bv.contains_key(&term) || memo.boolean.contains_key(&term) {
            return;
        }
        let TermData::App(sym, args) = terms.get(term) else {
            return;
        };
        let fits = |value: &BigInt, width: u32| {
            value.sign() != num_bigint::Sign::Minus && value.bits() <= u64::from(width)
        };
        if sym.name() == "select" && args.len() == 2 {
            let Some(cell) = Self::definition_operand_read_value(
                terms,
                bv_model,
                args[0],
                args[1],
                array_model,
                memo,
            ) else {
                return;
            };
            match (terms.sort(term), cell.as_str()) {
                (Sort::BitVec(sort), _) => {
                    if let Some(value) = Self::parse_interpretation_bitvec(&cell)
                        .filter(|value| fits(value, sort.width))
                    {
                        memo.bv.insert(term, value);
                    }
                }
                (Sort::Bool, "true") => {
                    memo.boolean.insert(term, true);
                }
                (Sort::Bool, "false") => {
                    memo.boolean.insert(term, false);
                }
                _ => {}
            }
            return;
        }
        if !Self::is_uninterpreted_operand_application(terms, sym.name(), args) {
            return;
        }
        // An uninterpreted application is a leaf of the SAT problem: its own
        // assignment is the value the model evaluator reports for it. Whatever
        // the leaf evaluator can compute is computed, never read back.
        let (values, bools) = (&bv_model.values, &bv_model.bool_overrides);
        match terms.sort(term) {
            Sort::BitVec(sort) => {
                if Self::evaluate_bv_expr_with_bools(terms, term, values, bools, memo).is_none() {
                    if let Some(value) = values.get(&term).filter(|v| fits(v, sort.width)) {
                        memo.bv.insert(term, value.clone());
                    }
                }
            }
            Sort::Bool => {
                if Self::evaluate_bool_substitution(terms, term, values, bools, memo).is_none() {
                    if let Some(&value) = bools.get(&term) {
                        memo.boolean.insert(term, value);
                    }
                }
            }
            _ => {}
        }
    }

    /// Whether `name(args)` is an uninterpreted application over BV/Bool
    /// arguments. A cached value of an INTERPRETED operator is exactly the
    /// dead node #store-chain-dead-node forbids (the gate recomputes the
    /// operator from its arguments), so a doubtful name is never seeded: no
    /// theory registry may know it (the pair `flatten_reads/transport.rs`
    /// consults, since each misses operators the other lists), it may not be
    /// spelled like a theory operator either misses (`bvsaddo`, `bvredor`,
    /// `ext_rotate_left`, `nat2bv`, ...), and an internal name counts only as a
    /// registered user declaration.
    fn is_uninterpreted_operand_application(
        terms: &TermStore,
        name: &str,
        args: &[TermId],
    ) -> bool {
        const THEORY_PREFIXES: [&str; 9] = [
            "bv", "ext_", "fp.", "str.", "re.", "seq.", "int.", "set.", "char.",
        ];
        if args.is_empty()
            || !args
                .iter()
                .all(|&arg| matches!(terms.sort(arg), Sort::BitVec(_) | Sort::Bool))
        {
            return false;
        }
        if name.starts_with('@') || name.starts_with("__ay") || name.starts_with("!ay.") {
            return terms.is_declared_function(name);
        }
        !Self::is_known_theory_symbol(name)
            && !crate::features::is_builtin_symbol_name(name)
            && !THEORY_PREFIXES
                .iter()
                .any(|prefix| name.starts_with(prefix))
            && !["2bv", "2nat", "2int"]
                .iter()
                .any(|conversion| name.contains(conversion))
    }

    /// `array`'s interpretation at `index`'s value, for an array variable
    /// resolved exactly like a store-chain base: a withheld variable refuses,
    /// a free one receives its one published default first.
    pub(super) fn definition_operand_read_value(
        terms: &TermStore,
        bv_model: &BvModel,
        array: TermId,
        index: TermId,
        array_model: &mut ArrayModel,
        memo: &mut BvEvalMemo,
    ) -> Option<String> {
        if !matches!(terms.get(array), TermData::Var(_, _)) {
            return None;
        }
        let Sort::Array(sort) = terms.sort(array) else {
            return None;
        };
        let Sort::BitVec(index_sort) = &sort.index_sort else {
            return None;
        };
        let index_value = Self::store_chain_operand_value(terms, bv_model, index, memo)?;
        let interp = Self::resolve_substitution_target_interp(terms, bv_model, array, array_model)?;
        let key = format_bitvec(&index_value, index_sort.width);
        interp
            .stores
            .iter()
            .find(|(cell, _)| *cell == key)
            .map(|(_, value)| value.clone())
            .or(interp.default)
    }

    /// Read back a BV cell the interpretation builders wrote with
    /// [`format_bitvec`]; anything else is not a BV cell.
    fn parse_interpretation_bitvec(cell: &str) -> Option<BigInt> {
        if let Some(hex) = cell.strip_prefix("#x") {
            BigInt::parse_bytes(hex.as_bytes(), 16)
        } else if let Some(bin) = cell.strip_prefix("#b") {
            BigInt::parse_bytes(bin.as_bytes(), 2)
        } else {
            None
        }
    }
}
