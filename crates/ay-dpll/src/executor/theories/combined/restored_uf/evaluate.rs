// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact compound point keys over the transaction's current closure leaves.
//!
//! The callback recognizes only an admitted free UF occurrence or Var. Cached
//! compound values from EUF/LIA are never semantic authority for an ITE or an
//! arithmetic expression. This evaluator neither constructs terms nor calls a
//! solver/model evaluator, and every nested visit uses the caller's SAME Pay.

use ay_core::{Constant, Sort, Symbol, TermData, TermId};
use ay_frontend::Context;
use num_bigint::BigInt;

use super::{charge, entries, integer_bytes, same_sort, total, Atom, Checked, Pay, Probe, Refusal};

#[cfg(test)]
type Leaf<'a> = dyn FnMut(TermId, &mut Pay<'_>) -> Checked<Option<Atom>> + 'a;

pub(super) enum Resolution {
    Value(Atom),
    Alias(TermId),
}
type Resolver<'a> = dyn FnMut(TermId, &mut Pay<'_>) -> Checked<Option<Resolution>> + 'a;

#[cfg(test)]
pub(super) fn value(
    ctx: &Context,
    term: TermId,
    leaf: &mut Leaf<'_>,
    pay: &mut Pay<'_>,
) -> Checked<Atom> {
    value_observed(ctx, term, leaf, pay, &Probe::new(false))
}

#[cfg(test)]
pub(super) fn value_observed(
    ctx: &Context,
    term: TermId,
    leaf: &mut Leaf<'_>,
    pay: &mut Pay<'_>,
    probe: &Probe,
) -> Checked<Atom> {
    let mut resolver = |term, pay: &mut Pay<'_>| Ok(leaf(term, pay)?.map(Resolution::Value));
    resolved_value_observed(ctx, term, &mut resolver, pay, probe)
}

pub(super) fn resolved_value_observed(
    ctx: &Context,
    term: TermId,
    resolver: &mut Resolver<'_>,
    pay: &mut Pay<'_>,
    probe: &Probe,
) -> Checked<Atom> {
    descend(ctx, term, resolver, pay, &mut Vec::new(), probe)
}

fn sort<'a>(ctx: &'a Context, term: TermId, pay: &mut Pay<'_>) -> Checked<&'a Sort> {
    pay(1, 0)?;
    if term.index() >= ctx.terms.len() {
        return Err(Refusal::Unsupported);
    }
    Ok(ctx.terms.sort(term))
}

fn supported(ctx: &Context, sort: &Sort, pay: &mut Pay<'_>) -> Checked<bool> {
    Ok(match sort {
        Sort::Int | Sort::Bool => true,
        Sort::Uninterpreted(name) => {
            // The three registry lookups below hash the actual nominal name.
            charge(pay, &[1, name.len(), name.len(), name.len()], &[])?;
            ctx.is_model_recovery_free_carrier(name)
        }
        _ => false,
    })
}

fn typed(ctx: &Context, term: TermId, value: Atom, pay: &mut Pay<'_>) -> Checked<Atom> {
    let actual = sort(ctx, term, pay)?;
    let valid = match (&value, actual) {
        (Atom::Int(_), Sort::Int) | (Atom::Bool(_), Sort::Bool) => true,
        (Atom::Carrier(_), Sort::Uninterpreted(_)) => supported(ctx, actual, pay)?,
        _ => false,
    };
    if valid {
        Ok(value)
    } else {
        Err(Refusal::Unsupported)
    }
}

fn expect(ctx: &Context, term: TermId, expected: &Sort, pay: &mut Pay<'_>) -> Checked<()> {
    if same_sort(sort(ctx, term, pay)?, expected, pay)? {
        Ok(())
    } else {
        Err(Refusal::Unsupported)
    }
}

fn boolean(value: Atom) -> Checked<bool> {
    match value {
        Atom::Bool(value) => Ok(value),
        _ => Err(Refusal::Unsupported),
    }
}

fn integer(value: Atom) -> Checked<BigInt> {
    match value {
        Atom::Int(value) => Ok(value),
        _ => Err(Refusal::Unsupported),
    }
}

fn descend(
    ctx: &Context,
    term: TermId,
    leaf: &mut Resolver<'_>,
    pay: &mut Pay<'_>,
    active: &mut Vec<TermId>,
    probe: &Probe,
) -> Checked<Atom> {
    // Bound both malformed cycles and native recursion. The active-path scan
    // and storage admission happen before lookup/callback/recursive traversal.
    probe.check("semantic-depth-sort", Some(term), None);
    charge(pay, &[1, active.len()], &[])?;
    if active.len() >= 256 || active.contains(&term) {
        return Err(Refusal::Unsupported);
    }
    let actual = sort(ctx, term, pay)?;
    if !supported(ctx, actual, pay)? {
        return Err(Refusal::Unsupported);
    }
    entries(pay, 1)?;
    active.push(term);
    let result = node(ctx, term, leaf, pay, active, probe);
    active.pop();
    result.and_then(|value| typed(ctx, term, value, pay))
}

fn node(
    ctx: &Context,
    term: TermId,
    leaf: &mut Resolver<'_>,
    pay: &mut Pay<'_>,
    active: &mut Vec<TermId>,
    probe: &Probe,
) -> Checked<Atom> {
    // Only the owner knows the complete admitted free-function inventory.
    // A returned leaf has already paid for its owned value copy. The exact
    // result sort is checked again by descend before it can become a key.
    if let Some(value) = leaf(term, pay)? {
        return match value {
            Resolution::Value(value) => Ok(value),
            Resolution::Alias(target) => {
                // Only a captured ordinary Bool variable can be a derived
                // equation alias. Recurse inside THIS active path and meter,
                // never through a fresh evaluator or a cached compound atom.
                probe.check("boolean-alias", Some(term), Some(target));
                pay(1, 0)?;
                if !matches!(ctx.terms.get(term), TermData::Var(..)) {
                    return Err(Refusal::Unsupported);
                }
                expect(ctx, term, &Sort::Bool, pay)?;
                expect(ctx, target, &Sort::Bool, pay)?;
                descend(ctx, target, leaf, pay, active, probe)
            }
        };
    }
    probe.check("unsupported-semantic-term", Some(term), None);
    match ctx.terms.get(term) {
        TermData::Const(Constant::Int(value)) => {
            let bytes = integer_bytes(value)?;
            charge(pay, &[1, bytes], &[bytes, 64])?;
            Ok(Atom::Int(value.clone()))
        }
        TermData::Const(Constant::Bool(value)) => {
            pay(1, 0)?;
            Ok(Atom::Bool(*value))
        }
        TermData::Not(inner) => {
            expect(ctx, term, &Sort::Bool, pay)?;
            expect(ctx, *inner, &Sort::Bool, pay)?;
            Ok(Atom::Bool(!boolean(descend(
                ctx, *inner, leaf, pay, active, probe,
            )?)?))
        }
        TermData::Ite(condition, then_term, else_term) => {
            expect(ctx, *condition, &Sort::Bool, pay)?;
            let result = sort(ctx, term, pay)?;
            expect(ctx, *then_term, result, pay)?;
            expect(ctx, *else_term, result, pay)?;
            let condition = boolean(descend(ctx, *condition, leaf, pay, active, probe)?)?;
            descend(
                ctx,
                if condition { *then_term } else { *else_term },
                leaf,
                pay,
                active,
                probe,
            )
        }
        TermData::App(Symbol::Named(name), args) => {
            charge(
                pay,
                &[1, name.len(), name.len(), name.len(), name.len()],
                &[],
            )?;
            if !matches!(
                name.as_ref(),
                "and"
                    | "or"
                    | "xor"
                    | "=>"
                    | "not"
                    | "="
                    | "distinct"
                    | "+"
                    | "-"
                    | "<"
                    | "<="
                    | ">"
                    | ">="
            ) || !ctx.canonical_operator_binding_is_unambiguous(name)
            {
                return Err(Refusal::Unsupported);
            }
            // Pay each edge before operand metadata scans or value allocation.
            pay(args.len(), 0)?;
            application(ctx, term, name, args, leaf, pay, active, probe)
        }
        // Unrecognized variables, indexed operators, binders, real/BV values
        // and all unsupported interpreted operators decline the transaction.
        _ => Err(Refusal::Unsupported),
    }
}

fn application(
    ctx: &Context,
    term: TermId,
    name: &str,
    args: &[TermId],
    leaf: &mut Resolver<'_>,
    pay: &mut Pay<'_>,
    active: &mut Vec<TermId>,
    probe: &Probe,
) -> Checked<Atom> {
    match name {
        "and" | "or" => {
            expect(ctx, term, &Sort::Bool, pay)?;
            for &arg in args {
                expect(ctx, arg, &Sort::Bool, pay)?;
            }
            let identity = name == "and";
            for &arg in args {
                let value = boolean(descend(ctx, arg, leaf, pay, active, probe)?)?;
                if value != identity {
                    return Ok(Atom::Bool(value));
                }
            }
            Ok(Atom::Bool(identity))
        }
        "not" => {
            if args.len() != 1 {
                return Err(Refusal::Unsupported);
            }
            expect(ctx, term, &Sort::Bool, pay)?;
            expect(ctx, args[0], &Sort::Bool, pay)?;
            Ok(Atom::Bool(!boolean(descend(
                ctx, args[0], leaf, pay, active, probe,
            )?)?))
        }
        "xor" | "=>" => {
            if args.len() != 2 {
                return Err(Refusal::Unsupported);
            }
            expect(ctx, term, &Sort::Bool, pay)?;
            for &arg in args {
                expect(ctx, arg, &Sort::Bool, pay)?;
            }
            let left = boolean(descend(ctx, args[0], leaf, pay, active, probe)?)?;
            if name == "=>" && !left {
                return Ok(Atom::Bool(true));
            }
            let right = boolean(descend(ctx, args[1], leaf, pay, active, probe)?)?;
            Ok(Atom::Bool(if name == "xor" {
                left != right
            } else {
                !left || right
            }))
        }
        "=" | "distinct" => {
            if args.len() < 2 || (name == "=" && args.len() != 2) {
                return Err(Refusal::Unsupported);
            }
            expect(ctx, term, &Sort::Bool, pay)?;
            let argument_sort = sort(ctx, args[0], pay)?;
            if !supported(ctx, argument_sort, pay)? {
                return Err(Refusal::Unsupported);
            }
            for &arg in args {
                expect(ctx, arg, argument_sort, pay)?;
            }
            entries(pay, args.len())?;
            let mut values = Vec::new();
            for &arg in args {
                values.push(descend(ctx, arg, leaf, pay, active, probe)?);
            }
            if name == "=" {
                return Ok(Atom::Bool(values[0].same(&values[1], pay)?));
            }
            for (index, value) in values.iter().enumerate() {
                for other in &values[..index] {
                    if value.same(other, pay)? {
                        return Ok(Atom::Bool(false));
                    }
                }
            }
            Ok(Atom::Bool(true))
        }
        "+" | "-" => {
            if name == "-" && args.is_empty() {
                return Err(Refusal::Unsupported);
            }
            expect(ctx, term, &Sort::Int, pay)?;
            for &arg in args {
                expect(ctx, arg, &Sort::Int, pay)?;
            }
            charge(pay, &[1], &[64])?;
            let mut value = BigInt::from(0);
            for (index, &arg) in args.iter().enumerate() {
                let next = integer(descend(ctx, arg, leaf, pay, active, probe)?)?;
                let left_bytes = integer_bytes(&value)?;
                let right_bytes = integer_bytes(&next)?;
                // A carry/sign may add one bit. This conservative payload
                // bound also covers BigInt's sign and temporary limb storage.
                let output = total(&[left_bytes.max(right_bytes), 64])?;
                charge(pay, &[1, left_bytes, right_bytes, output], &[output])?;
                value = if name == "+" {
                    &value + &next
                } else if index == 0 && args.len() != 1 {
                    next
                } else {
                    &value - &next
                };
            }
            Ok(Atom::Int(value))
        }
        "<" | "<=" | ">" | ">=" => {
            if args.len() != 2 {
                return Err(Refusal::Unsupported);
            }
            expect(ctx, term, &Sort::Bool, pay)?;
            for &arg in args {
                expect(ctx, arg, &Sort::Int, pay)?;
            }
            let left = integer(descend(ctx, args[0], leaf, pay, active, probe)?)?;
            let right = integer(descend(ctx, args[1], leaf, pay, active, probe)?)?;
            charge(
                pay,
                &[1, integer_bytes(&left)?, integer_bytes(&right)?],
                &[],
            )?;
            Ok(Atom::Bool(match name {
                "<" => left < right,
                "<=" => left <= right,
                ">" => left > right,
                _ => left >= right,
            }))
        }
        _ => Err(Refusal::Unsupported),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::executor_types::UnknownOrigin;

    fn app(ctx: &mut Context, name: &str, args: &[TermId], sort: Sort) -> TermId {
        ctx.terms.mk_app(Symbol::named(name), args, sort)
    }

    fn pay(_: usize, _: usize) -> Result<(), UnknownOrigin> {
        Ok(())
    }

    #[test]
    fn compound_ite_and_arithmetic_keys_follow_the_current_leaf_value() {
        let mut ctx = Context::new();
        let x = ctx.terms.mk_var("x", Sort::Int);
        let one = ctx.terms.mk_int(1.into());
        let zero = ctx.terms.mk_int(0.into());
        let difference = app(&mut ctx, "-", &[x, one], Sort::Int);
        let clipped = app(&mut ctx, "<=", &[difference, zero], Sort::Bool);
        let key = ctx.terms.mk_ite_raw(clipped, zero, difference);
        for (current, expected) in [(1, 0), (4, 3), (-2, 0)] {
            let mut leaf = |term, debit: &mut Pay<'_>| -> Checked<Option<Atom>> {
                if term == x {
                    debit(1, 64)?;
                    Ok(Some(Atom::Int(current.into())))
                } else {
                    Ok(None)
                }
            };
            assert_eq!(
                value(&ctx, key, &mut leaf, &mut pay).unwrap(),
                Atom::Int(expected.into())
            );
        }
    }

    #[test]
    fn wrong_leaf_sort_and_malformed_native_operand_sorts_are_refused() {
        let mut ctx = Context::new();
        let x = ctx.terms.mk_var("x", Sort::Int);
        let truth = ctx.terms.mk_bool(true);
        let malformed = app(&mut ctx, "+", &[x, truth], Sort::Int);
        let mut wrong = |term, _: &mut Pay<'_>| -> Checked<Option<Atom>> {
            Ok((term == x).then_some(Atom::Bool(true)))
        };
        assert_eq!(
            value(&ctx, x, &mut wrong, &mut pay),
            Err(Refusal::Unsupported)
        );
        let mut absent = |_, _: &mut Pay<'_>| Ok(None);
        assert_eq!(
            value(&ctx, malformed, &mut absent, &mut pay),
            Err(Refusal::Unsupported)
        );
    }

    #[test]
    fn a_native_ordinary_binding_cannot_borrow_canonical_arithmetic_meaning() {
        let mut ctx = Context::new();
        let fake = ctx.terms.mk_var("fake_plus", Sort::Int);
        ctx.register_symbol("+".into(), fake, Sort::Int);
        assert!(!ctx.canonical_operator_binding_is_unambiguous("+"));
        let one = ctx.terms.mk_int(1.into());
        let sum = app(&mut ctx, "+", &[one, one], Sort::Int);
        let mut absent = |_, _: &mut Pay<'_>| Ok(None);
        assert_eq!(
            value(&ctx, sum, &mut absent, &mut pay),
            Err(Refusal::Unsupported)
        );
    }

    #[test]
    fn held_stop_is_observed_before_any_leaf_callback() {
        let mut ctx = Context::new();
        let x = ctx.terms.mk_var("x", Sort::Int);
        let mut called = false;
        let mut leaf = |_, _: &mut Pay<'_>| {
            called = true;
            Ok(Some(Atom::Int(0.into())))
        };
        assert_eq!(
            value(&ctx, x, &mut leaf, &mut |_, _| Err(
                UnknownOrigin::InterruptFlag
            )),
            Err(Refusal::Stopped(UnknownOrigin::InterruptFlag))
        );
        assert!(!called);
    }

    #[test]
    fn large_literal_copy_is_admitted_and_exhaustion_never_becomes_a_default() {
        let mut ctx = Context::new();
        let huge = BigInt::from(1u32) << 32_768usize;
        let literal = ctx.terms.mk_int(huge);
        let mut absent = |_, _: &mut Pay<'_>| Ok(None);
        let mut requested_large_payload = false;
        let result = value(&ctx, literal, &mut absent, &mut |_, bytes| {
            if bytes > 1024 {
                requested_large_payload = true;
                Err(UnknownOrigin::MemoryBudget)
            } else {
                Ok(())
            }
        });
        assert!(requested_large_payload);
        assert_eq!(result, Err(Refusal::Stopped(UnknownOrigin::MemoryBudget)));
    }

    #[test]
    fn malformed_cycle_and_unsupported_interpreted_operator_decline() {
        let mut ctx = Context::new();
        let one = ctx.terms.mk_int(1.into());
        let unsupported = app(&mut ctx, "*", &[one, one], Sort::Int);
        // Safe low-level term DATA can be malformed. The active-path check
        // must refuse it without recursive stack growth or default values.
        let next = TermId(u32::try_from(ctx.terms.len()).unwrap());
        let cycle = app(&mut ctx, "+", &[next, one], Sort::Int);
        assert_eq!(cycle, next);
        let mut absent = |_, _: &mut Pay<'_>| Ok(None);
        assert_eq!(
            value(&ctx, unsupported, &mut absent, &mut pay),
            Err(Refusal::Unsupported)
        );
        assert_eq!(
            value(&ctx, cycle, &mut absent, &mut pay),
            Err(Refusal::Unsupported)
        );
    }
}
