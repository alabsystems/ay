// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Lexical scalar typing and streaming canonical output, without substitution.
//! Every let RHS sees the old scope; unique generated slots prevent capture.

use super::*;

struct Binding<'a> {
    name: &'a str,
    sort: Scalar,
    slot: usize,
}

struct Writer<'a, 'b> {
    environment: Vec<Binding<'a>>,
    next_slot: usize,
    budget: &'b mut Budget,
}

pub(super) fn definition(
    name: &str,
    parameters: &SExpr,
    expected: &[Sort],
    body: &SExpr,
    result: Scalar,
    budget: &mut Budget,
) -> Option<String> {
    let parameters = parameters.as_list()?;
    if parameters.len() != expected.len() {
        return None;
    }
    budget.charge(parameters.len(), parameters.len().checked_mul(128)?)?;
    let mut writer = Writer {
        environment: Vec::new(),
        next_slot: 0,
        budget,
    };
    writer
        .environment
        .try_reserve_exact(parameters.len())
        .ok()?;
    let mut text = String::new();
    writer.budget.push(&mut text, "(define-fun ")?;
    writer.budget.symbol(&mut text, name)?;
    writer.budget.push(&mut text, " (")?;
    for (parameter, expected) in parameters.iter().zip(expected) {
        let [name, sort] = parameter.as_list()? else {
            return None;
        };
        let name = name.as_symbol()?;
        writer.budget.name(name)?;
        let sort = Scalar::parse(sort)?;
        if sort != Scalar::from_sort(expected)? || writer.lookup(name)?.is_some() {
            return None;
        }
        let slot = writer.next()?;
        if slot != 0 {
            writer.budget.push(&mut text, " ")?;
        }
        writer.budget.push(&mut text, "(")?;
        writer.budget.local(&mut text, slot)?;
        writer.budget.push(&mut text, " ")?;
        writer.budget.sort_text(&mut text, sort)?;
        writer.budget.push(&mut text, ")")?;
        writer.environment.push(Binding { name, sort, slot });
    }
    writer.budget.push(&mut text, ") ")?;
    writer.budget.sort_text(&mut text, result)?;
    writer.budget.push(&mut text, " ")?;
    if writer.expression(body, 0, &mut text)? != result {
        return None;
    }
    writer.budget.push(&mut text, ")")?;
    drop(writer);
    budget.charge(1, 0)?;
    Some(text)
}

impl<'a> Writer<'a, '_> {
    fn next(&mut self) -> Option<usize> {
        let current = self.next_slot;
        self.next_slot = current.checked_add(1)?;
        Some(current)
    }

    fn lookup(&mut self, name: &str) -> Option<Option<(Scalar, usize)>> {
        for binding in self.environment.iter().rev() {
            self.budget
                .charge(name.len().min(binding.name.len()).checked_add(1)?, 0)?;
            if binding.name == name {
                return Some(Some((binding.sort, binding.slot)));
            }
        }
        Some(None)
    }

    fn expression(
        &mut self,
        expression: &'a SExpr,
        depth: usize,
        text: &mut String,
    ) -> Option<Scalar> {
        self.budget.charge(1, 0)?;
        if depth > MAX_DEPTH {
            return None;
        }
        if let Some(sort) = self.literal(expression, text)? {
            return Some(sort);
        }
        if let SExpr::Symbol(name) = expression {
            self.budget.name(name)?;
            let (sort, slot) = self.lookup(name)??;
            self.budget.local(text, slot)?;
            return Some(sort);
        }
        let [head, arguments @ ..] = expression.as_list()? else {
            return None;
        };
        if head.is_symbol("let") {
            return self.let_expression(arguments, depth, text);
        }
        self.budget.charge(
            arguments.len(),
            arguments.len().checked_mul(size_of::<Scalar>())?,
        )?;
        let mut sorts = Vec::new();
        sorts.try_reserve_exact(arguments.len()).ok()?;
        self.budget.push(text, "(")?;
        operations::write_head(head, self.budget, text)?;
        for argument in arguments {
            self.budget.push(text, " ")?;
            sorts.push(self.expression(argument, depth + 1, text)?);
        }
        let result = operations::result(head, &sorts)?;
        self.budget.scalar(result)?;
        self.budget.push(text, ")")?;
        Some(result)
    }

    fn literal(&mut self, expression: &SExpr, text: &mut String) -> Option<Option<Scalar>> {
        let (sort, digits, decimal) = match expression {
            SExpr::True => {
                self.budget.push(text, "true")?;
                return Some(Some(Scalar::Bool));
            }
            SExpr::False => {
                self.budget.push(text, "false")?;
                return Some(Some(Scalar::Bool));
            }
            SExpr::Hexadecimal(digits) => (
                Scalar::Bv(
                    u32::try_from(digits.strip_prefix("#x").unwrap_or(digits).len())
                        .ok()?
                        .checked_mul(4)?,
                ),
                digits.len(),
                false,
            ),
            SExpr::Binary(digits) => (
                Scalar::Bv(u32::try_from(digits.strip_prefix("#b").unwrap_or(digits).len()).ok()?),
                digits.len(),
                false,
            ),
            SExpr::List(items) if items.first().is_some_and(|head| head.is_symbol("_")) => {
                let [_, value, width] = items.as_slice() else {
                    return None;
                };
                let digits = value.as_symbol()?.strip_prefix("bv")?;
                (Scalar::Bv(natural(width)?), digits.len(), true)
            }
            _ => return Some(None),
        };
        let Scalar::Bv(width) = sort else {
            return None;
        };
        if !(1..=crate::api::MAX_API_BITVECTOR_WIDTH).contains(&width) {
            return None;
        }
        let width_bytes = usize::try_from(width).ok()?;
        // Decimal conversion can do repeated multi-limb arithmetic. Charge a
        // conservative digit/limb product before calling the numeric library.
        let work = if decimal {
            digits.checked_mul(width_bytes.div_ceil(64).max(1))?
        } else {
            digits
        };
        self.budget.charge(
            work.checked_add(1)?,
            width_bytes
                .checked_mul(4)?
                .checked_add(digits.checked_mul(4)?)?
                .checked_add(256)?,
        )?;
        let ModelValue::BitVec {
            value,
            width: decoded,
        } = self.budget.literals.decode(expression, &sort.core())?
        else {
            return None;
        };
        if decoded != width {
            return None;
        }
        // The strict decoder has already rejected negative/out-of-range values.
        // Do not use the normal printer's modular reduction to repair them.
        let (radix, count, prefix) = if width.is_multiple_of(4) {
            (16, width_bytes / 4, "#x")
        } else {
            (2, width_bytes, "#b")
        };
        let digits = value.to_str_radix(radix);
        if digits.len() > count {
            return None;
        }
        self.budget.push(text, prefix)?;
        for _ in digits.len()..count {
            self.budget.push(text, "0")?;
        }
        self.budget.push(text, &digits)?;
        Some(Some(sort))
    }

    fn let_expression(
        &mut self,
        arguments: &'a [SExpr],
        depth: usize,
        text: &mut String,
    ) -> Option<Scalar> {
        let [bindings, body] = arguments else {
            return None;
        };
        let bindings = bindings.as_list()?;
        if bindings.is_empty() {
            return None;
        }
        self.budget
            .charge(bindings.len(), bindings.len().checked_mul(256)?)?;
        let mut pending: Vec<Binding<'a>> = Vec::new();
        pending.try_reserve_exact(bindings.len()).ok()?;
        self.budget.push(text, "(let (")?;
        for (index, binding) in bindings.iter().enumerate() {
            let [name, rhs] = binding.as_list()? else {
                return None;
            };
            let name = name.as_symbol()?;
            self.budget.name(name)?;
            for previous in &pending {
                self.budget
                    .charge(name.len().min(previous.name.len()).checked_add(1)?, 0)?;
                if previous.name == name {
                    return None;
                }
            }
            let slot = self.next()?;
            if index != 0 {
                self.budget.push(text, " ")?;
            }
            self.budget.push(text, "(")?;
            self.budget.local(text, slot)?;
            self.budget.push(text, " ")?;
            let sort = self.expression(rhs, depth + 1, text)?;
            self.budget.push(text, ")")?;
            pending.push(Binding { name, sort, slot });
        }
        self.budget.push(text, ") ")?;
        let old = self.environment.len();
        self.environment.try_reserve_exact(pending.len()).ok()?;
        self.environment.extend(pending);
        let result = self.expression(body, depth + 1, text)?;
        self.environment.truncate(old);
        self.budget.push(text, ")")?;
        Some(result)
    }
}
