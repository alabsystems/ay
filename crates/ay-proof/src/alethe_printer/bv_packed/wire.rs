// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exhaustive, discharged Boolean cases for small-support wire operations.
//! The checker evaluates only closed constants. The producer's bit mapping
//! chooses a candidate; it supplies no trusted shift or extension rule.

use super::*;
use ay_core::Constant;
use num_traits::ToPrimitive;

const MAX_CASE_BITS: usize = 8;

/// The distinct symbolic bits of `bits` in first-seen order, or `None` past
/// [`MAX_CASE_BITS`]: each one doubles the closed cases
/// [`PackedProof::wire_operation`] discharges.
pub(super) fn case_atoms<'a>(bits: impl IntoIterator<Item = &'a String>) -> Option<Vec<String>> {
    let mut atoms: Vec<String> = Vec::new();
    for bit in bits {
        if !matches!(bit.as_str(), "true" | "false") && !atoms.contains(bit) {
            atoms.push(bit.clone());
            if atoms.len() > MAX_CASE_BITS {
                return None;
            }
        }
    }
    Some(atoms)
}

/// Whether [`PackedProof::wire_operation`] admits an operation whose input
/// and output bits together are `bits`. It decides before anything is
/// printed, so a caller can pick another lowering on `false`.
pub(super) fn admits_wire_cases(bits: &[String]) -> bool {
    case_atoms(bits).is_some()
}

struct Operation<'a> {
    name: &'a str,
    suffix: Option<&'a str>,
}

impl Operation<'_> {
    fn apply(&self, value: &str) -> String {
        match self.suffix {
            Some(suffix) => format!("({} {value} {suffix})", self.name),
            None => format!("({} {value})", self.name),
        }
    }
}

impl PackedProof<'_, '_> {
    pub(super) fn literal_shift(
        &mut self,
        op: &str,
        args: &[TermId],
        width: usize,
        depth: usize,
    ) -> Option<Value> {
        let [source, amount] = args else { return None };
        let source = self.vector(*source, depth + 1)?;
        let literal = self.vector(*amount, depth + 1)?;
        let TermData::Const(Constant::BitVec { value, .. }) = self.printer.terms.get(*amount)
        else {
            return None;
        };
        if source.bits.len() != width || literal.bits.len() != width {
            return None;
        }
        let amount = value.to_usize()?;
        // Bound the checker's closed evaluation too. Its arithmetic-shift
        // evaluator requires an amount no larger than the operand width.
        if amount > MAX_WIDTH || op == "bvashr" && amount > width {
            return None;
        }
        if op != "bvashr" || amount < width {
            return self.bitblast_literal_shift(op, source, literal, amount);
        }
        let shift = amount.min(width);
        let fill = if op == "bvashr" {
            source.bits.last()?.clone()
        } else {
            "false".into()
        };
        let bits = (0..width)
            .map(|i| {
                let index = if op == "bvshl" {
                    i.checked_sub(shift)
                } else {
                    i.checked_add(shift).filter(|&index| index < width)
                };
                index.map_or_else(|| fill.clone(), |index| source.bits[index].clone())
            })
            .collect();
        self.wire_operation(op, source, Some(&literal.equality.left), bits)
    }

    pub(super) fn wire_operation(
        &mut self,
        op: &str,
        source: Value,
        suffix: Option<&str>,
        bits: Vec<String>,
    ) -> Option<Value> {
        // Clean reads the zero extension by zero as the operand itself.
        // Congruence through that erased wrapper is therefore not a Cong
        // instance in its parsed document, even in the closed-case lane.
        // Use the existing disclosed identity and transport the earlier
        // operand derivation instead. Pinned Carcara retains its wrapper.
        if op == "(_ zero_extend 0)"
            && super::super::dialect::current() == super::super::dialect::AletheDialect::Clean
        {
            if suffix.is_some()
                || source.bits.is_empty()
                || source.bits.len() > MAX_WIDTH
                || bits != source.bits
            {
                return None;
            }
            return self.extended_vector(source, 0);
        }
        let operation = Operation { name: op, suffix };
        let atoms = case_atoms(source.bits.iter().chain(&bits))?;
        let changed = self.equality(
            &operation.apply(&source.equality.left),
            &operation.apply(&source.equality.right),
            "cong",
            &[&source.equality.step],
        )?;
        let mapped = self.evaluate_wire(&operation, &source.bits, &bits, &atoms)?;
        Some(Value {
            equality: self.chain(changed, mapped)?,
            bits,
        })
    }

    fn evaluate_wire(
        &mut self,
        operation: &Operation<'_>,
        input: &[String],
        output: &[String],
        atoms: &[String],
    ) -> Option<Equality> {
        let source = operation.apply(&bbterm(input));
        let target = bbterm(output);
        let input_name = self.define_word(input)?;
        self.define_word(output)?;
        self.spellings
            .insert(source.clone(), operation.apply(&input_name));
        if let Some((condition, remaining)) = atoms.split_first() {
            let yes = self.wire_case(operation, input, output, condition, remaining, true)?;
            let no = self.wire_case(operation, input, output, condition, remaining, false)?;
            return self.equality(&source, &target, "resolution", &[&yes, &no]);
        }
        let constant = format!(
            "#b{}",
            output
                .iter()
                .rev()
                .map(|bit| match bit.as_str() {
                    "true" => Some('1'),
                    "false" => Some('0'),
                    _ => None,
                })
                .collect::<Option<String>>()?
        );
        let left = self.equality(&source, &constant, "evaluate", &[])?;
        let right = self.equality(&target, &constant, "evaluate", &[])?;
        let reverse = self.equality(&constant, &target, "symm", &[&right.step])?;
        self.chain(left, reverse)
    }

    fn wire_case(
        &mut self,
        operation: &Operation<'_>,
        input: &[String],
        output: &[String],
        condition: &str,
        remaining: &[String],
        positive: bool,
    ) -> Option<String> {
        let end = self.fresh();
        let assumption = self.fresh();
        let literal = if positive {
            condition.into()
        } else {
            format!("(not {condition})")
        };
        let value = positive.to_string();
        self.append(&format!(
            "(anchor :step {end})\n(assume {assumption} {literal})\n"
        ))?;
        let equation = format!("(= {condition} {value})");
        let simplified = self.equality(&equation, &literal, "equiv_simplify", &[])?;
        let implication = self.step(
            &format!("{equation} (not {literal})"),
            "equiv2",
            &[&simplified.step],
        )?;
        let condition_step = self.step(&equation, "resolution", &[&implication, &assumption])?;
        let replace = |bits: &[String]| {
            bits.iter()
                .map(|bit| {
                    if bit == condition {
                        value.clone()
                    } else {
                        bit.clone()
                    }
                })
                .collect::<Vec<_>>()
        };
        let new_input = replace(input);
        let new_output = replace(output);
        let name = self.define_word(&new_input)?;
        self.define_word(&new_output)?;
        self.spellings
            .insert(operation.apply(&bbterm(&new_input)), operation.apply(&name));
        let input_eq = self.wire_substitution(input, &new_input, &condition_step)?;
        let left = self.equality(
            &operation.apply(&input_eq.left),
            &operation.apply(&input_eq.right),
            "cong",
            &[&input_eq.step],
        )?;
        let middle = self.evaluate_wire(operation, &new_input, &new_output, remaining)?;
        let output_eq = self.wire_substitution(output, &new_output, &condition_step)?;
        let right = self.equality(
            &output_eq.right,
            &output_eq.left,
            "symm",
            &[&output_eq.step],
        )?;
        let equality = self.chain(left, middle)?;
        let equality = self.chain(equality, right)?;
        self.named_step(
            &end,
            &format!(
                "(not {literal}) (= {} {})",
                self.spelling(&equality.left),
                self.spelling(&equality.right)
            ),
            "subproof",
            &[],
            &format!(" :discharge ({assumption})"),
        )?;
        Some(end)
    }

    fn wire_substitution(
        &mut self,
        old: &[String],
        new: &[String],
        condition: &str,
    ) -> Option<Equality> {
        // Alethe cong consumes one premise per changed argument, including
        // repeated occurrences. An unused condition needs no premise.
        let premises: Vec<_> = old
            .iter()
            .zip(new)
            .filter(|(a, b)| a != b)
            .map(|_| condition)
            .collect();
        let rule = if premises.is_empty() { "refl" } else { "cong" };
        self.equality(&bbterm(old), &bbterm(new), rule, &premises)
    }

    pub(super) fn bitwise(
        &mut self,
        op: &str,
        args: &[TermId],
        width: usize,
        depth: usize,
    ) -> Option<Value> {
        let [left, right] = args else { return None };
        let left = self.vector(*left, depth + 1)?;
        let right = self.vector(*right, depth + 1)?;
        if left.bits.len() != width || right.bits.len() != width {
            return None;
        }
        self.bitwise_values(op, left, right)
    }

    pub(super) fn bitwise_values(&mut self, op: &str, left: Value, right: Value) -> Option<Value> {
        if left.bits.is_empty()
            || left.bits.len() > MAX_WIDTH
            || left.bits.len() != right.bits.len()
        {
            return None;
        }
        let (gate, absorber, identity) = match op {
            "bvor" => ("or", "true", "false"),
            "bvand" => ("and", "false", "true"),
            _ => return None,
        };
        let changed = self.congruence(op, &[left.equality, right.equality])?;
        let expanded: Vec<_> = left
            .bits
            .iter()
            .zip(&right.bits)
            .map(|(left, right)| format!("({gate} {left} {right})"))
            .collect();
        let blasted = self.equality(
            &changed.right,
            &bbterm(&expanded),
            &format!("bitblast_{gate}"),
            &[],
        )?;
        let mut bits = Vec::new();
        let mut premises = Vec::new();
        for ((left, right), source) in left.bits.iter().zip(&right.bits).zip(&expanded) {
            let target = if left == absorber || right == absorber {
                absorber
            } else if left == identity {
                right
            } else if right == identity || left == right {
                left
            } else {
                source
            };
            let rule = if target == source {
                "refl".into()
            } else {
                format!("{gate}_simplify")
            };
            let survivor = target != source
                && target != absorber
                && matches!(gate, "and" | "or")
                && !matches!(target, "true" | "false");
            let step = if survivor {
                // One operand survives, and it may itself be an `and`/`or`
                // application (see `simplify_to_survivor`).
                self.simplify_to_survivor(source, target, gate, &rule)?.step
            } else {
                self.equality(source, target, &rule, &[])?.step
            };
            premises.push(step);
            bits.push(target.to_owned());
        }
        let references: Vec<_> = premises.iter().map(String::as_str).collect();
        let reduced = self.equality(&bbterm(&expanded), &bbterm(&bits), "cong", &references)?;
        let equality = self.chain(changed, blasted)?;
        Some(Value {
            equality: self.chain(equality, reduced)?,
            bits,
        })
    }
}
