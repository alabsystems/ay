// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Affine witnesses and contradictions by Gaussian elimination over a prime field.
//! Algorithm: Victor Shoup, A Computational Introduction to Number Theory and
//! Algebra, chapter 15 (Matrices over Fields), https://shoup.net/ntb/ntb-b1.pdf.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Constant, FiniteFieldSort, Sort, Symbol, TermData, TermId, TermStore};

fn pay(
    work: &mut usize,
    amount: usize,
    control: &mut dyn FnMut(usize, usize) -> bool,
    bytes: usize,
) -> Option<()> {
    let Some(remaining) = work.checked_sub(amount) else {
        // A later algorithm shares this same counter: exhausted admission is
        // terminal, never an opportunity to retry with an apparently fresh
        // remainder after a refused aggregate charge.
        *work = 0;
        return None;
    };
    *work = remaining;
    control(amount, bytes).then_some(())
}

pub(super) enum Candidate {
    Model(Vec<(TermId, u32, FiniteFieldSort)>),
    Contradiction(Vec<u32>),
}

struct Pivot {
    column: usize,
    swapped: usize,
    inverse: u32,
}

/// Fermat inversion by binary exponentiation in an authenticated prime field.
/// Each multiplication fits in u64 even when the field grows to a u32 modulus.
/// Shoup, chapter 2 (modular arithmetic and repeated squaring).
fn inverse(value: u32, field: FiniteFieldSort) -> Option<u32> {
    let modulus = u64::from(field.modulus());
    if value == 0 || u64::from(value) >= modulus {
        return None;
    }
    let mut exponent = field.modulus() - 2;
    let mut base = u64::from(value);
    let mut result = 1u64;
    while exponent != 0 {
        if exponent & 1 != 0 {
            result = result * base % modulus;
        }
        base = base * base % modulus;
        exponent >>= 1;
    }
    u32::try_from(result).ok()
}

// Canonical u32 residues need a u64 intermediate before reduction. In
// particular, reducing after a u32 product has already overflowed is unsound.
fn add(a: u32, b: u32, modulus: u32) -> u32 {
    ((u64::from(a) + u64::from(b)) % u64::from(modulus)) as u32
}

fn subtract(a: u32, b: u32, modulus: u32) -> u32 {
    ((u64::from(a) + u64::from(modulus) - u64::from(b)) % u64::from(modulus)) as u32
}

fn multiply(a: u32, b: u32, modulus: u32) -> u32 {
    (u64::from(a) * u64::from(b) % u64::from(modulus)) as u32
}

/// The caller supplies its existing cumulative work counter and retained arena.
/// A contradiction is only a candidate until the independent checker accepts it.
pub(super) fn witness_with_progress(
    terms: &TermStore,
    roots: &[TermId],
    seen: &HashSet<TermId>,
    work: &mut usize,
    control: &mut dyn FnMut(usize, usize) -> bool,
) -> Option<Candidate> {
    pay(work, seen.len(), control, 0)?;
    let edges = seen.iter().try_fold(roots.len(), |count, term| {
        if !control(0, 0) {
            return None;
        }
        count.checked_add(match terms.get(*term) {
            TermData::App(_, args) => args.len(),
            _ => 0,
        })
    })?;
    // The actual paid edge count bounds all pending entries; source arity
    // is not an independent quota. Admit copies before reserving the stack.
    let stack_capacity = edges;
    let base = seen
        .len()
        .checked_mul(256)?
        .checked_add(stack_capacity.checked_mul(size_of::<TermId>())?)?;
    pay(work, edges, control, base)?;
    let mut variables = Vec::new();
    let mut field = None;
    for &term in seen {
        pay(work, 1, control, base)?;
        if let Sort::FiniteField(f) = terms.sort(term) {
            if field.is_some_and(|prior| prior != *f) {
                return None;
            }
            field = Some(*f);
            if matches!(terms.get(term), TermData::Var(..)) {
                variables.push(term);
            }
        } else if matches!(terms.get(term), TermData::Var(..)) {
            return None;
        }
    }
    let field = field?;
    let p = field.modulus();
    let levels = variables.len().bit_width() as usize + 1;
    pay(work, variables.len().checked_mul(levels)?, control, base)?;
    variables.sort_unstable();
    let n = variables.len();
    pay(work, n, control, base)?;
    let columns = n.checked_add(1)?;
    let indices: HashMap<_, _> = variables.iter().enumerate().map(|(i, t)| (*t, i)).collect();
    let mut equations = Vec::new();
    let mut pending = Vec::with_capacity(stack_capacity);
    pending.extend_from_slice(roots);
    let mut visited = HashSet::default();
    let mut rows = 0usize;
    while let Some(term) = pending.pop() {
        pay(work, 1, control, base)?;
        if !visited.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Const(Constant::Bool(true)) => {}
            TermData::App(Symbol::Named(name), args) if name == "and" => {
                if pending.len().checked_add(args.len())? > stack_capacity {
                    return None;
                }
                pending.extend_from_slice(args)
            }
            TermData::App(Symbol::Named(name), args)
                if name == "="
                    && args.len() >= 2
                    && args
                        .iter()
                        .all(|t| terms.sort(*t) == &Sort::FiniteField(field)) =>
            {
                rows = rows.checked_add(args.len() - 1)?;
                equations.push(term);
            }
            _ => return None,
        }
    }
    // Bound all live dense affine memo rows, equations, elimination and model
    // scratch before constructing any coefficient array. This is original
    // attempt storage, not a new allowance or an allocator reservation.
    let cells = seen
        .len()
        .checked_add(rows)?
        .checked_add(4)?
        .checked_mul(columns)?;
    if cells > *work {
        return None;
    }
    let bytes = base
        .checked_add(cells.checked_mul(8)?)?
        .checked_add(rows.checked_mul(size_of::<Vec<u32>>())?)?;
    pay(work, cells, control, bytes)?;
    let mut memo = HashMap::default();
    let mut matrix = Vec::with_capacity(rows);
    // This first certificate covers direct binary authored equalities. The
    // stack visited them in reverse order. Deduplication, conjunctions and
    // n-ary expansion cannot silently change the witness's row identities.
    pay(work, equations.len(), control, bytes)?;
    let certify =
        rows == equations.len() && equations.iter().rev().copied().eq(roots.iter().copied());
    for term in equations {
        let TermData::App(_, args) = terms.get(term) else {
            return None;
        };
        let first = affine(
            terms, args[0], field, &indices, columns, &mut memo, work, control, bytes, 0,
        )?;
        for &arg in &args[1..] {
            let other = affine(
                terms, arg, field, &indices, columns, &mut memo, work, control, bytes, 0,
            )?;
            pay(work, columns, control, bytes)?;
            let mut row: Vec<_> = first
                .iter()
                .zip(other)
                .map(|(a, b)| subtract(*a, b, p))
                .collect();
            row[n] = (p - row[n]) % p;
            matrix.push(row);
        }
    }
    let mut pivots = Vec::new();
    let mut rank = 0;
    for column in 0..n {
        pay(work, matrix.len(), control, bytes)?;
        let Some(pivot) = (rank..matrix.len()).find(|&row| matrix[row][column] != 0) else {
            continue;
        };
        matrix.swap(rank, pivot);
        // At most two modular multiplications per exponent bit. Charge before
        // work, preserving the caller's cumulative budget and cancellation.
        let inverse_work = 2 * (p - 2).bit_width() as usize;
        pay(work, inverse_work.checked_add(columns)?, control, bytes)?;
        let inverse = inverse(matrix[rank][column], field)?;
        for entry in &mut matrix[rank][column..] {
            *entry = multiply(*entry, inverse, p);
        }
        for row in rank + 1..matrix.len() {
            let factor = matrix[row][column];
            if factor == 0 {
                continue;
            }
            pay(work, columns, control, bytes)?;
            // Keep the multiplier in the eliminated pivot cell. Neither
            // pivot selection nor back-substitution reads this dead entry.
            for j in column + 1..columns {
                matrix[row][j] = subtract(matrix[row][j], multiply(factor, matrix[rank][j], p), p);
            }
        }
        pivots.push(Pivot {
            column,
            swapped: pivot,
            inverse,
        });
        rank += 1;
    }
    // Every remaining coefficient is zero except the saved pivot factors.
    pay(work, matrix.len().checked_sub(rank)?, control, bytes)?;
    if let Some(conflict) = (rank..matrix.len()).find(|&row| matrix[row][n] != 0) {
        if !certify {
            return None;
        }
        // Pull a unit covector for the contradictory row back through the
        // elementary row operations. Undo later swaps on the stored rows so
        // every factor is read in the position it had at this pivot.
        let witness_bytes = bytes.checked_add(rows.checked_mul(size_of::<u32>())?)?;
        pay(work, rows, control, witness_bytes)?;
        let mut multipliers = vec![0; rows];
        multipliers[conflict] = 1;
        for (k, pivot) in pivots.iter().enumerate().rev() {
            pay(work, rows - k, control, witness_bytes)?;
            let mut weight = multipliers[k];
            for r in k + 1..rows {
                weight = subtract(
                    weight,
                    multiply(multipliers[r], matrix[r][pivot.column], p),
                    p,
                );
            }
            multipliers[k] = multiply(weight, pivot.inverse, p);
            multipliers.swap(k, pivot.swapped);
            matrix.swap(k, pivot.swapped);
        }
        multipliers[..rows].reverse();
        return Some(Candidate::Contradiction(multipliers));
    }
    let mut solution = vec![0; n];
    for row in (0..rank).rev() {
        pay(work, columns, control, bytes)?;
        let pivot = pivots[row].column;
        let mut rhs = matrix[row][n];
        for column in pivot + 1..n {
            rhs = subtract(rhs, multiply(matrix[row][column], solution[column], p), p);
        }
        solution[pivot] = rhs;
    }
    pay(work, n, control, bytes)?;
    Some(Candidate::Model(
        variables
            .into_iter()
            .zip(solution)
            .map(|(term, value)| (term, value, field))
            .collect(),
    ))
}

fn affine(
    terms: &TermStore,
    term: TermId,
    field: FiniteFieldSort,
    indices: &HashMap<TermId, usize>,
    columns: usize,
    memo: &mut HashMap<TermId, Vec<u32>>,
    work: &mut usize,
    control: &mut dyn FnMut(usize, usize) -> bool,
    bytes: usize,
    depth: usize,
) -> Option<Vec<u32>> {
    if depth > 128 || terms.sort(term) != &Sort::FiniteField(field) {
        return None;
    }
    pay(work, columns, control, bytes)?;
    if let Some(row) = memo.get(&term) {
        return Some(row.clone());
    }
    let p = field.modulus();
    let mut result = vec![0; columns];
    match terms.get(term) {
        TermData::Const(Constant::FiniteField { value, field: f }) if *f == field && *value < p => {
            result[columns - 1] = *value
        }
        TermData::Var(..) => result[*indices.get(&term)?] = 1,
        TermData::App(Symbol::Named(name), args) => {
            if (name == "ff.neg" && args.len() != 1) || (name != "ff.neg" && args.len() < 2) {
                return None;
            }
            if !matches!(name.as_str(), "ff.add" | "ff.neg" | "ff.bitsum" | "ff.mul") {
                return None;
            }
            if name == "ff.mul" {
                result[columns - 1] = 1;
            }
            let mut weight = 1;
            for &arg in args {
                let row = affine(
                    terms,
                    arg,
                    field,
                    indices,
                    columns,
                    memo,
                    work,
                    control,
                    bytes,
                    depth + 1,
                )?;
                pay(work, columns, control, bytes)?;
                if name == "ff.mul" {
                    let left_constant = result[..columns - 1].iter().all(|v| *v == 0);
                    let right_constant = row[..columns - 1].iter().all(|v| *v == 0);
                    if !left_constant && !right_constant {
                        return None;
                    }
                    if right_constant {
                        let scale = row[columns - 1];
                        for v in &mut result {
                            *v = multiply(*v, scale, p);
                        }
                    } else {
                        let scale = result[columns - 1];
                        result = row;
                        for v in &mut result {
                            *v = multiply(*v, scale, p);
                        }
                    }
                } else {
                    let scale = if name == "ff.neg" {
                        p - 1
                    } else if name == "ff.bitsum" {
                        weight
                    } else {
                        1
                    };
                    for (a, b) in result.iter_mut().zip(row) {
                        *a = add(*a, multiply(scale, b, p), p);
                    }
                }
                weight = multiply(weight, 2, p);
            }
        }
        _ => return None,
    }
    pay(work, columns, control, bytes)?;
    memo.insert(term, result.clone());
    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn modular_intermediates_preserve_full_width_residues() {
        // The largest u32 prime. These boundary operations overflow u32
        // before reduction; their expected residues follow field identities.
        let p = 4_294_967_291;
        assert_eq!(add(p - 1, p - 1, p), p - 2);
        assert_eq!(subtract(0, p - 1, p), 1);
        assert_eq!(subtract(p - 1, 0, p), p - 1);
        assert_eq!(multiply(p - 1, p - 1, p), 1);
        assert_eq!(multiply(p - 2, p - 3, p), 6);
        assert_eq!(add(p - 1, multiply(p - 1, p - 1, p), p), 0);
    }

    #[test]
    fn every_supported_nonzero_residue_has_a_checked_inverse() {
        for modulus in 2..=251 {
            let Some(field) = FiniteFieldSort::new(modulus) else {
                continue;
            };
            assert_eq!(inverse(0, field), None);
            assert_eq!(inverse(modulus, field), None);
            assert_eq!(inverse(u32::MAX, field), None);
            for value in 1..modulus {
                let result = inverse(value, field).unwrap();
                assert!(result < modulus);
                assert_eq!(u64::from(value) * u64::from(result) % u64::from(modulus), 1);
            }
        }
        for modulus in [257, 65_521, 2_147_483_647, 4_294_967_291] {
            let field = FiniteFieldSort::new(modulus).unwrap();
            for value in [1, 2, 17, modulus / 2, modulus - 2, modulus - 1] {
                let result = inverse(value, field).unwrap();
                assert!(result < modulus);
                assert_eq!(u64::from(value) * u64::from(result) % u64::from(modulus), 1);
            }
        }
    }
}
