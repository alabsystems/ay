// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Odd-characteristic quadratic diagonalization and deterministic compressed
//! sums of squares (van de Woestijne, ISSAC 2005, section 6.1).
//! https://www.opt.math.tugraz.at/~cvdwoest/maths/issac2005.pdf
//! Only SAT proposals: every remaining equation and the authored model gate
//! must still succeed. No failure here licenses a contradiction theorem.
use super::super::{Polynomial, Ring};

struct Run {
    value: u32,
    count: u32,
}

impl Ring<'_, '_> {
    fn conic_add(&mut self, a: u32, b: u32) -> Option<u32> {
        self.pay(1, 0)?;
        Some(self.sum(a, b))
    }
    fn conic_neg(&mut self, a: u32) -> Option<u32> {
        self.pay(1, 0)?;
        Some(if a == 0 { 0 } else { self.field.modulus() - a })
    }
    fn conic_sub(&mut self, a: u32, b: u32) -> Option<u32> {
        let b = self.conic_neg(b)?;
        self.conic_add(a, b)
    }
    fn conic_div(&mut self, a: u32, b: u32) -> Option<u32> {
        let inverse = self.inverse(b)?;
        self.product(a, inverse)
    }
    fn conic_sqrt(&mut self, variable: usize, value: u32) -> Option<Option<u32>> {
        let constant = self.conic_neg(value)?;
        let mut polynomial = Vec::new();
        self.reserve(&mut polynomial, 3)?;
        self.pay(3, 0)?;
        polynomial.extend_from_slice(&[constant, 0, 1]);
        Some(
            self.root_choice(variable, polynomial)?
                .map(|root| root.value),
        )
    }
    fn conic_prefix(&mut self, runs: &[Run], count: u32) -> Option<u32> {
        let mut left = count;
        let mut sum = 0;
        for run in runs {
            self.pay(1, 0)?;
            let take = left.min(run.count);
            let square = self.product(run.value, run.value)?;
            let part = self.product(square, take)?;
            sum = self.conic_add(sum, part)?;
            left -= take;
            if left == 0 {
                return Some(sum);
            }
        }
        None
    }
    fn conic_keep(&mut self, out: &mut Vec<Run>, value: u32, count: u32) -> Option<()> {
        self.pay(1, 0)?;
        if count != 0 {
            self.reserve(out, 1)?;
            out.push(Run { value, count });
        }
        Some(())
    }
    fn conic_squares(&mut self, variable: usize, value: u32) -> Option<[u32; 2]> {
        self.pay(1, 0)?;
        if value == 0 {
            return Some([0, 0]);
        }
        // A compressed representation of value copies of 1², not value
        // entries. Every reduction removes at least one roughly-third block.
        let mut runs = Vec::new();
        self.conic_keep(&mut runs, 1, value)?;
        let mut total = value;
        while total >= 3 {
            self.pay(1, 0)?;
            let cuts = [total / 3, ((u64::from(total) * 2) / 3) as u32, total];
            let mut sums = [0; 3];
            for (sum, &cut) in sums.iter_mut().zip(&cuts) {
                *sum = self.conic_prefix(&runs, cut)?;
            }
            let mut reduction = None;
            for (index, &sum) in sums.iter().enumerate() {
                self.pay(1, 0)?;
                if sum == 0 {
                    reduction = Some((0, cuts[index], 1));
                    break;
                }
            }
            if reduction.is_none() {
                'pairs: for high in 1..3 {
                    for low in 0..high {
                        self.pay(1, 0)?;
                        let quotient = self.conic_div(sums[high], sums[low])?;
                        if let Some(scale) = self.conic_sqrt(variable, quotient)? {
                            reduction = Some((cuts[low], cuts[high], scale));
                            break 'pairs;
                        }
                    }
                }
            }
            // Three nonzero prefix sums occupy only two square classes.
            // Failure of this invariant is refusal, never a model guess.
            let (before, through, scale) = reduction?;
            let mut next = Vec::new();
            let mut start = 0u32;
            for run in runs {
                self.pay(1, 0)?;
                let end = start.checked_add(run.count)?;
                let prefix = end.min(before).saturating_sub(start);
                if prefix != 0 {
                    let value = self.product(run.value, scale)?;
                    self.conic_keep(&mut next, value, prefix)?;
                }
                let suffix = end.saturating_sub(start.max(through));
                self.conic_keep(&mut next, run.value, suffix)?;
                start = end;
            }
            total = total.checked_sub(through.checked_sub(before)?)?;
            runs = next;
        }
        let mut result = [0; 2];
        let mut at = 0usize;
        for run in runs {
            self.pay(1, 0)?;
            // This final expansion contains at most TWO scalars.
            for _ in 0..run.count {
                self.pay(1, 0)?;
                *result.get_mut(at)? = run.value;
                at += 1;
            }
        }
        let first = self.product(result[0], result[0])?;
        let second = self.product(result[1], result[1])?;
        (self.conic_add(first, second)? == value).then_some(result)
    }
    fn conic_diagonal(&mut self, variable: usize, a: u32, b: u32, value: u32) -> Option<[u32; 2]> {
        self.pay(1, 0)?;
        if value == 0 {
            return Some([0, 0]);
        }
        let target = self.conic_div(value, a)?;
        if let Some(root) = self.conic_sqrt(variable, target)? {
            return Some([root, 0]);
        }
        let other = self.conic_div(value, b)?;
        if let Some(root) = self.conic_sqrt(variable, other)? {
            return Some([0, root]);
        }
        let ratio = self.conic_div(b, a)?;
        let negative = self.conic_neg(ratio)?;
        if let Some(root) = self.conic_sqrt(variable, negative)? {
            // (u+r*v)(u-r*v)=target; choose factors target and 1.
            let numerator = self.conic_add(target, 1)?;
            let u = self.conic_div(numerator, 2)?;
            let numerator = self.conic_sub(target, 1)?;
            let denominator = self.product(2, root)?;
            let v = self.conic_div(numerator, denominator)?;
            return Some([u, v]);
        }
        // The remaining square-class case has -1 nonsquare and b/a square.
        // Reduce to a sum of two squares, using compressed prefix reduction.
        let scale = self.conic_sqrt(variable, ratio)??;
        let [u, v] = self.conic_squares(variable, target)?;
        Some([u, self.conic_div(v, scale)?])
    }
    pub(super) fn conic_point(
        &mut self,
        variable: usize,
        mut c: [u32; 6],
    ) -> Option<Option<[u32; 2]>> {
        self.pay(1, 0)?;
        if self.field.modulus() == 2 {
            // Over the PRIME field F_2, x²=x. Solve the resulting bilinear
            // equation algebraically, including its degenerate linear cases.
            let d = self.conic_add(c[3], c[0])?;
            let e = self.conic_add(c[4], c[2])?;
            return Some(if e != 0 {
                Some([0, c[5]])
            } else if d != 0 {
                Some([c[5], 0])
            } else if c[1] != 0 {
                Some([1, c[5]])
            } else if c[5] == 0 {
                Some([0, 0])
            } else {
                None
            });
        }
        enum Coordinates {
            Original,
            Swapped,
            SumDifference,
        }
        let coordinates = if c[0] != 0 {
            Coordinates::Original
        } else if c[2] != 0 {
            c.swap(0, 2);
            c.swap(3, 4);
            Coordinates::Swapped
        } else if c[1] != 0 {
            let d = self.conic_add(c[3], c[4])?;
            let e = self.conic_sub(c[3], c[4])?;
            c = [c[1], 0, self.conic_neg(c[1])?, d, e, c[5]];
            Coordinates::SumDifference
        } else {
            let negative = self.conic_neg(c[5])?;
            return Some(if c[3] != 0 {
                Some([self.conic_div(negative, c[3])?, 0])
            } else if c[4] != 0 {
                Some([0, self.conic_div(negative, c[4])?])
            } else if c[5] == 0 {
                Some([0, 0])
            } else {
                None
            });
        };
        let [a, b, quadratic_y, d, e, constant] = c;
        let twice_a = self.product(2, a)?;
        let four_a = self.product(2, twice_a)?;
        let b_squared = self.product(b, b)?;
        let correction = self.conic_div(b_squared, four_a)?;
        let quadratic_y = self.conic_sub(quadratic_y, correction)?;
        let bd = self.product(b, d)?;
        let correction = self.conic_div(bd, twice_a)?;
        let linear_y = self.conic_sub(e, correction)?;
        let d_squared = self.product(d, d)?;
        let correction = self.conic_div(d_squared, four_a)?;
        let constant = self.conic_sub(constant, correction)?;
        let (u, y) = if quadratic_y != 0 {
            let square = self.product(linear_y, linear_y)?;
            let four_b = self.product(4 % self.field.modulus(), quadratic_y)?;
            let correction = self.conic_div(square, four_b)?;
            let target = self.conic_sub(correction, constant)?;
            let [u, v] = self.conic_diagonal(variable, a, quadratic_y, target)?;
            let twice_b = self.product(2, quadratic_y)?;
            let shift = self.conic_div(linear_y, twice_b)?;
            (u, self.conic_sub(v, shift)?)
        } else if linear_y != 0 {
            let negative = self.conic_neg(constant)?;
            (0, self.conic_div(negative, linear_y)?)
        } else {
            let negative = self.conic_neg(constant)?;
            let target = self.conic_div(negative, a)?;
            let Some(root) = self.conic_sqrt(variable, target)? else {
                return Some(None);
            };
            (root, 0)
        };
        let by = self.product(b, y)?;
        let numerator = self.conic_add(by, d)?;
        let shift = self.conic_div(numerator, twice_a)?;
        let x = self.conic_sub(u, shift)?;
        Some(Some(match coordinates {
            Coordinates::Original => [x, y],
            Coordinates::Swapped => [y, x],
            Coordinates::SumDifference => [self.conic_add(x, y)?, self.conic_sub(x, y)?],
        }))
    }
}

pub(super) fn construct(
    ring: &mut Ring<'_, '_>,
    basis: &[Polynomial],
    values: &[Option<u32>],
) -> Option<Option<Vec<Option<u32>>>> {
    let mut variables = [0; 2];
    let mut count = 0usize;
    for (index, value) in values.iter().enumerate() {
        ring.pay(1, 0)?;
        if value.is_none() {
            let Some(slot) = variables.get_mut(count) else {
                return Some(None);
            };
            *slot = index;
            count += 1;
        }
    }
    if count != 2 {
        return Some(None);
    }
    let [x, y] = variables;
    'rows: for original in basis {
        let row = ring.substitute(original, values)?;
        let mut coefficients = [0; 6];
        for term in row {
            ring.pay(term.exponents.len(), 0)?;
            if term
                .exponents
                .iter()
                .enumerate()
                .any(|(index, &power)| index != x && index != y && power != 0)
            {
                continue 'rows;
            }
            let index = match (term.exponents[x], term.exponents[y]) {
                (2, 0) => 0,
                (1, 1) => 1,
                (0, 2) => 2,
                (1, 0) => 3,
                (0, 1) => 4,
                (0, 0) => 5,
                _ => continue 'rows,
            };
            coefficients[index] = ring.conic_add(coefficients[index], term.coefficient)?;
        }
        let Some(point) = ring.conic_point(x, coefficients)? else {
            continue;
        };
        let mut completed = Vec::new();
        ring.reserve(&mut completed, values.len())?;
        ring.pay(values.len(), 0)?;
        completed.extend_from_slice(values);
        completed[x] = Some(point[0]);
        completed[y] = Some(point[1]);
        if ring.satisfies(basis, &completed)? {
            return Some(Some(completed));
        }
    }
    Some(None)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::{FiniteFieldSort, Sort, TermStore};

    fn evaluate(c: [u32; 6], x: u32, y: u32, p: u32) -> u32 {
        let [a, b, c, d, e, f] = c.map(u64::from);
        let (x, y) = (u64::from(x), u64::from(y));
        ((a * x * x + b * x * y + c * y * y + d * x + e * y + f) % u64::from(p)) as u32
    }
    #[test]
    fn conic_points_match_independent_exhaustive_small_field_truth() {
        for p in [2, 3, 5, 7] {
            let mut terms = TermStore::new();
            let field = FiniteFieldSort::new(p).unwrap();
            let x = terms.mk_var("x", Sort::FiniteField(field));
            let y = terms.mk_var("y", Sort::FiniteField(field));
            // All six coefficients for F2/F3; all quadratic parts/constants
            // plus independently selected linear terms for the larger fields.
            let linear = if p <= 3 { p } else { 2 };
            for a in 0..p {
                for b in 0..p {
                    for c in 0..p {
                        for d in 0..linear {
                            for e in 0..linear {
                                for f in 0..p {
                                    let coefficients = [a, b, c, d, e, f];
                                    let expected = (0..p).any(|x| {
                                        (0..p).any(|y| evaluate(coefficients, x, y, p) == 0)
                                    });
                                    let mut fuel = 1_000_000;
                                    let mut ring = Ring {
                                        terms: &terms,
                                        variables: vec![x, y],
                                        field,
                                        fuel: &mut fuel,
                                        control: &mut |_, _| true,
                                    };
                                    let actual = ring.conic_point(0, coefficients).unwrap();
                                    assert_eq!(
                                        actual.is_some(),
                                        expected,
                                        "p={p}, coefficients={coefficients:?}"
                                    );
                                    if let Some([x, y]) = actual {
                                        assert!(x < p && y < p);
                                        assert_eq!(
                                            evaluate(coefficients, x, y, p),
                                            0,
                                            "{coefficients:?}, p={p}, ({x},{y})"
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    #[test]
    fn conic_compressed_squares_preserve_large_and_nonsplit_domains() {
        for p in [3, 7, 31, 65537, 4294967291] {
            let mut terms = TermStore::new();
            let field = FiniteFieldSort::new(p).unwrap();
            let x = terms.mk_var("x", Sort::FiniteField(field));
            for target in [1, 2, p - 1, p / 2] {
                let mut fuel = 1_000_000;
                let mut ring = Ring {
                    terms: &terms,
                    variables: vec![x],
                    field,
                    fuel: &mut fuel,
                    control: &mut |_, _| true,
                };
                let [x, y] = ring.conic_squares(0, target).unwrap();
                assert_eq!(
                    (u128::from(x) * u128::from(x) + u128::from(y) * u128::from(y)) % u128::from(p),
                    u128::from(target)
                );
            }
        }
    }
    #[test]
    fn conic_original_refusal_during_compression_is_sticky() {
        let mut terms = TermStore::new();
        let field = FiniteFieldSort::new(65537).unwrap();
        let x = terms.mk_var("x", Sort::FiniteField(field));
        let mut total = 0usize;
        let mut bytes = 0usize;
        let mut fuel = 1_000_000;
        {
            let mut control = |_, extra| {
                total += 1;
                bytes += extra;
                true
            };
            let mut ring = Ring {
                terms: &terms,
                variables: vec![x],
                field,
                fuel: &mut fuel,
                control: &mut control,
            };
            assert!(ring.conic_squares(0, 65536).is_some());
        }
        let mut polls = 0usize;
        let mut fuel = 1_000_000;
        let mut control = |_, _| {
            polls += 1;
            polls < total / 2
        };
        let mut ring = Ring {
            terms: &terms,
            variables: vec![x],
            field,
            fuel: &mut fuel,
            control: &mut control,
        };
        assert!(ring.conic_squares(0, 65536).is_none());
        assert_eq!(*ring.fuel, 0);
        drop(ring);
        let stopped = polls;
        let mut control = |_, _| {
            polls += 1;
            true
        };
        let mut ring = Ring {
            terms: &terms,
            variables: vec![x],
            field,
            fuel: &mut fuel,
            control: &mut control,
        };
        assert!(ring.conic_squares(0, 65536).is_none());
        drop(ring);
        assert_eq!(polls, stopped);
        let mut fresh = 1_000_000;
        let mut ring = Ring {
            terms: &terms,
            variables: vec![x],
            field,
            fuel: &mut fresh,
            control: &mut |_, _| true,
        };
        assert!(ring.conic_squares(0, 65536).is_some());
        drop(ring);
        assert!(bytes > 0);
        let mut used = 0usize;
        let mut fuel = 1_000_000;
        let mut control = |_, extra| {
            used += extra;
            used < bytes / 2
        };
        let mut ring = Ring {
            terms: &terms,
            variables: vec![x],
            field,
            fuel: &mut fuel,
            control: &mut control,
        };
        assert!(ring.conic_squares(0, 65536).is_none());
        assert_eq!(*ring.fuel, 0);
    }
}
