// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Congruence diagonalization (Gram--Schmidt / completing squares), retaining
//! the original-coordinate basis. See Voight, Quaternion Algebras, ch. 4,
//! https://doi.org/10.1007/978-3-030-56694-4_4 . Binary forms reuse conic.rs.
//! These are model proposals, never contradiction certificates.
use super::super::{Polynomial, Ring};

struct Form {
    // Polynomial coefficients in the upper triangle on input; an actual
    // symmetric matrix after division of off-diagonal coefficients by two.
    quadratic: Vec<Vec<u32>>,
    linear: Vec<u32>,
    constant: u32,
}

impl Ring<'_, '_> {
    fn quadric_add(&mut self, a: u32, b: u32) -> Option<u32> {
        self.pay(1, 0)?;
        Some(self.sum(a, b))
    }
    fn quadric_sub(&mut self, a: u32, b: u32) -> Option<u32> {
        self.pay(1, 0)?;
        Some(self.sum(a, if b == 0 { 0 } else { self.field.modulus() - b }))
    }
    fn quadric_zeroes(&mut self, n: usize) -> Option<Vec<u32>> {
        let mut out = Vec::new();
        self.reserve(&mut out, n)?;
        self.pay(n, 0)?;
        out.resize(n, 0);
        Some(out)
    }
    fn quadric_matrix(&mut self, n: usize) -> Option<Vec<Vec<u32>>> {
        n.checked_mul(n)?;
        let mut out = Vec::new();
        self.reserve(&mut out, n)?;
        for _ in 0..n {
            self.pay(1, 0)?;
            out.push(self.quadric_zeroes(n)?);
        }
        Some(out)
    }
    fn quadric_point(&mut self, variable: usize, mut form: Form) -> Option<Option<Vec<u32>>> {
        let n = form.linear.len();
        self.pay(n, 0)?;
        if n == 0 || form.quadratic.len() != n || form.constant >= self.field.modulus() {
            return None;
        }
        for (i, row) in form.quadratic.iter().enumerate() {
            self.pay(n, 0)?;
            if row.len() != n
                || form.linear[i] >= self.field.modulus()
                || row
                    .iter()
                    .enumerate()
                    .any(|(j, &value)| value >= self.field.modulus() || (j < i && value != 0))
            {
                return None;
            }
        }
        let mut point = self.quadric_zeroes(n)?;
        if self.field.modulus() == 2 {
            // A Boolean quadratic function is determined by its square-free
            // coefficients. A nonzero linear coefficient certifies a unit
            // vector; otherwise a cross coefficient certifies its two units.
            if form.constant == 0 {
                return Some(Some(point));
            }
            for i in 0..n {
                let linear = self.quadric_add(form.linear[i], form.quadratic[i][i])?;
                if linear != 0 {
                    point[i] = 1;
                    return Some(Some(point));
                }
            }
            for i in 0..n {
                for j in i + 1..n {
                    self.pay(1, 0)?;
                    if form.quadratic[i][j] != 0 {
                        point[i] = 1;
                        point[j] = 1;
                        return Some(Some(point));
                    }
                }
            }
            return Some(None);
        }
        let half = self.inverse(2)?;
        for i in 0..n {
            for j in i + 1..n {
                let coefficient = self.product(form.quadratic[i][j], half)?;
                form.quadratic[i][j] = coefficient;
                form.quadratic[j][i] = coefficient;
            }
        }
        let mut basis = self.quadric_matrix(n)?;
        for (i, row) in basis.iter_mut().enumerate() {
            self.pay(1, 0)?;
            row[i] = 1;
        }
        let mut rank = 0;
        for column in 0..n {
            self.pay(1, 0)?;
            let mut pivot = None;
            for i in column..n {
                self.pay(1, 0)?;
                if form.quadratic[i][i] != 0 {
                    pivot = Some(i);
                    break;
                }
            }
            if pivot.is_none() {
                let mut pair = None;
                'cross: for i in column..n {
                    for j in i + 1..n {
                        self.pay(1, 0)?;
                        if form.quadratic[i][j] != 0 {
                            pair = Some((i, j));
                            break 'cross;
                        }
                    }
                }
                let Some((i, j)) = pair else {
                    break;
                };
                // Replace basis vector e_i by e_i+e_j. With zero diagonal,
                // its norm is 2*A_ij != 0 in odd characteristic.
                let diagonal = self.product(2, form.quadratic[i][j])?;
                for row in 0..n {
                    self.pay(1, 0)?;
                    if row != i {
                        let value =
                            self.quadric_add(form.quadratic[row][i], form.quadratic[row][j])?;
                        form.quadratic[row][i] = value;
                        form.quadratic[i][row] = value;
                    }
                    basis[row][i] = self.quadric_add(basis[row][i], basis[row][j])?;
                }
                form.quadratic[i][i] = diagonal;
                form.linear[i] = self.quadric_add(form.linear[i], form.linear[j])?;
                pivot = Some(i);
            }
            let pivot = pivot?;
            form.quadratic.swap(column, pivot);
            form.linear.swap(column, pivot);
            for row in &mut form.quadratic {
                self.pay(1, 0)?;
                row.swap(column, pivot);
            }
            for row in &mut basis {
                self.pay(1, 0)?;
                row.swap(column, pivot);
            }
            let inverse = self.inverse(form.quadratic[column][column])?;
            let mut factors = self.quadric_zeroes(n - column - 1)?;
            for j in column + 1..n {
                factors[j - column - 1] = self.product(form.quadratic[column][j], inverse)?;
            }
            // The Schur complement and the SAME congruence on the linear
            // term/original-coordinate basis, not a fresh specialized system.
            for j in column + 1..n {
                for k in j..n {
                    let correction =
                        self.product(factors[j - column - 1], form.quadratic[column][k])?;
                    let value = self.quadric_sub(form.quadratic[j][k], correction)?;
                    form.quadratic[j][k] = value;
                    form.quadratic[k][j] = value;
                }
                let correction = self.product(factors[j - column - 1], form.linear[column])?;
                form.linear[j] = self.quadric_sub(form.linear[j], correction)?;
                for row in &mut basis {
                    let correction = self.product(factors[j - column - 1], row[column])?;
                    row[j] = self.quadric_sub(row[j], correction)?;
                }
                form.quadratic[column][j] = 0;
                form.quadratic[j][column] = 0;
            }
            rank = column + 1;
        }
        let mut linear_coordinate = None;
        for i in rank..n {
            self.pay(1, 0)?;
            if form.linear[i] != 0 {
                linear_coordinate = Some(i);
                break;
            }
        }
        if let Some(i) = linear_coordinate {
            let inverse = self.inverse(form.linear[i])?;
            let negative = self.quadric_sub(0, form.constant)?;
            point[i] = self.product(negative, inverse)?;
        } else if rank == 0 {
            if form.constant != 0 {
                return Some(None);
            }
        } else {
            // Rank>=2 binary forms represent every target. Other diagonal
            // coordinates may be zero by that theorem, not by point trials.
            let second = if rank >= 2 { form.quadratic[1][1] } else { 0 };
            let linear = if rank >= 2 { form.linear[1] } else { 0 };
            let Some([first, second]) = self.conic_point(
                variable,
                [
                    form.quadratic[0][0],
                    0,
                    second,
                    form.linear[0],
                    linear,
                    form.constant,
                ],
            )?
            else {
                return Some(None);
            };
            point[0] = first;
            if rank >= 2 {
                point[1] = second;
            }
        }
        let mut original = self.quadric_zeroes(n)?;
        for (i, row) in basis.iter().enumerate() {
            for (&coefficient, &value) in row.iter().zip(&point) {
                let term = self.product(coefficient, value)?;
                original[i] = self.quadric_add(original[i], term)?;
            }
        }
        Some(Some(original))
    }
}

pub(super) fn construct(
    ring: &mut Ring<'_, '_>,
    basis: &[Polynomial],
    values: &[Option<u32>],
) -> Option<Option<Vec<Option<u32>>>> {
    let mut variables = Vec::new();
    let mut positions = Vec::new();
    ring.reserve(&mut positions, values.len())?;
    for (index, value) in values.iter().enumerate() {
        ring.pay(1, 0)?;
        if value.is_none() {
            positions.push(Some(variables.len()));
            ring.reserve(&mut variables, 1)?;
            variables.push(index);
        } else {
            positions.push(None);
        }
    }
    let n = variables.len();
    if n < 3 {
        return Some(None);
    }
    'rows: for original in basis {
        let row = ring.substitute(original, values)?;
        // Refuse higher degree BEFORE allocating a dense quadratic matrix.
        // This avoids consuming its storage on an unrelated unsupported row.
        for term in &row {
            let mut degree = 0u32;
            for &power in &term.exponents {
                ring.pay(1, 0)?;
                if power > 2 || degree > 2 - power {
                    continue 'rows;
                }
                degree += power;
            }
        }
        let mut form = Form {
            quadratic: ring.quadric_matrix(n)?,
            linear: ring.quadric_zeroes(n)?,
            constant: 0,
        };
        for term in row {
            let mut indices = [0usize; 2];
            let mut degree = 0usize;
            for (index, &power) in term.exponents.iter().enumerate() {
                ring.pay(1, 0)?;
                if power > 2 {
                    continue 'rows;
                }
                for _ in 0..power {
                    ring.pay(1, 0)?;
                    let Some(at) = indices.get_mut(degree) else {
                        continue 'rows;
                    };
                    *at = positions[index]?;
                    degree += 1;
                }
            }
            match degree {
                0 => form.constant = ring.quadric_add(form.constant, term.coefficient)?,
                1 => {
                    form.linear[indices[0]] =
                        ring.quadric_add(form.linear[indices[0]], term.coefficient)?
                }
                2 => {
                    let [i, j] = indices;
                    form.quadratic[i][j] =
                        ring.quadric_add(form.quadratic[i][j], term.coefficient)?;
                }
                _ => return None,
            }
        }
        let Some(point) = ring.quadric_point(variables[0], form)? else {
            continue;
        };
        let mut completed = Vec::new();
        ring.reserve(&mut completed, values.len())?;
        ring.pay(values.len(), 0)?;
        completed.extend_from_slice(values);
        for (index, &value) in variables.iter().zip(&point) {
            ring.pay(1, 0)?;
            completed[*index] = Some(value);
        }
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

    #[test]
    fn quadric_closes_the_actual_prior_model_stage_refusal() {
        let mut terms = TermStore::new();
        let field = FiniteFieldSort::new(65537).unwrap();
        let variables: Vec<_> = (0..3)
            .map(|i| terms.mk_var(&format!("x{i}"), Sort::FiniteField(field)))
            .collect();
        let mut fuel = 1_000_000;
        let mut ring = Ring {
            terms: &terms,
            variables,
            field,
            fuel: &mut fuel,
            control: &mut |_, _| true,
        };
        let mut row = Vec::new();
        for i in 0..3 {
            let mut powers = ring.zero_exponents().unwrap();
            powers[i] = 2;
            ring.add_summand(&mut row, &powers, 1).unwrap();
        }
        let powers = ring.zero_exponents().unwrap();
        ring.add_summand(&mut row, &powers, 65534).unwrap();
        let basis = vec![row];
        let values = [None; 3];
        assert!(matches!(
            ring.equation(&basis, &values),
            Some(super::super::Equation::Unsupported)
        ));
        assert!(
            super::super::parametric::construct(&mut ring, &basis, &values)
                .unwrap()
                .is_none()
        );
        assert!(super::super::conic::construct(&mut ring, &basis, &values)
            .unwrap()
            .is_none());
        let completed = construct(&mut ring, &basis, &values).unwrap().unwrap();
        assert!(ring.satisfies(&basis, &completed).unwrap());
    }

    fn form(c: [u32; 10]) -> Form {
        Form {
            quadratic: vec![
                vec![c[0], c[1], c[2]],
                vec![0, c[3], c[4]],
                vec![0, 0, c[5]],
            ],
            linear: c[6..9].to_vec(),
            constant: c[9],
        }
    }
    fn evaluate(c: [u32; 10], x: u32, y: u32, z: u32, p: u32) -> u32 {
        let c = c.map(u64::from);
        let (x, y, z) = (u64::from(x), u64::from(y), u64::from(z));
        ((c[0] * x * x
            + c[1] * x * y
            + c[2] * x * z
            + c[3] * y * y
            + c[4] * y * z
            + c[5] * z * z
            + c[6] * x
            + c[7] * y
            + c[8] * z
            + c[9])
            % u64::from(p)) as u32
    }
    #[test]
    fn quadric_three_variable_points_match_all_small_field_coefficients() {
        for p in [2u32, 3] {
            let mut terms = TermStore::new();
            let field = FiniteFieldSort::new(p).unwrap();
            let variables: Vec<_> = (0..3)
                .map(|i| terms.mk_var(&format!("x{i}"), Sort::FiniteField(field)))
                .collect();
            for mut encoded in 0..p.pow(10) {
                let mut c = [0; 10];
                for coefficient in &mut c {
                    *coefficient = encoded % p;
                    encoded /= p;
                }
                let expected =
                    (0..p).any(|x| (0..p).any(|y| (0..p).any(|z| evaluate(c, x, y, z, p) == 0)));
                let mut fuel = 1_000_000;
                let mut ring = Ring {
                    terms: &terms,
                    variables: variables.clone(),
                    field,
                    fuel: &mut fuel,
                    control: &mut |_, _| true,
                };
                let point = ring.quadric_point(0, form(c)).unwrap();
                assert_eq!(point.is_some(), expected, "p={p}, coefficients={c:?}");
                if let Some(point) = point {
                    assert_eq!(point.len(), 3);
                    assert!(point.iter().all(|&value| value < p));
                    assert_eq!(
                        evaluate(c, point[0], point[1], point[2], p),
                        0,
                        "{c:?}, p={p}, {point:?}"
                    );
                }
            }
        }
    }
    fn rank_form(p: u32, rank: usize, target: u32) -> Form {
        let n = 4;
        let mut q = vec![vec![0; n]; n];
        let mut linear = vec![0; n];
        let mut constant = (p - target) % p;
        // Known invertible lower-triangular coordinate map, translated before
        // squaring. This independently generates every rank from zero to four.
        for row in 0..rank {
            let a = (row as u32 + 1) % p;
            let shift = (row as u32 + 2) % p;
            constant = ((u64::from(constant) + u64::from(a) * u64::from(shift) * u64::from(shift))
                % u64::from(p)) as u32;
            for i in 0..=row {
                linear[i] = ((u64::from(linear[i]) + 2 * u64::from(a) * u64::from(shift))
                    % u64::from(p)) as u32;
                for j in i..=row {
                    let multiplier = if i == j { 1 } else { 2 };
                    q[i][j] = (q[i][j] + multiplier * a) % p;
                }
            }
        }
        Form {
            quadratic: q,
            linear,
            constant,
        }
    }
    fn evaluate_form(form: &Form, point: &[u32], p: u32) -> u32 {
        let mut value = u64::from(form.constant);
        for (i, &x) in point.iter().enumerate() {
            value += u64::from(form.linear[i]) * u64::from(x);
            for (j, &y) in point.iter().enumerate().skip(i) {
                value += u64::from(form.quadratic[i][j]) * u64::from(x) * u64::from(y);
            }
        }
        (value % u64::from(p)) as u32
    }
    #[test]
    fn quadric_four_variable_translated_ranks_match_independent_assignment_truth() {
        for p in [5u32, 7] {
            let mut terms = TermStore::new();
            let field = FiniteFieldSort::new(p).unwrap();
            let variables: Vec<_> = (0..4)
                .map(|i| terms.mk_var(&format!("x{i}"), Sort::FiniteField(field)))
                .collect();
            for rank in 0..=4 {
                for target in 0..p {
                    let original = rank_form(p, rank, target);
                    let expected = (0..p.pow(4)).any(|mut encoded| {
                        let mut point = [0; 4];
                        for value in &mut point {
                            *value = encoded % p;
                            encoded /= p;
                        }
                        evaluate_form(&original, &point, p) == 0
                    });
                    let mut fuel = 1_000_000;
                    let mut ring = Ring {
                        terms: &terms,
                        variables: variables.clone(),
                        field,
                        fuel: &mut fuel,
                        control: &mut |_, _| true,
                    };
                    let point = ring.quadric_point(0, rank_form(p, rank, target)).unwrap();
                    assert_eq!(
                        point.is_some(),
                        expected,
                        "p={p},rank={rank},target={target}"
                    );
                    if let Some(point) = point {
                        assert_eq!(evaluate_form(&original, &point, p), 0);
                    }
                }
            }
        }
    }
    #[test]
    fn quadric_diagonalization_retains_original_stop_memory_and_fresh_request() {
        let mut terms = TermStore::new();
        let field = FiniteFieldSort::new(65537).unwrap();
        let variables: Vec<_> = (0..4)
            .map(|i| terms.mk_var(&format!("x{i}"), Sort::FiniteField(field)))
            .collect();
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
                variables: variables.clone(),
                field,
                fuel: &mut fuel,
                control: &mut control,
            };
            assert!(ring
                .quadric_point(0, rank_form(65537, 4, 3))
                .unwrap()
                .is_some());
        }
        let mut calls = 0usize;
        let mut fuel = 1_000_000;
        let mut control = |_, _| {
            calls += 1;
            calls < total / 2
        };
        let mut ring = Ring {
            terms: &terms,
            variables: variables.clone(),
            field,
            fuel: &mut fuel,
            control: &mut control,
        };
        assert!(ring.quadric_point(0, rank_form(65537, 4, 3)).is_none());
        assert_eq!(*ring.fuel, 0);
        drop(ring);
        let stopped = calls;
        let mut control = |_, _| {
            calls += 1;
            true
        };
        let mut ring = Ring {
            terms: &terms,
            variables: variables.clone(),
            field,
            fuel: &mut fuel,
            control: &mut control,
        };
        assert!(ring.quadric_point(0, rank_form(65537, 4, 3)).is_none());
        drop(ring);
        assert_eq!(calls, stopped);
        let mut used = 0usize;
        let mut fuel = 1_000_000;
        let mut control = |_, extra| {
            used += extra;
            used < bytes / 2
        };
        let mut ring = Ring {
            terms: &terms,
            variables: variables.clone(),
            field,
            fuel: &mut fuel,
            control: &mut control,
        };
        assert!(ring.quadric_point(0, rank_form(65537, 4, 3)).is_none());
        assert_eq!(*ring.fuel, 0);
        drop(ring);
        let mut fuel = 1_000_000;
        let mut ring = Ring {
            terms: &terms,
            variables,
            field,
            fuel: &mut fuel,
            control: &mut |_, _| true,
        };
        assert!(ring
            .quadric_point(0, rank_form(65537, 4, 3))
            .unwrap()
            .is_some());
    }
}
