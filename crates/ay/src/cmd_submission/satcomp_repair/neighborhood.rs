// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CNF-probe neighborhood/instance builders for satcomp_repair (free-var growth +
//! reduced/flip CNF writers). Extracted from satcomp_repair.rs.

use super::*;
use std::collections::BTreeSet;
use std::fs::File;
use std::io::Write;
use std::path::Path;

use anyhow::{Context, Result};

fn variable_clause_index(num_vars: usize, clauses: &[Vec<i32>]) -> Vec<Vec<usize>> {
    let mut by_var = vec![Vec::new(); num_vars];
    for (clause_idx, clause) in clauses.iter().enumerate() {
        for &lit in clause {
            by_var[lit.unsigned_abs() as usize - 1].push(clause_idx);
        }
    }
    by_var
}

pub(super) fn grow_free_vars(
    num_vars: usize,
    clauses: &[Vec<i32>],
    residual_ids: &[usize],
    radius: usize,
) -> BTreeSet<usize> {
    let by_var = variable_clause_index(num_vars, clauses);
    let mut free_vars: BTreeSet<usize> = residual_ids
        .iter()
        .flat_map(|&idx| {
            clauses[idx]
                .iter()
                .map(|lit| lit.unsigned_abs() as usize - 1)
        })
        .collect();
    for _ in 0..radius {
        let mut touched = BTreeSet::new();
        for &var in &free_vars {
            touched.extend(by_var[var].iter().copied());
        }
        for clause_idx in touched {
            for &lit in &clauses[clause_idx] {
                free_vars.insert(lit.unsigned_abs() as usize - 1);
            }
        }
    }
    free_vars
}

pub(super) fn grow_neighborhoods(
    num_vars: usize,
    clauses: &[Vec<i32>],
    residual_ids: &[usize],
    max_radius: usize,
) -> Vec<NeighborhoodRow> {
    let by_var = variable_clause_index(num_vars, clauses);
    let mut free_vars: BTreeSet<usize> = residual_ids
        .iter()
        .flat_map(|&idx| {
            clauses[idx]
                .iter()
                .map(|lit| lit.unsigned_abs() as usize - 1)
        })
        .collect();
    let mut rows = vec![NeighborhoodRow {
        radius: 0,
        free_vars: free_vars.clone(),
        touched_clauses: residual_ids.len(),
        delta_vars: free_vars.len(),
    }];
    for radius in 1..=max_radius {
        let mut touched = BTreeSet::new();
        for &var in &free_vars {
            touched.extend(by_var[var].iter().copied());
        }
        let before = free_vars.clone();
        for clause_idx in &touched {
            for &lit in &clauses[*clause_idx] {
                free_vars.insert(lit.unsigned_abs() as usize - 1);
            }
        }
        rows.push(NeighborhoodRow {
            radius,
            free_vars: free_vars.clone(),
            touched_clauses: touched.len(),
            delta_vars: free_vars.difference(&before).count(),
        });
    }
    rows
}

pub(super) fn write_reduced_cnf(
    path: &Path,
    formula: &RawFormula,
    assignment: &[bool],
    free_vars: &BTreeSet<usize>,
    extra_free_vars: &BTreeSet<usize>,
) -> Result<(usize, Vec<usize>)> {
    let mut frozen_vars = Vec::new();
    for var in 0..formula.num_vars {
        if !free_vars.contains(&var) && !extra_free_vars.contains(&var) {
            frozen_vars.push(var);
        }
    }
    let mut file =
        File::create(path).with_context(|| format!("failed to create '{}'", path.display()))?;
    writeln!(
        file,
        "p cnf {} {}",
        formula.num_vars,
        formula.clauses.len() + frozen_vars.len()
    )?;
    for clause in &formula.clauses {
        for lit in clause {
            write!(file, "{lit} ")?;
        }
        writeln!(file, "0")?;
    }
    for &var in &frozen_vars {
        let lit = if assignment[var] {
            (var + 1) as i32
        } else {
            -((var + 1) as i32)
        };
        writeln!(file, "{lit} 0")?;
    }
    Ok((frozen_vars.len(), frozen_vars))
}

pub(super) fn write_flip_cnf(
    path: &Path,
    formula: &RawFormula,
    assignment: &[bool],
    free_vars: &BTreeSet<usize>,
    flipped_var: usize,
) -> Result<usize> {
    let outside_count = formula.num_vars - free_vars.len();
    let mut file =
        File::create(path).with_context(|| format!("failed to create '{}'", path.display()))?;
    writeln!(
        file,
        "p cnf {} {}",
        formula.num_vars,
        formula.clauses.len() + outside_count
    )?;
    for clause in &formula.clauses {
        for lit in clause {
            write!(file, "{lit} ")?;
        }
        writeln!(file, "0")?;
    }
    let mut units = 0usize;
    for (var, &value) in assignment.iter().enumerate() {
        if free_vars.contains(&var) {
            continue;
        }
        let unit_value = if var == flipped_var { !value } else { value };
        let lit = if unit_value {
            (var + 1) as i32
        } else {
            -((var + 1) as i32)
        };
        writeln!(file, "{lit} 0")?;
        units += 1;
    }
    Ok(units)
}
