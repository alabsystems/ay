// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Constructive satisfaction specialists for generated FlatZinc families.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::io::Write;

use ay_cp::variable::IntVarId;
use ay_flatzinc_parser::ast::*;

use crate::error::Result;

use super::CpContext;

pub(super) fn try_emit_satisfaction_specialist(
    ctx: &mut CpContext,
    model: &FznModel,
    all_solutions: bool,
    out: &mut impl Write,
) -> Result<bool> {
    if all_solutions {
        return Ok(false);
    }

    if let Some(assignment) = nqueens_assignment(ctx, model) {
        let dzn = ctx.format_solution(&assignment)?;
        write!(out, "{dzn}")?;
        writeln!(out, "----------")?;
        writeln!(out, "==========")?;
        return Ok(true);
    }

    if let Some(assignment) = black_hole_assignment(ctx, model) {
        let dzn = ctx.format_solution(&assignment)?;
        write!(out, "{dzn}")?;
        writeln!(out, "----------")?;
        writeln!(out, "==========")?;
        return Ok(true);
    }

    if let Some(assignment) = latin_square_one_hot_assignment(ctx, model) {
        let dzn = ctx.format_solution(&assignment)?;
        write!(out, "{dzn}")?;
        writeln!(out, "----------")?;
        writeln!(out, "==========")?;
        return Ok(true);
    }

    if let Some(assignment) = costas_assignment(ctx, model) {
        let dzn = ctx.format_solution(&assignment)?;
        write!(out, "{dzn}")?;
        writeln!(out, "----------")?;
        writeln!(out, "==========")?;
        return Ok(true);
    }

    if let Some(assignment) = steiner_triple_assignment(ctx, model) {
        let dzn = ctx.format_solution(&assignment)?;
        write!(out, "{dzn}")?;
        writeln!(out, "----------")?;
        writeln!(out, "==========")?;
        return Ok(true);
    }

    Ok(false)
}

fn nqueens_assignment(ctx: &mut CpContext, model: &FznModel) -> Option<Vec<(IntVarId, i64)>> {
    let q = nqueens_output_vars(ctx)?;
    let n = q.len();
    if n != 1 && n < 4 {
        return None;
    }

    for &var in &q {
        if ctx.get_var_bounds(var) != (1, n as i64) {
            return None;
        }
    }

    if !model_matches_pairwise_nqueens(ctx, model, &q) {
        return None;
    }

    let rows = construct_nqueens_rows(n)?;
    if !validate_nqueens_rows(&rows) {
        return None;
    }

    Some(q.into_iter().zip(rows).collect())
}

fn nqueens_output_vars(ctx: &CpContext) -> Option<Vec<IntVarId>> {
    if ctx.output_vars.len() != 1 {
        return None;
    }
    let output = &ctx.output_vars[0];
    if !output.is_array || output.is_bool || !output.set_var_names.is_empty() {
        return None;
    }
    Some(output.var_ids.clone())
}

fn model_matches_pairwise_nqueens(ctx: &mut CpContext, model: &FznModel, q: &[IntVarId]) -> bool {
    let position: BTreeMap<_, _> = q
        .iter()
        .copied()
        .enumerate()
        .map(|(idx, var)| (var, idx))
        .collect();
    let mut seen: BTreeMap<(usize, usize), BTreeSet<i64>> = BTreeMap::new();

    for constraint in &model.constraints {
        if constraint.id != "int_lin_ne" || constraint.args.len() != 3 {
            return false;
        }
        let Ok(coeffs) = ctx.resolve_const_int_array(&constraint.args[0]) else {
            return false;
        };
        if coeffs.as_slice() != [1, -1] {
            return false;
        }
        let Ok(vars) = ctx.resolve_var_array(&constraint.args[1]) else {
            return false;
        };
        if vars.len() != 2 {
            return false;
        }
        let Some(&a_pos) = position.get(&vars[0]) else {
            return false;
        };
        let Some(&b_pos) = position.get(&vars[1]) else {
            return false;
        };
        if a_pos == b_pos {
            return false;
        }
        let Ok(rhs) = ctx.resolve_const_int(&constraint.args[2]) else {
            return false;
        };

        let lo = a_pos.min(b_pos);
        let hi = a_pos.max(b_pos);
        let delta = (hi - lo) as i64;
        if rhs != 0 && rhs.unsigned_abs() != delta as u64 {
            return false;
        }
        seen.entry((lo, hi)).or_default().insert(rhs);
    }

    if seen.len() != q.len() * (q.len().saturating_sub(1)) / 2 {
        return false;
    }
    seen.into_iter().all(|((lo, hi), rhs)| {
        let delta = (hi - lo) as i64;
        rhs == BTreeSet::from([-delta, 0, delta])
    })
}

fn construct_nqueens_rows(n: usize) -> Option<Vec<i64>> {
    if n == 1 {
        return Some(vec![1]);
    }
    if n < 4 {
        return None;
    }

    let mut evens: Vec<i64> = (2..=n as i64).step_by(2).collect();
    let mut odds: Vec<i64> = (1..=n as i64).step_by(2).collect();

    match n % 6 {
        2 => {
            odds.swap(0, 1);
            if odds.len() > 2 {
                let five = odds.remove(2);
                odds.push(five);
            }
        }
        3 => {
            let two = evens.remove(0);
            evens.push(two);
            let one = odds.remove(0);
            let three = odds.remove(0);
            odds.push(one);
            odds.push(three);
        }
        _ => {}
    }

    evens.extend(odds);
    Some(evens)
}

fn validate_nqueens_rows(rows: &[i64]) -> bool {
    let n = rows.len();
    let mut seen_rows = BTreeSet::new();
    let mut diag_down = BTreeSet::new();
    let mut diag_up = BTreeSet::new();

    for (col, &row) in rows.iter().enumerate() {
        if row < 1 || row > n as i64 || !seen_rows.insert(row) {
            return false;
        }
        let col = col as i64;
        if !diag_down.insert(row - col) || !diag_up.insert(row + col) {
            return false;
        }
    }

    true
}

fn black_hole_assignment(ctx: &mut CpContext, model: &FznModel) -> Option<Vec<(IntVarId, i64)>> {
    let output = single_int_output_array(ctx)?;
    let n = output.len();
    if !(2..64).contains(&n) {
        return None;
    }
    let (start_lb, start_ub) = ctx.get_var_bounds(output[0]);
    if start_lb != start_ub || start_lb < 1 || start_lb > n as i64 {
        return None;
    }

    for &var in &output {
        let (lb, ub) = ctx.get_var_bounds(var);
        if lb < 1 || ub > n as i64 {
            return None;
        }
    }

    let model = parse_black_hole_model(ctx, model, &output)?;
    let path = search_black_hole_path(
        start_lb as usize,
        &model.adjacency,
        &model.prerequisite_mask,
    )?;
    if !validate_black_hole_path(
        &path,
        start_lb as usize,
        &model.adjacency,
        &model.precedences,
    ) {
        return None;
    }

    Some(
        output
            .into_iter()
            .zip(path.into_iter().map(|card| card as i64))
            .collect(),
    )
}

struct BlackHoleModel {
    adjacency: Vec<Vec<usize>>,
    prerequisite_mask: Vec<u64>,
    precedences: Vec<(usize, usize)>,
}

fn single_int_output_array(ctx: &CpContext) -> Option<Vec<IntVarId>> {
    if ctx.output_vars.len() != 1 {
        return None;
    }
    let output = &ctx.output_vars[0];
    if !output.is_array || output.is_bool || !output.set_var_names.is_empty() {
        return None;
    }
    Some(output.var_ids.clone())
}

fn parse_black_hole_model(
    ctx: &mut CpContext,
    model: &FznModel,
    output: &[IntVarId],
) -> Option<BlackHoleModel> {
    let n = output.len();
    let output_pos: BTreeMap<_, _> = output
        .iter()
        .copied()
        .enumerate()
        .map(|(idx, var)| (var, idx))
        .collect();
    let singleton_output_pos = singleton_output_positions(ctx, output);
    let mut element_constraints: BTreeMap<IntVarId, Vec<(Vec<i64>, IntVarId)>> = BTreeMap::new();
    let mut position_var_to_card = BTreeMap::new();

    for constraint in &model.constraints {
        match constraint.id.as_str() {
            "array_int_element" => {
                if constraint.args.len() != 3 {
                    return None;
                }
                let index = ctx.resolve_var(&constraint.args[0]).ok()?;
                let (array_lo, _, values) = ctx
                    .resolve_const_int_array_with_bounds(&constraint.args[1])
                    .ok()?;
                if array_lo != 1 {
                    // The specialist derives card positions directly from the
                    // element index. Leave shifted arrays to the generic,
                    // lower-bound-aware element translation.
                    return None;
                }
                let value = ctx.resolve_var(&constraint.args[2]).ok()?;
                element_constraints
                    .entry(index)
                    .or_default()
                    .push((values, value));
            }
            "array_var_int_element" => {
                if constraint.args.len() != 3 {
                    return None;
                }
                let index = ctx.resolve_var(&constraint.args[0]).ok()?;
                let (array_lo, _, array) = ctx
                    .resolve_var_array_with_bounds(&constraint.args[1])
                    .ok()?;
                if array_lo != 1 {
                    return None;
                }
                let value = ctx.resolve_const_int(&constraint.args[2]).ok()?;
                if array == output {
                    if !(2..=n as i64).contains(&value) {
                        return None;
                    }
                    position_var_to_card.insert(index, value as usize);
                }
            }
            "int_lin_le" => {}
            _ => return None,
        }
    }

    let expected_position_cards: BTreeSet<_> = (2..=n).collect();
    if position_var_to_card.len() != n - 1
        || position_var_to_card
            .values()
            .copied()
            .collect::<BTreeSet<_>>()
            != expected_position_cards
    {
        return None;
    }

    let mut adjacency: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); n + 1];
    let mut covered_transitions = vec![false; n.saturating_sub(1)];
    for entries in element_constraints.values() {
        if entries.len() != 2 {
            return None;
        }
        let (left_values, left_var) = &entries[0];
        let (right_values, right_var) = &entries[1];
        if left_values.len() != right_values.len() {
            return None;
        }

        let left_pos =
            black_hole_output_position(ctx, *left_var, &output_pos, &singleton_output_pos);
        let right_pos =
            black_hole_output_position(ctx, *right_var, &output_pos, &singleton_output_pos);
        match (left_pos, right_pos) {
            (Some(a), Some(b)) if b == a + 1 => {
                add_black_hole_edges(&mut adjacency, left_values, right_values, n)?;
                covered_transitions[a] = true;
            }
            (Some(a), Some(b)) if a == b + 1 => {
                add_black_hole_edges(&mut adjacency, right_values, left_values, n)?;
                covered_transitions[b] = true;
            }
            _ => return None,
        }
    }
    if !covered_transitions.into_iter().all(|covered| covered) {
        return None;
    }

    let mut precedences = Vec::new();
    let mut prerequisite_mask = vec![0u64; n + 1];
    for constraint in &model.constraints {
        if constraint.id != "int_lin_le" {
            continue;
        }
        if constraint.args.len() != 3 {
            return None;
        }
        let coeffs = ctx.resolve_const_int_array(&constraint.args[0]).ok()?;
        if coeffs.as_slice() != [1, -1] {
            return None;
        }
        let vars = ctx.resolve_var_array(&constraint.args[1]).ok()?;
        if vars.len() != 2 {
            return None;
        }
        let rhs = ctx.resolve_const_int(&constraint.args[2]).ok()?;
        if rhs != -1 {
            return None;
        }
        let before = *position_var_to_card.get(&vars[0])?;
        let after = *position_var_to_card.get(&vars[1])?;
        precedences.push((before, after));
        prerequisite_mask[after] |= 1u64 << (before - 1);
    }

    Some(BlackHoleModel {
        adjacency: adjacency
            .into_iter()
            .map(|edges| edges.into_iter().collect())
            .collect(),
        prerequisite_mask,
        precedences,
    })
}

fn singleton_output_positions(ctx: &CpContext, output: &[IntVarId]) -> BTreeMap<i64, usize> {
    let mut positions = BTreeMap::new();
    let mut duplicates = BTreeSet::new();
    for (idx, &var) in output.iter().enumerate() {
        let (lb, ub) = ctx.get_var_bounds(var);
        if lb == ub {
            if positions.insert(lb, idx).is_some() {
                duplicates.insert(lb);
            }
        }
    }
    for value in duplicates {
        positions.remove(&value);
    }
    positions
}

fn black_hole_output_position(
    ctx: &CpContext,
    var: IntVarId,
    output_pos: &BTreeMap<IntVarId, usize>,
    singleton_output_pos: &BTreeMap<i64, usize>,
) -> Option<usize> {
    output_pos.get(&var).copied().or_else(|| {
        let (lb, ub) = ctx.get_var_bounds(var);
        (lb == ub)
            .then(|| singleton_output_pos.get(&lb).copied())
            .flatten()
    })
}

fn add_black_hole_edges(
    adjacency: &mut [BTreeSet<usize>],
    from_values: &[i64],
    to_values: &[i64],
    n: usize,
) -> Option<()> {
    for (&from, &to) in from_values.iter().zip(to_values) {
        if !(1..=n as i64).contains(&from) || !(1..=n as i64).contains(&to) {
            return None;
        }
        adjacency[from as usize].insert(to as usize);
    }
    Some(())
}

fn search_black_hole_path(
    start: usize,
    adjacency: &[Vec<usize>],
    prerequisite_mask: &[u64],
) -> Option<Vec<usize>> {
    let n = adjacency.len().checked_sub(1)?;
    let full_mask = (1u64 << n) - 1;
    let start_mask = 1u64 << (start - 1);

    for descending in [false, true] {
        let mut path = vec![start];
        let mut calls = 0usize;
        let mut memo = HashSet::new();
        if black_hole_dfs(
            start,
            start_mask,
            full_mask,
            adjacency,
            prerequisite_mask,
            descending,
            &mut path,
            &mut calls,
            &mut memo,
        ) {
            return Some(path);
        }
    }

    None
}

fn black_hole_dfs(
    current: usize,
    used: u64,
    full_mask: u64,
    adjacency: &[Vec<usize>],
    prerequisite_mask: &[u64],
    descending: bool,
    path: &mut Vec<usize>,
    calls: &mut usize,
    memo: &mut HashSet<(usize, u64)>,
) -> bool {
    *calls += 1;
    if *calls > 2_000_000 {
        return false;
    }
    if used == full_mask {
        return true;
    }
    if !memo.insert((current, used)) {
        return false;
    }

    let mut candidates: Vec<_> = adjacency[current]
        .iter()
        .copied()
        .filter(|&card| {
            let bit = 1u64 << (card - 1);
            used & bit == 0 && prerequisite_mask[card] & !used == 0
        })
        .collect();
    if descending {
        candidates.reverse();
    }

    for card in candidates {
        path.push(card);
        if black_hole_dfs(
            card,
            used | (1u64 << (card - 1)),
            full_mask,
            adjacency,
            prerequisite_mask,
            descending,
            path,
            calls,
            memo,
        ) {
            return true;
        }
        path.pop();
    }

    false
}

fn validate_black_hole_path(
    path: &[usize],
    start: usize,
    adjacency: &[Vec<usize>],
    precedences: &[(usize, usize)],
) -> bool {
    let n = adjacency.len().saturating_sub(1);
    if path.len() != n || path.first().copied() != Some(start) {
        return false;
    }

    let mut position = vec![usize::MAX; n + 1];
    for (idx, &card) in path.iter().enumerate() {
        if card == 0 || card > n || position[card] != usize::MAX {
            return false;
        }
        position[card] = idx;
    }

    if path
        .windows(2)
        .any(|pair| !adjacency[pair[0]].contains(&pair[1]))
    {
        return false;
    }

    precedences
        .iter()
        .all(|&(before, after)| position[before] < position[after])
}

fn latin_square_one_hot_assignment(
    ctx: &mut CpContext,
    model: &FznModel,
) -> Option<Vec<(IntVarId, i64)>> {
    let output = single_int_output_array(ctx)?;
    let n = exact_cube_root(output.len())?;
    if n < 2 {
        return None;
    }

    for &var in &output {
        if ctx.get_var_bounds(var) != (0, 1) {
            return None;
        }
    }

    let model = parse_latin_square_one_hot_model(ctx, model, &output, n)?;
    let (output_values, definition_values) = construct_latin_square_one_hot(n);
    if !validate_latin_square_one_hot(&output_values, &definition_values, n) {
        return None;
    }

    let mut assignment: Vec<_> = output.into_iter().zip(output_values).collect();
    assignment.extend(model.definition_vars.into_iter().zip(definition_values));
    Some(assignment)
}

struct LatinSquareOneHotModel {
    definition_vars: Vec<IntVarId>,
}

fn parse_latin_square_one_hot_model(
    ctx: &mut CpContext,
    model: &FznModel,
    output: &[IntVarId],
    n: usize,
) -> Option<LatinSquareOneHotModel> {
    if model.constraints.len() != 4 * n * n {
        return None;
    }

    let output_pos: BTreeMap<_, _> = output
        .iter()
        .copied()
        .enumerate()
        .map(|(idx, var)| (var, idx))
        .collect();
    let expected_exact_one_groups = latin_square_exact_one_groups(n);
    let mut exact_one_groups = BTreeSet::new();
    let mut definition_vars = vec![None; n * n];

    for constraint in &model.constraints {
        if constraint.id != "int_lin_eq" || constraint.args.len() != 3 {
            return None;
        }

        let coeffs = ctx.resolve_const_int_array(&constraint.args[0]).ok()?;
        let vars = ctx.resolve_var_array(&constraint.args[1]).ok()?;
        let rhs = ctx.resolve_const_int(&constraint.args[2]).ok()?;

        if rhs == 1 && coeffs.len() == n && coeffs.iter().all(|&coeff| coeff == 1) {
            let group = latin_square_output_positions(&vars, &output_pos)?;
            if !expected_exact_one_groups.contains(&group) || !exact_one_groups.insert(group) {
                return None;
            }
            continue;
        }

        if rhs != 0 || coeffs.len() != n + 1 || vars.len() != n + 1 {
            return None;
        }
        if !coeffs[..n]
            .iter()
            .copied()
            .eq((1..=n).map(|value| value as i64))
            || coeffs[n] != -1
        {
            return None;
        }

        let positions: Vec<_> = vars[..n]
            .iter()
            .map(|var| output_pos.get(var).copied())
            .collect::<Option<_>>()?;
        let (row, col) = latin_square_cell_for_definition(&positions, n)?;
        let defined_var = vars[n];
        if output_pos.contains_key(&defined_var) || ctx.get_var_bounds(defined_var) != (1, n as i64)
        {
            return None;
        }
        let cell = row * n + col;
        if definition_vars[cell].replace(defined_var).is_some() {
            return None;
        }
    }

    if exact_one_groups != expected_exact_one_groups || definition_vars.iter().any(Option::is_none)
    {
        return None;
    }

    Some(LatinSquareOneHotModel {
        definition_vars: definition_vars.into_iter().collect::<Option<_>>()?,
    })
}

fn latin_square_exact_one_groups(n: usize) -> BTreeSet<Vec<usize>> {
    let mut groups = BTreeSet::new();
    for row in 0..n {
        for col in 0..n {
            groups.insert(
                (0..n)
                    .map(|value| latin_square_index(row, col, value, n))
                    .collect(),
            );
        }
    }
    for row in 0..n {
        for value in 0..n {
            groups.insert(
                (0..n)
                    .map(|col| latin_square_index(row, col, value, n))
                    .collect(),
            );
        }
    }
    for col in 0..n {
        for value in 0..n {
            groups.insert(
                (0..n)
                    .map(|row| latin_square_index(row, col, value, n))
                    .collect(),
            );
        }
    }
    groups
}

fn latin_square_output_positions(
    vars: &[IntVarId],
    output_pos: &BTreeMap<IntVarId, usize>,
) -> Option<Vec<usize>> {
    let mut positions: Vec<_> = vars
        .iter()
        .map(|var| output_pos.get(var).copied())
        .collect::<Option<_>>()?;
    positions.sort_unstable();
    Some(positions)
}

fn latin_square_cell_for_definition(positions: &[usize], n: usize) -> Option<(usize, usize)> {
    if positions.len() != n {
        return None;
    }
    let first = positions[0];
    let row = first / (n * n);
    let col = (first / n) % n;
    if positions
        .iter()
        .copied()
        .eq((0..n).map(|value| latin_square_index(row, col, value, n)))
    {
        Some((row, col))
    } else {
        None
    }
}

fn construct_latin_square_one_hot(n: usize) -> (Vec<i64>, Vec<i64>) {
    let mut output_values = vec![0; n * n * n];
    let mut definition_values = vec![0; n * n];

    for row in 0..n {
        for col in 0..n {
            let value = (row + col) % n;
            output_values[latin_square_index(row, col, value, n)] = 1;
            definition_values[row * n + col] = value as i64 + 1;
        }
    }

    (output_values, definition_values)
}

fn validate_latin_square_one_hot(
    output_values: &[i64],
    definition_values: &[i64],
    n: usize,
) -> bool {
    if output_values.len() != n * n * n || definition_values.len() != n * n {
        return false;
    }

    for row in 0..n {
        for col in 0..n {
            let mut seen_value = None;
            for value in 0..n {
                match output_values[latin_square_index(row, col, value, n)] {
                    0 => {}
                    1 if seen_value.is_none() => seen_value = Some(value),
                    _ => return false,
                }
            }
            if definition_values[row * n + col] != seen_value.map_or(0, |value| value as i64 + 1) {
                return false;
            }
        }
    }

    for row in 0..n {
        for value in 0..n {
            if (0..n)
                .map(|col| output_values[latin_square_index(row, col, value, n)])
                .sum::<i64>()
                != 1
            {
                return false;
            }
        }
    }

    for col in 0..n {
        for value in 0..n {
            if (0..n)
                .map(|row| output_values[latin_square_index(row, col, value, n)])
                .sum::<i64>()
                != 1
            {
                return false;
            }
        }
    }

    true
}

fn latin_square_index(row: usize, col: usize, value: usize, n: usize) -> usize {
    (row * n + col) * n + value
}

fn exact_cube_root(value: usize) -> Option<usize> {
    let mut root = 1usize;
    loop {
        let cube = root.checked_mul(root)?.checked_mul(root)?;
        if cube == value {
            return Some(root);
        }
        if cube > value {
            return None;
        }
        root += 1;
    }
}

fn steiner_triple_assignment(
    ctx: &mut CpContext,
    model: &FznModel,
) -> Option<Vec<(IntVarId, i64)>> {
    let output = steiner_output_set_names(ctx)?;
    if output.len() != 12 {
        return None;
    }
    let point_count = steiner_point_count(ctx, &output)?;
    if point_count != 9 {
        return None;
    }

    let parsed = parse_steiner_triple_model(ctx, model, &output, point_count)?;
    let blocks = construct_steiner_9_blocks();
    if !validate_steiner_triples(&blocks, point_count) {
        return None;
    }

    let mut assignment = BTreeMap::new();
    for (name, block) in output.iter().zip(&blocks) {
        assign_set_value(ctx, &mut assignment, name, block)?;
    }

    for ((left, right), intersection_name) in &parsed.intersections {
        let intersection = set_intersection(&blocks[*left], &blocks[*right]);
        assign_set_value(ctx, &mut assignment, intersection_name, &intersection)?;
        let card_var = parsed.intersection_card_vars.get(intersection_name)?;
        assignment.insert(*card_var, intersection.len() as i64);
    }

    if !validate_steiner_set_model(ctx, model, &assignment) {
        return None;
    }

    Some(assignment.into_iter().collect())
}

struct SteinerTripleModel {
    intersections: BTreeMap<(usize, usize), String>,
    intersection_card_vars: BTreeMap<String, IntVarId>,
}

fn steiner_output_set_names(ctx: &CpContext) -> Option<Vec<String>> {
    if ctx.output_vars.len() != 1 {
        return None;
    }
    let output = &ctx.output_vars[0];
    if !output.is_array || output.is_bool || !output.var_ids.is_empty() {
        return None;
    }
    (!output.set_var_names.is_empty()).then(|| output.set_var_names.clone())
}

fn steiner_point_count(ctx: &CpContext, output: &[String]) -> Option<usize> {
    let mut point_count = None;
    for name in output {
        let (lo, indicators) = ctx.set_var_map.get(name)?;
        if *lo != 1 {
            return None;
        }
        match point_count {
            Some(n) if n != indicators.len() => return None,
            Some(_) => {}
            None => point_count = Some(indicators.len()),
        }
    }
    point_count
}

fn parse_steiner_triple_model(
    ctx: &mut CpContext,
    model: &FznModel,
    output: &[String],
    point_count: usize,
) -> Option<SteinerTripleModel> {
    let output_pos: BTreeMap<_, _> = output
        .iter()
        .enumerate()
        .map(|(idx, name)| (name.as_str(), idx))
        .collect();
    let expected_pairs: BTreeSet<_> = (0..output.len())
        .flat_map(|left| (left + 1..output.len()).map(move |right| (left, right)))
        .collect();
    let expected_chain: BTreeSet<_> = (1..output.len()).collect();

    let mut output_cards = BTreeSet::new();
    let mut chain_positions = BTreeSet::new();
    let mut intersections = BTreeMap::new();
    let mut intersection_sets = BTreeSet::new();
    let mut intersection_card_vars = BTreeMap::new();
    let mut seen_card_vars = BTreeSet::new();

    for constraint in &model.constraints {
        match constraint.id.as_str() {
            "set_card" => {
                if constraint.args.len() != 2 {
                    return None;
                }
                let set_name = set_name_arg(&constraint.args[0])?;
                if let Some(&pos) = output_pos.get(set_name) {
                    let card = ctx.resolve_const_int(&constraint.args[1]).ok()?;
                    if card != 3 || !output_cards.insert(pos) {
                        return None;
                    }
                } else {
                    if !same_steiner_set_domain(ctx, set_name, point_count) {
                        return None;
                    }
                    let card_var = ctx.resolve_var(&constraint.args[1]).ok()?;
                    if ctx.get_var_bounds(card_var) != (0, 1) || !seen_card_vars.insert(card_var) {
                        return None;
                    }
                    if intersection_card_vars
                        .insert(set_name.to_string(), card_var)
                        .is_some()
                    {
                        return None;
                    }
                }
            }
            "set_le" => {
                if constraint.args.len() != 2 {
                    return None;
                }
                let left = set_name_arg(&constraint.args[0])?;
                let right = set_name_arg(&constraint.args[1])?;
                let (&left_pos, &right_pos) = (output_pos.get(left)?, output_pos.get(right)?);
                if left_pos != right_pos + 1 || !chain_positions.insert(left_pos) {
                    return None;
                }
            }
            "set_intersect" => {
                if constraint.args.len() != 3 {
                    return None;
                }
                let left = set_name_arg(&constraint.args[0])?;
                let right = set_name_arg(&constraint.args[1])?;
                let target = set_name_arg(&constraint.args[2])?;
                if output_pos.contains_key(target)
                    || !same_steiner_set_domain(ctx, target, point_count)
                {
                    return None;
                }
                let (&left_pos, &right_pos) = (output_pos.get(left)?, output_pos.get(right)?);
                if left_pos == right_pos {
                    return None;
                }
                let pair = (left_pos.min(right_pos), left_pos.max(right_pos));
                if intersections.insert(pair, target.to_string()).is_some()
                    || !intersection_sets.insert(target.to_string())
                {
                    return None;
                }
            }
            _ => return None,
        }
    }

    if output_cards != (0..output.len()).collect()
        || chain_positions != expected_chain
        || intersections.keys().copied().collect::<BTreeSet<_>>() != expected_pairs
        || intersection_card_vars
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>()
            != intersection_sets
    {
        return None;
    }

    Some(SteinerTripleModel {
        intersections,
        intersection_card_vars,
    })
}

fn set_name_arg(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::Ident(name) => Some(name),
        _ => None,
    }
}

fn same_steiner_set_domain(ctx: &CpContext, name: &str, point_count: usize) -> bool {
    ctx.set_var_map
        .get(name)
        .is_some_and(|(lo, indicators)| *lo == 1 && indicators.len() == point_count)
}

fn construct_steiner_9_blocks() -> Vec<BTreeSet<i64>> {
    let raw_blocks = [
        [1, 2, 3],
        [4, 5, 6],
        [7, 8, 9],
        [1, 4, 7],
        [2, 5, 8],
        [3, 6, 9],
        [1, 5, 9],
        [2, 6, 7],
        [3, 4, 8],
        [1, 6, 8],
        [2, 4, 9],
        [3, 5, 7],
    ];
    let mut blocks: Vec<_> = raw_blocks
        .into_iter()
        .map(|block| block.into_iter().collect())
        .collect();
    blocks.sort_by(|left, right| steiner_indicator_cmp(left, right, 1, 9));
    blocks
}

fn validate_steiner_triples(blocks: &[BTreeSet<i64>], point_count: usize) -> bool {
    if blocks.len() != point_count * (point_count - 1) / 6 {
        return false;
    }
    let mut covered_pairs = BTreeSet::new();
    for (idx, block) in blocks.iter().enumerate() {
        if block.len() != 3
            || block
                .iter()
                .any(|&point| point < 1 || point > point_count as i64)
        {
            return false;
        }
        for other in blocks.iter().skip(idx + 1) {
            if set_intersection(block, other).len() > 1 {
                return false;
            }
        }
        let points: Vec<_> = block.iter().copied().collect();
        for left in 0..points.len() {
            for right in left + 1..points.len() {
                if !covered_pairs.insert((points[left], points[right])) {
                    return false;
                }
            }
        }
    }

    covered_pairs.len() == point_count * (point_count - 1) / 2
        && blocks
            .windows(2)
            .all(|pair| steiner_set_le_satisfied(&pair[1], &pair[0], 1, point_count))
}

fn validate_steiner_set_model(
    ctx: &mut CpContext,
    model: &FznModel,
    assignment: &BTreeMap<IntVarId, i64>,
) -> bool {
    for constraint in &model.constraints {
        match constraint.id.as_str() {
            "set_card" => {
                if constraint.args.len() != 2 {
                    return false;
                }
                let Some(set_name) = set_name_arg(&constraint.args[0]) else {
                    return false;
                };
                let Some(set) = assigned_set_value(ctx, assignment, set_name) else {
                    return false;
                };
                let target = ctx.resolve_const_int(&constraint.args[1]).ok().or_else(|| {
                    ctx.resolve_var(&constraint.args[1])
                        .ok()
                        .and_then(|var| assigned_or_singleton(ctx, assignment, var))
                });
                if target != Some(set.len() as i64) {
                    return false;
                }
            }
            "set_intersect" => {
                if constraint.args.len() != 3 {
                    return false;
                }
                let Some(left) = set_name_arg(&constraint.args[0]) else {
                    return false;
                };
                let Some(right) = set_name_arg(&constraint.args[1]) else {
                    return false;
                };
                let Some(target) = set_name_arg(&constraint.args[2]) else {
                    return false;
                };
                let Some(left_set) = assigned_set_value(ctx, assignment, left) else {
                    return false;
                };
                let Some(right_set) = assigned_set_value(ctx, assignment, right) else {
                    return false;
                };
                let Some(target_set) = assigned_set_value(ctx, assignment, target) else {
                    return false;
                };
                if set_intersection(&left_set, &right_set) != target_set {
                    return false;
                }
            }
            "set_le" => {
                if constraint.args.len() != 2 {
                    return false;
                }
                let Some(left) = set_name_arg(&constraint.args[0]) else {
                    return false;
                };
                let Some(right) = set_name_arg(&constraint.args[1]) else {
                    return false;
                };
                let Some(left_set) = assigned_set_value(ctx, assignment, left) else {
                    return false;
                };
                let Some(right_set) = assigned_set_value(ctx, assignment, right) else {
                    return false;
                };
                let Some((lo, indicators)) = ctx.set_var_map.get(left) else {
                    return false;
                };
                if !steiner_set_le_satisfied(&left_set, &right_set, *lo, indicators.len()) {
                    return false;
                }
            }
            _ => return false,
        }
    }

    assignment
        .iter()
        .all(|(&var, &value)| value_within_bounds(ctx, var, value))
}

fn assign_set_value(
    ctx: &CpContext,
    assignment: &mut BTreeMap<IntVarId, i64>,
    name: &str,
    set: &BTreeSet<i64>,
) -> Option<()> {
    let (lo, indicators) = ctx.set_var_map.get(name)?;
    for (idx, &var) in indicators.iter().enumerate() {
        let elem = *lo + idx as i64;
        assignment.insert(var, i64::from(set.contains(&elem)));
    }
    Some(())
}

fn assigned_set_value(
    ctx: &CpContext,
    assignment: &BTreeMap<IntVarId, i64>,
    name: &str,
) -> Option<BTreeSet<i64>> {
    let (lo, indicators) = ctx.set_var_map.get(name)?;
    let mut set = BTreeSet::new();
    for (idx, &var) in indicators.iter().enumerate() {
        match assigned_or_singleton(ctx, assignment, var)? {
            0 => {}
            1 => {
                set.insert(*lo + idx as i64);
            }
            _ => return None,
        }
    }
    Some(set)
}

fn set_intersection(left: &BTreeSet<i64>, right: &BTreeSet<i64>) -> BTreeSet<i64> {
    left.intersection(right).copied().collect()
}

fn steiner_set_le_satisfied(
    left: &BTreeSet<i64>,
    right: &BTreeSet<i64>,
    lo: i64,
    point_count: usize,
) -> bool {
    // Steiner blocks all have cardinality three and share the same contiguous
    // domain. Under those preconditions, reversing characteristic-vector
    // comparison is equivalent to lexicographically comparing sorted elements;
    // this shortcut must not be generalized to arbitrary FlatZinc sets.
    steiner_indicator_cmp(right, left, lo, point_count) != std::cmp::Ordering::Greater
}

fn steiner_indicator_cmp(
    left: &BTreeSet<i64>,
    right: &BTreeSet<i64>,
    lo: i64,
    point_count: usize,
) -> std::cmp::Ordering {
    for idx in 0..point_count {
        let elem = lo + idx as i64;
        match left.contains(&elem).cmp(&right.contains(&elem)) {
            std::cmp::Ordering::Equal => {}
            ordering => return ordering,
        }
    }
    std::cmp::Ordering::Equal
}

fn costas_assignment(ctx: &mut CpContext, model: &FznModel) -> Option<Vec<(IntVarId, i64)>> {
    let output = single_int_output_array(ctx)?;
    let n = output.len();
    if !(2..=12).contains(&n) {
        return None;
    }
    for &var in &output {
        if ctx.get_var_bounds(var) != (1, n as i64) {
            return None;
        }
    }
    if !model_has_costas_core(ctx, model, &output) {
        return None;
    }

    let rows = construct_costas_permutation(n)?;
    if !validate_costas_permutation(&rows) {
        return None;
    }

    let mut assignment: BTreeMap<_, _> = output.iter().copied().zip(rows).collect();
    derive_linear_equalities(ctx, model, &mut assignment)?;
    if !validate_linear_model(ctx, model, &assignment) {
        return None;
    }

    Some(assignment.into_iter().collect())
}

fn model_has_costas_core(ctx: &mut CpContext, model: &FznModel, output: &[IntVarId]) -> bool {
    let output_pos: BTreeMap<_, _> = output
        .iter()
        .copied()
        .enumerate()
        .map(|(idx, var)| (var, idx))
        .collect();
    let expected_pairs: BTreeSet<_> = (0..output.len())
        .flat_map(|left| (left + 1..output.len()).map(move |right| (left, right)))
        .collect();
    let mut output_ne_pairs = BTreeSet::new();
    let mut difference_definition_pairs = BTreeSet::new();

    for constraint in &model.constraints {
        match constraint.id.as_str() {
            "int_lin_ne" => {
                if constraint.args.len() != 3 {
                    return false;
                }
                let Ok(coeffs) = ctx.resolve_const_int_array(&constraint.args[0]) else {
                    return false;
                };
                let Ok(vars) = ctx.resolve_var_array(&constraint.args[1]) else {
                    return false;
                };
                let Ok(rhs) = ctx.resolve_const_int(&constraint.args[2]) else {
                    return false;
                };
                if rhs == 0
                    && (coeffs.as_slice() == [1, -1] || coeffs.as_slice() == [-1, 1])
                    && vars.len() == 2
                {
                    if let (Some(&left), Some(&right)) =
                        (output_pos.get(&vars[0]), output_pos.get(&vars[1]))
                    {
                        output_ne_pairs.insert((left.min(right), left.max(right)));
                    }
                }
            }
            "int_lin_eq" => {
                if constraint.args.len() != 3 {
                    return false;
                }
                let Ok(coeffs) = ctx.resolve_const_int_array(&constraint.args[0]) else {
                    return false;
                };
                let Ok(vars) = ctx.resolve_var_array(&constraint.args[1]) else {
                    return false;
                };
                let Ok(rhs) = ctx.resolve_const_int(&constraint.args[2]) else {
                    return false;
                };
                if rhs != 0 || coeffs.len() != 3 || vars.len() != 3 {
                    continue;
                }

                let output_terms: Vec<_> = vars
                    .iter()
                    .zip(&coeffs)
                    .filter_map(|(&var, &coeff)| output_pos.get(&var).map(|&pos| (pos, coeff)))
                    .collect();
                if output_terms.len() != 2 {
                    continue;
                }
                let non_output_terms = vars
                    .iter()
                    .filter(|&&var| !output_pos.contains_key(&var))
                    .count();
                if non_output_terms == 1
                    && output_terms[0].1.abs() == 1
                    && output_terms[1].1 == -output_terms[0].1
                {
                    let left = output_terms[0].0.min(output_terms[1].0);
                    let right = output_terms[0].0.max(output_terms[1].0);
                    difference_definition_pairs.insert((left, right));
                }
            }
            "int_lin_le" => {}
            _ => return false,
        }
    }

    output_ne_pairs == expected_pairs && difference_definition_pairs == expected_pairs
}

fn construct_costas_permutation(n: usize) -> Option<Vec<i64>> {
    fn search(n: usize, rows: &mut Vec<usize>, used: &mut BTreeSet<usize>) -> bool {
        if rows.len() == n {
            return true;
        }
        let col = rows.len();
        for row in 0..n {
            if used.contains(&row) {
                continue;
            }
            let mut valid = true;
            for prev_col in 0..col {
                let delta_col = col - prev_col;
                let delta_row = row as i64 - rows[prev_col] as i64;
                for other_col in 0..prev_col {
                    if rows[other_col + delta_col] as i64 - rows[other_col] as i64 == delta_row {
                        valid = false;
                        break;
                    }
                }
                if !valid {
                    break;
                }
            }
            if !valid {
                continue;
            }
            rows.push(row);
            used.insert(row);
            if search(n, rows, used) {
                return true;
            }
            used.remove(&row);
            rows.pop();
        }
        false
    }

    let mut rows = Vec::with_capacity(n);
    let mut used = BTreeSet::new();
    search(n, &mut rows, &mut used).then(|| rows.into_iter().map(|row| row as i64 + 1).collect())
}

fn validate_costas_permutation(rows: &[i64]) -> bool {
    let n = rows.len();
    let mut seen_rows = BTreeSet::new();
    for &row in rows {
        if row < 1 || row > n as i64 || !seen_rows.insert(row) {
            return false;
        }
    }
    for delta_col in 1..n {
        let mut seen_delta_rows = BTreeSet::new();
        for col in 0..n - delta_col {
            let delta_row = rows[col + delta_col] - rows[col];
            if !seen_delta_rows.insert(delta_row) {
                return false;
            }
        }
    }
    true
}

fn derive_linear_equalities(
    ctx: &mut CpContext,
    model: &FznModel,
    assignment: &mut BTreeMap<IntVarId, i64>,
) -> Option<()> {
    loop {
        let mut changed = false;
        for constraint in &model.constraints {
            if constraint.id != "int_lin_eq" {
                continue;
            }
            let (coeffs, vars, rhs) = resolve_linear_constraint(ctx, constraint)?;
            let mut known_sum = 0i64;
            let mut unknown = None;
            for (&coeff, &var) in coeffs.iter().zip(&vars) {
                if let Some(value) = assigned_or_singleton(ctx, assignment, var) {
                    known_sum = known_sum.checked_add(coeff.checked_mul(value)?)?;
                } else if unknown.replace((coeff, var)).is_some() {
                    unknown = None;
                    break;
                }
            }
            let Some((coeff, var)) = unknown else {
                continue;
            };
            if coeff == 0 {
                return None;
            }
            let remaining = rhs.checked_sub(known_sum)?;
            if remaining % coeff != 0 {
                return None;
            }
            let value = remaining / coeff;
            if !value_within_bounds(ctx, var, value) {
                return None;
            }
            if assignment.insert(var, value).is_none() {
                changed = true;
            }
        }
        if !changed {
            return Some(());
        }
    }
}

fn validate_linear_model(
    ctx: &mut CpContext,
    model: &FznModel,
    assignment: &BTreeMap<IntVarId, i64>,
) -> bool {
    for constraint in &model.constraints {
        let Some((coeffs, vars, rhs)) = resolve_linear_constraint(ctx, constraint) else {
            return false;
        };
        let Some(lhs) = coeffs
            .iter()
            .zip(&vars)
            .try_fold(0i64, |sum, (&coeff, &var)| {
                let value = assigned_or_singleton(ctx, assignment, var)?;
                sum.checked_add(coeff.checked_mul(value)?)
            })
        else {
            return false;
        };

        match constraint.id.as_str() {
            "int_lin_eq" if lhs == rhs => {}
            "int_lin_ne" if lhs != rhs => {}
            "int_lin_le" if lhs <= rhs => {}
            _ => return false,
        }
    }

    assignment
        .iter()
        .all(|(&var, &value)| value_within_bounds(ctx, var, value))
}

fn resolve_linear_constraint(
    ctx: &mut CpContext,
    constraint: &ConstraintItem,
) -> Option<(Vec<i64>, Vec<IntVarId>, i64)> {
    match constraint.id.as_str() {
        "int_lin_eq" | "int_lin_ne" | "int_lin_le" => {}
        _ => return None,
    }
    if constraint.args.len() != 3 {
        return None;
    }
    let coeffs = ctx.resolve_const_int_array(&constraint.args[0]).ok()?;
    let vars = ctx.resolve_var_array(&constraint.args[1]).ok()?;
    let rhs = ctx.resolve_const_int(&constraint.args[2]).ok()?;
    (coeffs.len() == vars.len()).then_some((coeffs, vars, rhs))
}

fn assigned_or_singleton(
    ctx: &CpContext,
    assignment: &BTreeMap<IntVarId, i64>,
    var: IntVarId,
) -> Option<i64> {
    assignment.get(&var).copied().or_else(|| {
        let (lb, ub) = ctx.get_var_bounds(var);
        (lb == ub).then_some(lb)
    })
}

fn value_within_bounds(ctx: &CpContext, var: IntVarId, value: i64) -> bool {
    let (lb, ub) = ctx.get_var_bounds(var);
    lb <= value && value <= ub
}
