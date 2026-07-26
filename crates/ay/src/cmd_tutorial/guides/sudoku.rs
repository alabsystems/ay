// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;
use std::io::{self, BufRead, Write};

use anyhow::Result;

type SudokuGrid = [[i64; 4]; 4];
type SudokuMoves = HashMap<(usize, usize), i64>;

const GIVENS: [((usize, usize), i64); 6] = [
    ((0, 1), 2),
    ((0, 3), 4),
    ((1, 2), 1),
    ((2, 0), 2),
    ((2, 3), 3),
    ((3, 1), 3),
];

pub(super) fn run() -> Result<()> {
    println!();
    println!("=== AY Sudoku Lab ===");
    println!("A live 4x4 game backed by AY's real QF_LIA solver.");
    println!();
    println!("Commands:");
    println!("  set ROW COL VALUE   place 1..4, for example: set 1 1 1");
    println!("  clear ROW COL       remove one of your moves");
    println!("  check               ask whether the board can be completed");
    println!("  hint                prove a forced cell when possible");
    println!("  solve               show and independently validate a completion");
    println!("  why                 print the generated SMT-LIB model");
    println!("  reset               clear your moves (the clues remain)");
    println!("  quit                leave the lab");
    println!();

    let mut moves = SudokuMoves::new();
    print_partial(&moves);
    let stdin = io::stdin();
    loop {
        print!("sudoku> ");
        io::stdout().flush()?;
        let mut line = String::new();
        if stdin.lock().read_line(&mut line)? == 0 {
            println!();
            return Ok(());
        }
        let parts: Vec<_> = line.split_whitespace().collect();
        let Some(command) = parts.first().map(|word| word.to_ascii_lowercase()) else {
            continue;
        };
        match command.as_str() {
            "quit" | "q" | "exit" => return Ok(()),
            "help" | "?" => {
                println!("  Use set, clear, check, hint, solve, why, reset, or quit.");
            }
            "set" => match parse_move(&parts) {
                Ok((row, col, value)) => {
                    if given_at(row, col).is_some() {
                        println!(
                            "  r{}c{} is a fixed clue and cannot be changed.",
                            row + 1,
                            col + 1
                        );
                    } else {
                        moves.insert((row, col), value);
                        print_partial(&moves);
                    }
                }
                Err(message) => println!("  {message}"),
            },
            "clear" => match parse_cell(&parts) {
                Ok((row, col)) => {
                    if given_at(row, col).is_some() {
                        println!(
                            "  r{}c{} is a fixed clue and cannot be cleared.",
                            row + 1,
                            col + 1
                        );
                    } else if moves.remove(&(row, col)).is_some() {
                        print_partial(&moves);
                    } else {
                        println!("  That cell has no player move to clear.");
                    }
                }
                Err(message) => println!("  {message}"),
            },
            "check" => check(&moves)?,
            "hint" => hint(&moves)?,
            "solve" => solve(&moves)?,
            "why" | "rules" | "smt" => {
                println!("Generated SMT-LIB2 (the same text AY will solve):");
                println!("{}", script(&moves, None));
            }
            "reset" => {
                moves.clear();
                println!("  Player moves cleared.");
                print_partial(&moves);
            }
            _ => println!("  Unknown command. Type `help` for the command list."),
        }
    }
}

pub(super) fn print_live_result() -> Result<()> {
    let outputs = super::super::solve_smt_string(&script(&HashMap::new(), None))?;
    let verdict = outputs.first().map_or("(no result)", String::as_str);
    println!("  AY live solve: {verdict}");
    if verdict.trim() == "sat" {
        match outputs.get(1).and_then(|text| decode_model(text)) {
            Some(model) if validate(&model, &HashMap::new()) => {
                print_grid(&model);
                println!("  Independently rechecked: domains, clues, rows, columns, and boxes.");
            }
            _ => println!("  AY's SAT candidate failed the tutorial's independent checker."),
        }
    }
    Ok(())
}

fn parse_move(parts: &[&str]) -> Result<(usize, usize, i64), &'static str> {
    if parts.len() != 4 {
        return Err("usage: set ROW COL VALUE");
    }
    let row = board_number(parts[1]).ok_or("ROW must be 1, 2, 3, or 4")?;
    let col = board_number(parts[2]).ok_or("COL must be 1, 2, 3, or 4")?;
    let value = parts[3]
        .parse::<i64>()
        .ok()
        .filter(|value| (1..=4).contains(value))
        .ok_or("VALUE must be 1, 2, 3, or 4")?;
    Ok((row, col, value))
}

fn parse_cell(parts: &[&str]) -> Result<(usize, usize), &'static str> {
    if parts.len() != 3 {
        return Err("usage: clear ROW COL");
    }
    let row = board_number(parts[1]).ok_or("ROW must be 1, 2, 3, or 4")?;
    let col = board_number(parts[2]).ok_or("COL must be 1, 2, 3, or 4")?;
    Ok((row, col))
}

fn board_number(text: &str) -> Option<usize> {
    text.parse::<usize>()
        .ok()
        .filter(|value| (1..=4).contains(value))
        .map(|value| value - 1)
}

fn check(moves: &SudokuMoves) -> Result<()> {
    let outputs = super::super::solve_smt_string(&script(moves, None))?;
    match outputs.first().map(|output| output.trim()) {
        Some("sat") => {
            if outputs
                .get(1)
                .and_then(|text| decode_model(text))
                .is_some_and(|grid| validate(&grid, moves))
            {
                println!("  SAT: every current move extends to a complete board.");
            } else {
                println!("  AY's SAT candidate failed the tutorial's independent checker.");
            }
        }
        Some("unsat") => println!("  UNSAT: the moves contradict a clue or Sudoku rule."),
        Some("unknown") => println!("  UNKNOWN: do not treat the current board as valid."),
        Some(other) => println!("  Unexpected solver response: {other}"),
        None => println!("  AY produced no check-sat response."),
    }
    Ok(())
}

fn solve(moves: &SudokuMoves) -> Result<()> {
    let outputs = super::super::solve_smt_string(&script(moves, None))?;
    match outputs.first().map(|output| output.trim()) {
        Some("sat") => {
            let Some(grid) = outputs.get(1).and_then(|text| decode_model(text)) else {
                println!("  AY returned SAT, but the tutorial could not decode a complete grid.");
                return Ok(());
            };
            if validate(&grid, moves) {
                println!("  SAT: one independently validated completion is:");
                print_grid(&grid);
            } else {
                println!("  The returned model failed the tutorial's independent checker.");
            }
        }
        Some("unsat") => println!("  No completion exists for the current moves."),
        Some("unknown") => println!("  AY returned UNKNOWN; no completion is claimed."),
        Some(other) => println!("  Unexpected solver response: {other}"),
        None => println!("  AY produced no check-sat response."),
    }
    Ok(())
}

fn hint(moves: &SudokuMoves) -> Result<()> {
    let outputs = super::super::solve_smt_string(&script(moves, None))?;
    let Some(verdict) = outputs.first().map(|output| output.trim()) else {
        println!("  AY produced no check-sat response.");
        return Ok(());
    };
    if verdict != "sat" {
        match verdict {
            "unsat" => println!("  Clear a contradictory move before asking for a hint."),
            "unknown" => println!("  AY returned UNKNOWN, so the lab will not guess."),
            other => println!("  Unexpected solver response: {other}"),
        }
        return Ok(());
    }
    let Some(grid) = outputs.get(1).and_then(|text| decode_model(text)) else {
        println!("  The tutorial could not decode AY's candidate grid.");
        return Ok(());
    };
    if !validate(&grid, moves) {
        println!("  AY's candidate grid failed the tutorial's independent checker.");
        return Ok(());
    }

    for row in 0..4 {
        for col in 0..4 {
            if given_at(row, col).is_some() || moves.contains_key(&(row, col)) {
                continue;
            }
            let value = grid[row][col];
            let alternative = format!("(not (= r{}c{} {value}))", row + 1, col + 1);
            let probe = super::super::solve_smt_string(&script(moves, Some(&alternative)))?;
            if probe.first().is_some_and(|output| output.trim() == "unsat") {
                println!(
                    "  Forced hint: r{}c{} = {value}. AY proved every alternative impossible.",
                    row + 1,
                    col + 1
                );
                return Ok(());
            }
        }
    }

    for row in 0..4 {
        for col in 0..4 {
            if given_at(row, col).is_none() && !moves.contains_key(&(row, col)) {
                println!(
                    "  No forced cell was found. One continuation has r{}c{} = {},",
                    row + 1,
                    col + 1,
                    grid[row][col]
                );
                println!("  but another completion may choose differently.");
                return Ok(());
            }
        }
    }
    println!("  The board is complete. Use `solve` to validate it.");
    Ok(())
}

fn given_at(row: usize, col: usize) -> Option<i64> {
    GIVENS
        .iter()
        .find_map(|&((r, c), value)| (row == r && col == c).then_some(value))
}

fn script(moves: &SudokuMoves, extra_assertion: Option<&str>) -> String {
    let mut script = String::from("(set-logic QF_LIA)\n(set-option :produce-models true)\n");
    for row in 1..=4 {
        for col in 1..=4 {
            script.push_str(&format!("(declare-const r{row}c{col} Int)\n"));
            script.push_str(&format!(
                "(assert (and (<= 1 r{row}c{col}) (<= r{row}c{col} 4)))\n"
            ));
        }
    }
    for row in 1..=4 {
        script.push_str(&format!(
            "(assert (distinct r{row}c1 r{row}c2 r{row}c3 r{row}c4))\n"
        ));
    }
    for col in 1..=4 {
        script.push_str(&format!(
            "(assert (distinct r1c{col} r2c{col} r3c{col} r4c{col}))\n"
        ));
    }
    for box_row in [1, 3] {
        for box_col in [1, 3] {
            script.push_str(&format!(
                "(assert (distinct r{box_row}c{box_col} r{box_row}c{} r{}c{box_col} r{}c{}))\n",
                box_col + 1,
                box_row + 1,
                box_row + 1,
                box_col + 1
            ));
        }
    }
    for &((row, col), value) in &GIVENS {
        script.push_str(&format!("(assert (= r{}c{} {value}))\n", row + 1, col + 1));
    }
    let mut ordered: Vec<_> = moves.iter().collect();
    ordered.sort_unstable_by_key(|((row, col), _)| (*row, *col));
    for (&(row, col), value) in ordered {
        script.push_str(&format!("(assert (= r{}c{} {value}))\n", row + 1, col + 1));
    }
    if let Some(assertion) = extra_assertion {
        script.push_str("(assert ");
        script.push_str(assertion);
        script.push_str(")\n");
    }
    script.push_str("(check-sat)\n(get-model)\n");
    script
}

fn decode_model(model: &str) -> Option<SudokuGrid> {
    let mut values = HashMap::new();
    for line in model.lines() {
        if let Some((name, value)) = super::super::parse_define_fun(line.trim()) {
            if let Ok(value) = value.parse::<i64>() {
                values.insert(name, value);
            }
        }
    }
    let mut grid = [[0; 4]; 4];
    for (row, cells) in grid.iter_mut().enumerate() {
        for (col, cell) in cells.iter_mut().enumerate() {
            *cell = *values.get(&format!("r{}c{}", row + 1, col + 1))?;
        }
    }
    Some(grid)
}

fn validate(grid: &SudokuGrid, moves: &SudokuMoves) -> bool {
    let complete = |values: [i64; 4]| {
        let mut sorted = values;
        sorted.sort_unstable();
        sorted == [1, 2, 3, 4]
    };
    if !grid.iter().copied().all(complete) {
        return false;
    }
    for col in 0..4 {
        if !complete([grid[0][col], grid[1][col], grid[2][col], grid[3][col]]) {
            return false;
        }
    }
    for box_row in [0, 2] {
        for box_col in [0, 2] {
            if !complete([
                grid[box_row][box_col],
                grid[box_row][box_col + 1],
                grid[box_row + 1][box_col],
                grid[box_row + 1][box_col + 1],
            ]) {
                return false;
            }
        }
    }
    for &((row, col), value) in &GIVENS {
        if grid[row][col] != value {
            return false;
        }
    }
    moves
        .iter()
        .all(|(&(row, col), &value)| grid[row][col] == value)
}

fn print_partial(moves: &SudokuMoves) {
    println!("    +-----+-----+");
    for row in 0..4 {
        print!("    | ");
        for col in 0..4 {
            let value = given_at(row, col).or_else(|| moves.get(&(row, col)).copied());
            match value {
                Some(value) => print!("{value} "),
                None => print!(". "),
            }
            if col == 1 {
                print!("| ");
            }
        }
        println!("|");
        if row == 1 {
            println!("    +-----+-----+");
        }
    }
    println!("    +-----+-----+");
}

fn print_grid(grid: &SudokuGrid) {
    println!("    +-----+-----+");
    for (row, cells) in grid.iter().enumerate() {
        print!("    | ");
        for (col, value) in cells.iter().enumerate() {
            print!("{value} ");
            if col == 1 {
                print!("| ");
            }
        }
        println!("|");
        if row == 1 {
            println!("    +-----+-----+");
        }
    }
    println!("    +-----+-----+");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn script_contains_domains_groups_and_control_commands() {
        let script = script(&HashMap::new(), None);
        assert_eq!(script.matches("(declare-const r").count(), 16);
        assert_eq!(script.matches("(assert (distinct").count(), 12);
        assert!(script.contains("(assert (= r1c2 2))"));
        assert!(script.ends_with("(check-sat)\n(get-model)\n"));
    }

    #[test]
    fn validator_accepts_solution_and_rejects_bad_grid() {
        let valid = [[1, 2, 3, 4], [3, 4, 1, 2], [2, 1, 4, 3], [4, 3, 2, 1]];
        assert!(validate(&valid, &HashMap::new()));
        let mut invalid = valid;
        invalid[0][0] = 2;
        assert!(!validate(&invalid, &HashMap::new()));
    }

    #[test]
    fn player_move_is_included_and_checked() {
        let mut moves = HashMap::new();
        moves.insert((0, 0), 1);
        assert!(script(&moves, None).contains("(assert (= r1c1 1))"));
        let valid = [[1, 2, 3, 4], [3, 4, 1, 2], [2, 1, 4, 3], [4, 3, 2, 1]];
        assert!(validate(&valid, &moves));
        moves.insert((0, 0), 3);
        assert!(!validate(&valid, &moves));
    }
}
