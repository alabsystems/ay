// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Small solution visualizers for common constraint-model shapes.
//!
//! The visualizer consumes SMT-LIB input plus a solver `(model ...)` response.
//! It is intentionally presentation-only: it does not influence solving or
//! validate constraints. Current recognition covers compact board models used
//! by common teaching and puzzle encodings:
//!
//! - N-Queens: integer variables named `q1..qN` or `q_1..q_N`, where each value
//!   is the queen column for that row.
//! - Sudoku-like grids: integer variables named `r1c1..rNcN`.

use std::collections::{BTreeMap, BTreeSet};

use ay_frontend::sexp::parse_sexps;
use ay_frontend::SExpr;

/// Output format for recognized solution visualizations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VisualizationFormat {
    /// Terminal-friendly ASCII art.
    Ascii,
    /// Self-contained SVG markup written to stdout by the CLI.
    Svg,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum RecognizedVisualization {
    NQueens(NQueensBoard),
    Sudoku(SudokuGrid),
}

impl RecognizedVisualization {
    fn kind(&self) -> &'static str {
        match self {
            Self::NQueens(_) => "n-queens",
            Self::Sudoku(_) => "sudoku",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct NQueensBoard {
    columns_by_row: Vec<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SudokuGrid {
    cells: Vec<Vec<String>>,
}

/// Render a recognized constraint solution as ASCII or SVG.
///
/// Returns `None` when the input/model pair does not match a supported board
/// shape or the model cannot be parsed as integer assignments.
#[must_use]
pub fn render_solution_visualization(
    input: &str,
    model: &str,
    format: VisualizationFormat,
) -> Option<String> {
    let values = parse_integer_model_values(model);
    if values.is_empty() {
        return None;
    }

    let recognized = detect_n_queens(input, &values)
        .map(RecognizedVisualization::NQueens)
        .or_else(|| detect_sudoku(&values).map(RecognizedVisualization::Sudoku))?;

    Some(match format {
        VisualizationFormat::Ascii => render_ascii(&recognized),
        VisualizationFormat::Svg => render_svg(&recognized),
    })
}

fn parse_integer_model_values(model: &str) -> BTreeMap<String, i64> {
    let Ok(sexps) = parse_sexps(model) else {
        return BTreeMap::new();
    };

    let mut out = BTreeMap::new();
    for sexp in &sexps {
        collect_define_fun_ints(sexp, &mut out);
    }
    out
}

fn collect_define_fun_ints(sexp: &SExpr, out: &mut BTreeMap<String, i64>) {
    let SExpr::List(items) = sexp else {
        return;
    };

    if items.first().and_then(SExpr::as_symbol) == Some("define-fun") && items.len() >= 5 {
        let Some(name) = items[1].as_symbol() else {
            return;
        };
        let no_args = matches!(&items[2], SExpr::List(args) if args.is_empty());
        let int_sort = items[3].as_symbol() == Some("Int");
        if no_args && int_sort {
            if let Some(value) = parse_i64_sexpr(&items[4]) {
                out.insert(unquote_symbol_name(name).to_string(), value);
            }
        }
        return;
    }

    for item in items {
        collect_define_fun_ints(item, out);
    }
}

fn parse_i64_sexpr(sexp: &SExpr) -> Option<i64> {
    match sexp {
        SExpr::Numeral(n) => n.parse().ok(),
        SExpr::List(items) if items.len() == 2 && items[0].is_symbol("-") => {
            parse_i64_sexpr(&items[1]).and_then(i64::checked_neg)
        }
        _ => None,
    }
}

fn detect_n_queens(input: &str, values: &BTreeMap<String, i64>) -> Option<NQueensBoard> {
    let mut rows = BTreeMap::new();
    for (name, value) in values {
        if let Some(row) = parse_queen_row(name) {
            rows.insert(row, *value);
        }
    }

    let n = rows.len();
    if n < 4 {
        return None;
    }
    if rows.keys().copied().ne(1..=n) {
        return None;
    }

    let one_based = rows.values().all(|&value| (1..=n as i64).contains(&value));
    let zero_based = rows.values().all(|&value| (0..n as i64).contains(&value));
    if !one_based && !zero_based {
        return None;
    }

    let mut seen = BTreeSet::new();
    let columns_by_row: Vec<usize> = rows
        .values()
        .map(|value| {
            if one_based {
                *value as usize
            } else {
                (*value + 1) as usize
            }
        })
        .inspect(|col| {
            seen.insert(*col);
        })
        .collect();

    if seen.len() != n {
        return None;
    }

    let hint = input.to_ascii_lowercase();
    let has_queen_hint = hint.contains("queen");
    if !has_queen_hint && !has_n_queens_diagonal_shape(&columns_by_row) {
        return None;
    }

    Some(NQueensBoard { columns_by_row })
}

fn has_n_queens_diagonal_shape(columns_by_row: &[usize]) -> bool {
    for (row_a, col_a) in columns_by_row.iter().enumerate() {
        for (row_b, col_b) in columns_by_row.iter().enumerate().skip(row_a + 1) {
            let row_delta = row_b - row_a;
            let col_delta = col_a.abs_diff(*col_b);
            if row_delta == col_delta {
                return false;
            }
        }
    }
    true
}

fn parse_queen_row(name: &str) -> Option<usize> {
    let name = unquote_symbol_name(name);
    let rest = name.strip_prefix("q_").or_else(|| name.strip_prefix('q'))?;
    parse_positive_usize(rest)
}

fn detect_sudoku(values: &BTreeMap<String, i64>) -> Option<SudokuGrid> {
    let mut cells = BTreeMap::new();
    for (name, value) in values {
        if let Some((row, col)) = parse_grid_cell(name) {
            cells.insert((row, col), *value);
        }
    }

    let n = cells.keys().map(|(row, col)| (*row).max(*col)).max()?;
    if n < 2 || cells.len() != n * n {
        return None;
    }

    for row in 1..=n {
        for col in 1..=n {
            let value = *cells.get(&(row, col))?;
            if !(1..=n as i64).contains(&value) {
                return None;
            }
        }
    }

    let mut grid = Vec::with_capacity(n);
    for row in 1..=n {
        let mut grid_row = Vec::with_capacity(n);
        for col in 1..=n {
            grid_row.push(cells.get(&(row, col))?.to_string());
        }
        grid.push(grid_row);
    }

    Some(SudokuGrid { cells: grid })
}

fn parse_grid_cell(name: &str) -> Option<(usize, usize)> {
    let name = unquote_symbol_name(name);
    let rest = name.strip_prefix('r')?;
    let c_index = rest.find('c')?;
    let row = parse_positive_usize(&rest[..c_index])?;
    let col = parse_positive_usize(&rest[c_index + 1..])?;
    Some((row, col))
}

fn parse_positive_usize(text: &str) -> Option<usize> {
    if text.is_empty() || !text.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let value = text.parse().ok()?;
    (value > 0).then_some(value)
}

fn unquote_symbol_name(name: &str) -> &str {
    name.strip_prefix('|')
        .and_then(|s| s.strip_suffix('|'))
        .unwrap_or(name)
}

fn render_ascii(visualization: &RecognizedVisualization) -> String {
    match visualization {
        RecognizedVisualization::NQueens(board) => {
            let n = board.columns_by_row.len();
            let mut cells = vec![vec![".".to_string(); n]; n];
            for (row, col) in board.columns_by_row.iter().enumerate() {
                cells[row][col - 1] = "Q".to_string();
            }
            let mut out = format!("; ay visualization: n-queens {n}x{n}\n");
            out.push_str(&render_ascii_grid(&cells));
            out
        }
        RecognizedVisualization::Sudoku(grid) => {
            let n = grid.cells.len();
            let mut out = format!("; ay visualization: sudoku {n}x{n}\n");
            out.push_str(&render_ascii_grid(&grid.cells));
            out
        }
    }
}

fn render_ascii_grid(cells: &[Vec<String>]) -> String {
    let width = cells
        .iter()
        .flat_map(|row| row.iter())
        .map(String::len)
        .max()
        .unwrap_or(1)
        .max(1);
    let cols = cells.first().map_or(0, Vec::len);
    let horizontal = ascii_horizontal_rule(cols, width);

    let mut out = String::new();
    out.push_str(&horizontal);
    for row in cells {
        out.push('|');
        for cell in row {
            out.push(' ');
            out.push_str(&format!("{cell:^width$}"));
            out.push(' ');
            out.push('|');
        }
        out.push('\n');
        out.push_str(&horizontal);
    }
    out
}

fn ascii_horizontal_rule(cols: usize, width: usize) -> String {
    let mut out = String::new();
    out.push('+');
    for _ in 0..cols {
        out.push_str(&"-".repeat(width + 2));
        out.push('+');
    }
    out.push('\n');
    out
}

fn render_svg(visualization: &RecognizedVisualization) -> String {
    match visualization {
        RecognizedVisualization::NQueens(board) => {
            let n = board.columns_by_row.len();
            let mut cells = vec![vec![String::new(); n]; n];
            for (row, col) in board.columns_by_row.iter().enumerate() {
                cells[row][col - 1] = "Q".to_string();
            }
            render_svg_grid(visualization.kind(), &cells, true)
        }
        RecognizedVisualization::Sudoku(grid) => {
            render_svg_grid(visualization.kind(), &grid.cells, false)
        }
    }
}

fn render_svg_grid(kind: &str, cells: &[Vec<String>], checkerboard: bool) -> String {
    let n = cells.len();
    let cell = 42usize;
    let width = n * cell;
    let height = n * cell;
    let mut out = format!(
        "<svg xmlns=\"http://www.w3.org/2000/svg\" data-ay-visualization=\"{}\" viewBox=\"0 0 {} {}\" width=\"{}\" height=\"{}\">\n",
        escape_xml(kind),
        width,
        height,
        width,
        height
    );
    out.push_str(&format!(
        "  <title>ay {} solution visualization</title>\n",
        escape_xml(kind)
    ));
    out.push_str("  <rect width=\"100%\" height=\"100%\" fill=\"#ffffff\"/>\n");

    for (row_idx, row) in cells.iter().enumerate() {
        for (col_idx, value) in row.iter().enumerate() {
            let x = col_idx * cell;
            let y = row_idx * cell;
            let fill = if checkerboard && (row_idx + col_idx) % 2 == 1 {
                "#e8edf3"
            } else {
                "#ffffff"
            };
            out.push_str(&format!(
                "  <rect x=\"{x}\" y=\"{y}\" width=\"{cell}\" height=\"{cell}\" fill=\"{fill}\" stroke=\"#334155\" stroke-width=\"1\"/>\n"
            ));
            if !value.is_empty() {
                out.push_str(&format!(
                    "  <text x=\"{}\" y=\"{}\" text-anchor=\"middle\" dominant-baseline=\"central\" font-family=\"ui-monospace, SFMono-Regular, Menlo, monospace\" font-size=\"24\" fill=\"#0f172a\">{}</text>\n",
                    x + cell / 2,
                    y + cell / 2 + 1,
                    escape_xml(value)
                ));
            }
        }
    }

    out.push_str("</svg>");
    out
}

fn escape_xml(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for ch in text.chars() {
        match ch {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&apos;"),
            _ => out.push(ch),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    const N_QUEENS_MODEL: &str = r#"(model
  (define-fun q1 () Int 2)
  (define-fun q2 () Int 4)
  (define-fun q3 () Int 1)
  (define-fun q4 () Int 3)
)"#;

    const SUDOKU_MODEL: &str = r#"(model
  (define-fun r1c1 () Int 1)
  (define-fun r1c2 () Int 2)
  (define-fun r2c1 () Int 2)
  (define-fun r2c2 () Int 1)
)"#;

    #[test]
    fn renders_n_queens_ascii() {
        let rendered =
            render_solution_visualization("; N-Queens", N_QUEENS_MODEL, VisualizationFormat::Ascii)
                .expect("n-queens visualization");

        assert!(rendered.contains("; ay visualization: n-queens 4x4"));
        assert!(rendered.contains("| . | Q | . | . |"));
        assert!(rendered.contains("| . | . | . | Q |"));
    }

    #[test]
    fn renders_sudoku_ascii() {
        let rendered = render_solution_visualization("", SUDOKU_MODEL, VisualizationFormat::Ascii)
            .expect("sudoku visualization");

        assert!(rendered.contains("; ay visualization: sudoku 2x2"));
        assert!(rendered.contains("| 1 | 2 |"));
        assert!(rendered.contains("| 2 | 1 |"));
    }

    #[test]
    fn renders_svg_with_kind_marker() {
        let rendered = render_solution_visualization("", SUDOKU_MODEL, VisualizationFormat::Svg)
            .expect("sudoku svg");

        assert!(rendered.starts_with("<svg "));
        assert!(rendered.contains("data-ay-visualization=\"sudoku\""));
        assert!(rendered.contains(">1</text>"));
    }

    #[test]
    fn rejects_non_board_model() {
        let rendered = render_solution_visualization(
            "",
            "(model (define-fun x () Int 1))",
            VisualizationFormat::Ascii,
        );

        assert!(rendered.is_none());
    }
}
