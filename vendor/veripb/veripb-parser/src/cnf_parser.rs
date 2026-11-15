//! Parsing functions for DIMACS CNF format.
//!
//! The DIMACS CNF format is used to represent SAT formulas in CNF. It was first used in the 2nd DIMACS implementation challenge.
//!
//! Tokenization is performed using [`CNFToken`].

use logos::{Lexer, Logos};
use std::path::Path;
use veripb_formula::prelude::*;

use crate::{
    cnf_token::CNFToken,
    error::ParserError,
    io::{get_lines, read_line},
};

/// How strictly the `p cnf <vars> <clauses>` header is enforced.
///
/// A CNF file that was truncated at a clause boundary is syntactically
/// perfect; the only trace of the loss is that fewer clauses were read than
/// the header declares. Checking a proof against such a formula can produce a
/// wrong `SATISFIABLE` verdict, so the checker binary runs the parser with
/// [`CnfParserOptions::strict()`].
///
/// The default is *lenient* (mismatches are logged with [`log::warn!`]) purely
/// for backwards compatibility: DIMACS files with padded headers are common in
/// the wild, and this crate's public `parse_cnf_from_file` has always accepted
/// them.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct CnfParserOptions {
    /// Reject (rather than warn about) a `p cnf` header whose variable or
    /// clause count does not match the file contents.
    pub strict_header_counts: bool,
}

impl CnfParserOptions {
    /// Options that reject a header whose counts do not match the file.
    #[inline]
    pub fn strict() -> Self {
        Self {
            strict_header_counts: true,
        }
    }

    /// Options that only warn about a header whose counts do not match.
    #[inline]
    pub fn lenient() -> Self {
        Self {
            strict_header_counts: false,
        }
    }
}

/// Parse a formula from a DIMACS CNF file.
///
/// Header count mismatches are only warned about; see
/// [`parse_cnf_from_file_with_options`] and [`CnfParserOptions`].
///
/// Returns the formula and the size of the variable space it needs; see
/// [`parse_cnf_from_file_with_options`] for what that number is and is not.
#[inline]
pub fn parse_cnf_from_file<P>(filename: P) -> Result<(Formula, usize), ParserError>
where
    P: AsRef<Path>,
{
    parse_cnf_from_file_with_options(filename, CnfParserOptions::lenient())
}

/// Parse a formula from a DIMACS CNF file with explicit [`CnfParserOptions`].
///
/// The returned `usize` is `max(declared variable count, highest variable index used)` — the
/// size of the variable space a caller must cover, not the number the `p cnf` header declares.
/// Callers index dense per-variable structures by it and some of them do so with unchecked
/// accessors, so it must never be smaller than the largest index the file can produce; see the
/// comment at the return.
///
/// Both of those quantities are bounded, unconditionally and regardless of `options`, by
/// [`Lit::MAX_VAR_IDX`] (representability) and by [`MAX_DENSE_VAR_IDX`] (what the checker will
/// build dense tables for).
pub fn parse_cnf_from_file_with_options<P>(
    filename: P,
    options: CnfParserOptions,
) -> Result<(Formula, usize), ParserError>
where
    P: AsRef<Path>,
{
    let mut database = Formula::default();
    let mut num_vars = 0;
    let mut num_clauses = 0;
    let lines = get_lines(&filename)?;
    let mut parsed_header = false;
    let mut current_lits = Vec::new();
    // Highest variable index actually used by a literal, to be checked against
    // the variable count declared in the header.
    let mut max_var = 0;

    for (line_number, line) in lines.enumerate() {
        // Do NOT swallow this error: ending the iteration here would silently
        // drop every remaining clause (bug A).
        let line = read_line(line, &filename, line_number)?;
        let mut lex = CNFToken::lexer(&line);

        if parsed_header {
            while let Some(token) = lex.next() {
                match token {
                    Ok(CNFToken::Integer(Ok(integer))) => match integer {
                        0 => {
                            let clause = Clause::from_unnormalized_lits(current_lits.clone());
                            database.constraints.push(clause);
                            current_lits.clear();
                        }
                        // The variable index is the literal's magnitude. `unsigned_abs()` rather
                        // than `-integer`: negating `isize::MIN` wraps back to `isize::MIN` and
                        // before the release profile enabled overflow checks, the naive negation read
                        // the most negative literal as the index `2^63`.
                        _ => {
                            let var = integer.unsigned_abs();
                            // A variable index `Lit` cannot represent is rejected
                            // *unconditionally* — never gated on `strict_header_counts`. The
                            // header check is a truncation heuristic; letting it double as the
                            // guard for a sentinel collision is what made
                            // `--lenient-header-counts` a soundness switch.
                            if var > Lit::MAX_VAR_IDX {
                                return Err(ParserError::VariableIndexOutOfRange {
                                    filename: filename.as_ref().to_string_lossy().to_string(),
                                    line: line_number,
                                    index: var,
                                    max: Lit::MAX_VAR_IDX,
                                });
                            }
                            // ... and, also unconditionally, a variable index that is
                            // representable but too large to build a dense variable space for.
                            // The checker's tables are indexed by variable, so the cost of this
                            // literal is `Θ(var)` no matter how small the file is; see
                            // `MAX_DENSE_VAR_IDX`.
                            if var > MAX_DENSE_VAR_IDX {
                                return Err(ParserError::VariableSpaceTooLarge {
                                    filename: filename.as_ref().to_string_lossy().to_string(),
                                    line: line_number,
                                    index: var,
                                    max: MAX_DENSE_VAR_IDX,
                                });
                            }
                            max_var = max_var.max(var);
                            current_lits.push(Lit::from_var(var, integer < 0));
                        }
                    },
                    Ok(CNFToken::Integer(Err(_))) => {
                        return Err(ParserError::token_error_with_file(
                            lex.span(),
                            "64 bit integer",
                            filename.as_ref().to_string_lossy().to_string(),
                            line_number,
                        ));
                    }
                    Ok(CNFToken::Comment) => {}
                    _ => {
                        return Err(ParserError::token_error_with_file(
                            lex.span(),
                            "integer or comment",
                            filename.as_ref().to_string_lossy().to_string(),
                            line_number,
                        ));
                    }
                }
            }
        } else {
            match lex.next() {
                Some(Ok(CNFToken::ProblemHeader)) => {
                    let header = parse_header(&mut lex).map_err(|e| {
                        e.add_file_and_line(
                            filename.as_ref().to_string_lossy().to_string(),
                            line_number,
                        )
                    })?;
                    num_vars = header.0;
                    num_clauses = header.1;
                    // The declared variable count is the only other route to an unrepresentable
                    // index: callers size a variable-name table from it, and declaring a count
                    // above the representable range would otherwise let a literal that names an
                    // out-of-range variable satisfy the header check.
                    if num_vars > Lit::MAX_VAR_IDX {
                        return Err(ParserError::VariableIndexOutOfRange {
                            filename: filename.as_ref().to_string_lossy().to_string(),
                            line: line_number,
                            index: num_vars,
                            max: Lit::MAX_VAR_IDX,
                        });
                    }
                    // The declared count sizes the variable-name table on its own, so it needs
                    // the dense bound as well: `p cnf 4294967300 1` is a header consistent with
                    // its file, so the *strict* check waved it through and the run then asked
                    // for tables covering four billion variables and never came back.
                    if num_vars > MAX_DENSE_VAR_IDX {
                        return Err(ParserError::VariableSpaceTooLarge {
                            filename: filename.as_ref().to_string_lossy().to_string(),
                            line: line_number,
                            index: num_vars,
                            max: MAX_DENSE_VAR_IDX,
                        });
                    }
                    // The declared clause count is the other number this header hands to an
                    // allocator, and it is just as untrusted: `p cnf 1 999999999999999` asked
                    // for 96 PB of constraint storage and died inside the allocator (SIGABRT,
                    // no verdict) before a single clause had been read. The reservation is only
                    // ever an optimisation, so a request the allocator cannot meet is dropped
                    // rather than fatal -- the parser then grows the vector as it goes, exactly
                    // as it does for a header that under-declares.
                    database.try_reserve_exact(header.1);
                    parsed_header = true;
                }
                Some(Ok(CNFToken::Comment)) => {}
                _ => {
                    return Err(ParserError::token_error_with_file(
                        lex.span(),
                        "CNF header or comment",
                        filename.as_ref().to_string_lossy().to_string(),
                        line_number,
                    ));
                }
            }
        }
    }

    if !parsed_header {
        return Err(ParserError::NoHeader);
    }

    // A clause that was never terminated by `0` means the file ends mid-clause.
    // Dropping it (as the parser used to) hands the checker a formula that is
    // strictly weaker than the real one (bug B).
    if !current_lits.is_empty() {
        return Err(ParserError::UnterminatedClause {
            filename: filename.as_ref().to_string_lossy().to_string(),
            num_lits: current_lits.len(),
        });
    }

    check_header_count(
        &filename,
        options,
        "clauses",
        num_clauses,
        database.constraints.len(),
    )?;
    // Only an *under*-declared variable count is reported: the header is then wrong about the
    // file, which is the same truncation signal the clause count carries. It is no longer a
    // sizing hazard -- the returned count is `max(declared, used)`, so a caller's tables cover
    // every literal whether or not this check is enabled. Declaring more variables than are
    // used is normal and always allowed.
    if max_var > num_vars {
        check_header_count(&filename, options, "variables", num_vars, max_var)?;
    }

    // Return the size of the variable space the file actually needs, NOT the count its header
    // declares. Callers size dense per-variable structures from this number -- `src/lib.rs`
    // builds the variable-name table `x1..xN` from it, the checker sizes its `Assignment` from
    // that table, and `Assignment::{get,set}_lit_value_unchecked` then index a literal read
    // straight from this file with `get_unchecked`.
    //
    // Returning the declared count was an out-of-bounds read on the accept/reject path
    // (fixed 2026-08-24, defect found in round 4). Under `--lenient-header-counts` a file may
    // name a variable above `num_vars`, and every one of those indices was then out of bounds:
    //
    //     printf 'p cnf 1 1\n5 0\n'                      > a.cnf
    //     printf 'pseudo-Boolean proof version 3.0\nsol ~x5;\noutput NONE;\n\
    //             conclusion SAT : ~x5;\nend pseudo-Boolean proof;\n' > a.pbp
    //     veripb --lenient-header-counts a.cnf a.pbp
    //
    // printed `s VERIFIED SATISFIABLE` with exit 0 for an assignment that falsifies the only
    // clause of the formula, and the same input tripped
    // `debug_assert!(lit.get_var() < self.assignment.len())` in a debug build. Because the read
    // is undefined behaviour, the verdict was not even stable: the byte-identical upstream
    // parser at `4bb10c2c` rejects that input, and the `p cnf 1 2 / 5 0 / -5 0` spelling of the
    // same shortfall returns the *right* verdict by accident. None of those outcomes is a
    // guarantee, which is the whole reason this is closed rather than scored.
    //
    // The sparse-index cost that made `num_vars.max(max_var)` look unsafe on its own is handled
    // by the unconditional `MAX_DENSE_VAR_IDX` checks above, which refuse an index the checker
    // cannot build a dense variable space for -- including via the declared count, which could
    // reach the same blow-up under a *strict* header and used to hang there.
    Ok((database, num_vars.max(max_var)))
}

/// Report a mismatch between a count declared in the `p cnf` header and the
/// count actually found in the file, as an error or a warning depending on
/// `options`.
#[inline]
fn check_header_count<P>(
    filename: P,
    options: CnfParserOptions,
    kind: &'static str,
    declared: usize,
    actual: usize,
) -> Result<(), ParserError>
where
    P: AsRef<Path>,
{
    if declared == actual {
        return Ok(());
    }
    let error = ParserError::HeaderCountMismatch {
        filename: filename.as_ref().to_string_lossy().to_string(),
        kind,
        declared,
        actual,
    };
    if options.strict_header_counts {
        Err(error)
    } else {
        log::warn!("{error}");
        Ok(())
    }
}

/// Parse the problem header of an DIMACS CNF file.
#[inline]
fn parse_header(lex: &mut Lexer<CNFToken>) -> Result<(usize, usize), ParserError> {
    if let Some(Ok(CNFToken::Integer(Ok(num_vars)))) = lex.next()
        && let Some(Ok(CNFToken::Integer(Ok(num_clauses)))) = lex.next()
    {
        // The header owns its line: `p cnf <vars> <clauses>` and nothing else.
        // This returned after the two counts and the rest of the line was
        // dropped with it, so `p cnf 1 2 1 0` silently lost the clause `1 0`
        // -- and the count check could not catch it, because the declared 2
        // was compared against the 2 clauses that *survived*.
        // `{x1, ~x1, ~x1}` read as `{~x1, ~x1}`, and an unsatisfiable file
        // verified as `s VERIFIED SATISFIABLE` at exit 0. The same
        // one-item-per-line class as the OPB reader's defect, in the one
        // DIMACS line that is line-oriented -- clause data is a stream and may
        // legally share and span lines, but the header is not clause data.
        if lex.next().is_some() {
            return Err(ParserError::token_error(
                lex.span(),
                "end of line (the `p cnf <vars> <clauses>` header owns its line)",
            ));
        }
        return Ok((num_vars as usize, num_clauses as usize));
    }

    Err(ParserError::token_error(lex.span(), "integer in isize"))
}
