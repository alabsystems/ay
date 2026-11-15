//! Parsing functions for WCNF MaxSAT files.
//!
//! The format has been specified in the [MaxSAT Evaluation 2022](https://maxsat-evaluations.github.io/2022/rules.html#input).
//!
//! **There is no header path in this parser at all.** The 2022 format has no
//! `p`-line, and [`WCNFToken`] deliberately has no header production — its
//! only tokens are comments, `h` and integers — so a pre-2022 `p wcnf <vars>
//! <clauses> <top>` line cannot lex (`p` matches no token) and the file is
//! refused as a syntax error before any clause is read. The defect-26 commit
//! message says this path "was probed and is already strict"; the mechanism is
//! stronger than that phrasing suggests: there is no header-line code to be
//! lenient in, so the CNF parser's header-truncation defect (wrong verdict 26,
//! `parse_header` dropping a clause carried on the `p cnf` line) has no WCNF
//! counterpart by construction, not by a check that could regress.

use logos::Logos;
use malachite_bigint::BigInt;
use num_traits::Zero;
use std::path::Path;
use veripb_formula::prelude::*;

use crate::{
    error::ParserError,
    io::{get_lines, read_line},
    wcnf_token::WCNFToken,
};

enum Weight {
    Hard,
    Soft(BigInt),
}

/// Parse a formula from a WCNF file. The WCNF format is described in the [MaxSAT Evaluation 2022](https://maxsat-evaluations.github.io/2022/rules.html#input).
///
/// This function creates a [`VarNameManager`] and calls the function [`parse_wcnf_from_file_given_var_manager()`]. See [`parse_wcnf_from_file_given_var_manager()`] for more details.
#[inline]
pub fn parse_wcnf_from_file<P>(filename: P) -> Result<(Formula, VarNameManager), ParserError>
where
    P: AsRef<Path>,
{
    let mut var_name_manager = VarNameManager::default();
    let formula = parse_wcnf_from_file_given_var_manager(filename, &mut var_name_manager)?;
    Ok((formula, var_name_manager))
}

/// Parse a formula from a WCNF file. The WCNF format is described in the [MaxSAT Evaluation 2022](https://maxsat-evaluations.github.io/2022/rules.html#input).
///
/// For converting MaxSAT problem into a pseudo-Boolean minimization problem, we use the following conventions:
/// - Hard clauses are constraints.
/// - For empty soft clauses, increase the objective constant.
/// - Unit soft clauses are added immediately to the objective with the weight as coefficient and the negated clause literal as the objective literal.
/// - For any other soft clauses `C`, introduce a relaxation variable `_b<i>`, where `<i>` means that this clause is the ith clause. Then `~_b<i>` is added with the weight as coefficient to the objective and the clause `C or ~_b<i>` is added as a constraint.
pub fn parse_wcnf_from_file_given_var_manager<P>(
    filename: P,
    var_name_manager: &mut VarNameManager,
) -> Result<Formula, ParserError>
where
    P: AsRef<Path>,
{
    let mut database = Formula::default();
    let lines = get_lines(&filename)?;
    let mut current_lits = Vec::new();
    let mut weight = None;
    let mut objective_terms = Vec::new();
    let mut objective_constant = BigInt::zero();
    let mut clause_counter: u64 = 0;

    for (line_number, line) in lines.enumerate() {
        // Do NOT swallow this error: ending the iteration here would silently
        // drop every remaining clause (bug A).
        let line = read_line(line, &filename, line_number)?;
        let mut lex = WCNFToken::lexer(&line);

        while let Some(token) = lex.next() {
            match token {
                Ok(WCNFToken::Integer) => {
                    if weight.is_none() {
                        // The lexer's `[+-]?[0-9]+` admits spellings (`+5`, leading zeros) that a
                        // `FromStr` implementation need not accept; the release profile aborts on
                        // panic, so an `unwrap()` here would kill the process on a well-formed
                        // file rather than report a parse error.
                        let coeff = lex.slice().parse().map_err(|_| {
                            ParserError::token_error_with_file(
                                lex.span(),
                                "weight",
                                filename.as_ref().to_string_lossy().to_string(),
                                line_number,
                            )
                        })?;
                        weight = Some(Weight::Soft(coeff));
                    } else {
                        let integer: i64 = lex.slice().parse::<i64>().map_err(|_| {
                            ParserError::token_error_with_file(
                                lex.span(),
                                "literal",
                                filename.as_ref().to_string_lossy().to_string(),
                                line_number,
                            )
                        })?;
                        match integer {
                            0 => {
                                clause_counter += 1;
                                match std::mem::take(&mut weight) {
                                    None => {
                                        return Err(ParserError::token_error_with_file(
                                            lex.span(),
                                            "weight",
                                            filename.as_ref().to_string_lossy().to_string(),
                                            line_number,
                                        ));
                                    }
                                    Some(Weight::Hard) => {
                                        let clause =
                                            Clause::from_unnormalized_lits(current_lits.clone());
                                        database.constraints.push(clause);
                                    }
                                    Some(Weight::Soft(coeff)) => {
                                        match current_lits.len() {
                                            0 => {
                                                objective_constant += coeff;
                                            }
                                            1 => {
                                                // Unit soft clauses are added directly to the objective.
                                                let mut unit_lit = current_lits.pop().unwrap();
                                                unit_lit.negate();
                                                objective_terms
                                                    .push(GeneralPBTerm::new(coeff, unit_lit));
                                            }
                                            _ => {
                                                let blocking_lit = Lit::from_var(
                                                    var_name_manager.add_by_name(
                                                        &(String::from("_b")
                                                            + (clause_counter)
                                                                .to_string()
                                                                .as_str()),
                                                    ),
                                                    true,
                                                );
                                                current_lits.push(blocking_lit);
                                                let clause = Clause::from_unnormalized_lits(
                                                    current_lits.clone(),
                                                );
                                                database.constraints.push(clause);
                                                objective_terms
                                                    .push(GeneralPBTerm::new(coeff, blocking_lit));
                                            }
                                        }
                                    }
                                }
                                current_lits.clear();
                            }
                            // Variable identity comes from the literal's *value*, never from its
                            // spelling. `WCNFToken::Integer` is `[+-]?[0-9]+`, so `1`, `01`, `001`
                            // and `+1` are all accepted and all denote variable 1 — but building
                            // the name out of `lex.slice()` interned four different variables,
                            // silently splitting one variable into several and relaxing the
                            // formula (the reachable error is a false `VERIFIED`, not a false
                            // rejection). The CNF parser next door already goes by the value, and
                            // `proof_format_overview.md` documents the value-based reading.
                            //
                            // `unsigned_abs()` is the wide-type step: `-integer` wraps for
                            // `integer == i64::MIN`, which is an accepted literal, and the release
                            // profile had no overflow checks when this was written.
                            _ => {
                                let name = format!("x{}", integer.unsigned_abs());
                                current_lits.push(Lit::from_var(
                                    var_name_manager.add_by_name(&name),
                                    integer < 0,
                                ));
                            }
                        }
                    }
                }
                Ok(WCNFToken::HardClause) => {
                    if weight.is_some() {
                        return Err(ParserError::token_error_with_file(
                            lex.span(),
                            "previous clause has to end before next weight",
                            filename.as_ref().to_string_lossy().to_string(),
                            line_number,
                        ));
                    }
                    weight = Some(Weight::Hard);
                }
                Ok(WCNFToken::Comment) => {}
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
    }

    // A clause (or a bare weight) still open at the end of the file means the
    // file ends mid-clause. Dropping it (as the parser used to) hands the
    // checker a formula that is strictly weaker than the real one (bug B).
    if !current_lits.is_empty() || weight.is_some() {
        return Err(ParserError::UnterminatedClause {
            filename: filename.as_ref().to_string_lossy().to_string(),
            num_lits: current_lits.len(),
        });
    }

    database.objective = Some(PBObjective::from_terms(
        objective_terms,
        objective_constant,
        false,
    ));

    Ok(database)
}
