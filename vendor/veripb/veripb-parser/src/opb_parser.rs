//! Parser for the OPB format as [specified by the PB competition 2024](https://www.cril.univ-artois.fr/PB24/OPBgeneral.pdf).
//!
//! Tokenization is performed using [`OPBToken`].

use std::path::Path;

use ahash::{AHashMap, AHashSet};
use logos::{Lexer, Logos};
use malachite_bigint::BigInt;
use num_traits::Zero;
use veripb_formula::prelude::*;

use crate::{
    error::ParserError,
    io::{get_lines, read_line},
    opb_token::OPBToken,
    terms::{Comparator, GenericTerms, OptionalConstraintPair, Reification, generate_constraints},
};

type OptionalConstraint = Option<PBConstraintEnum>;
type Constraint = PBConstraintEnum;

type PreservedSetType = Option<AHashSet<VarIdx>>;

/// Parse an OPB file into [`Formula`] of constraints and store the names of the variables in a [`VarNameManager`].
///
/// This function creates a [`VarNameManager`] and calls the function `parse_opb_from_file_given_var_manager()`. See `parse_opb_from_file_given_var_manager()` for more details.
#[inline]
pub fn parse_opb_from_file<P>(
    filename: P,
) -> Result<
    (
        Formula,
        VarNameManager,
        AHashMap<String, isize>,
        PreservedSetType,
    ),
    ParserError,
>
where
    P: AsRef<Path>,
{
    let mut var_name_manager = VarNameManager::default();
    let (formula, labels, preserved_vars) =
        parse_opb_from_file_given_var_manager(filename, &mut var_name_manager)?;
    Ok((formula, var_name_manager, labels, preserved_vars))
}

/// Parse an OPB file into [`Formula`] of constraints and store the names of the variables in a [`VarNameManager`].
///
/// Furthermore, labels for constraints are supported. The labels are returned as a mapping from a [`String`] to a constraint ID. The constraint IDs start at 1, hence the the constraint ID is offset by 1 to the constraints in the formula.
///
/// A line that stands for more than one constraint, i.e., an equality, carries one label for each of them, in the order in which they are loaded.
pub fn parse_opb_from_file_given_var_manager<P>(
    filename: P,
    var_name_manager: &mut VarNameManager,
) -> Result<(Formula, AHashMap<String, isize>, PreservedSetType), ParserError>
where
    P: AsRef<Path>,
{
    let mut formula = Formula::default();
    let mut labels = AHashMap::new();
    let mut preserved_vars = None;
    let lines = get_lines(&filename)?;

    for (line_number, line) in lines.enumerate() {
        // Do NOT swallow this error: ending the iteration here would silently
        // drop every remaining constraint (bug A). Upstream still reads the
        // lines with `map_while(Result::ok)`, which stops at the first line
        // that fails to read and checks the proof against the truncated
        // formula; that matters more now that `get_lines` also decodes
        // gzip/xz/zstd, where a corrupt stream surfaces as an `Err` in the
        // middle of the file rather than as a short read at its end.
        let line = read_line(line, &filename, line_number)?;
        let mut lex = OPBToken::lexer(&line);
        // `ParserError::add_file_and_line` is infallible in this fork: an error
        // that already carries a position is returned unchanged instead of
        // being dropped. Upstream's closure unwraps an `Option` here, which
        // would panic for any error that is not a bare token error, so the
        // closure is kept without the `unwrap()`.
        let add_file_and_line = |e: ParserError| {
            e.add_file_and_line(filename.as_ref().to_string_lossy().to_string(), line_number)
        };
        let mut token = lex.next();
        // A constraint can be preceded by one label for each constraint it stands for.
        let mut line_labels = Vec::new();
        while let Some(Ok(OPBToken::Label)) = token {
            line_labels.push(lex.slice().to_string());
            token = lex.next();
        }
        let result = if !line_labels.is_empty() {
            // Only a constraint can follow a label.
            let constraint = match token {
                Some(Ok(
                    first @ (OPBToken::Integer
                    | OPBToken::GreaterEqual
                    | OPBToken::LessEqual
                    | OPBToken::Equal
                    | OPBToken::Var
                    | OPBToken::Negation),
                )) => parse_opb_constraint(&mut lex, first, var_name_manager)
                    .map_err(add_file_and_line)?,
                Some(Err(_)) | Some(Ok(_)) | None => {
                    return Err(ParserError::token_error_with_file(
                        lex.span(),
                        "a literal, '>=', '<=', '=', or integer",
                        filename.as_ref().to_string_lossy().to_string(),
                        line_number,
                    ));
                }
            };
            // Each of the constraints the line stands for is named by its own label, in the order
            // in which they are loaded, so a line has to carry either no label or all of them.
            let constraint_count =
                usize::from(constraint.0.is_some()) + usize::from(constraint.1.is_some());
            if line_labels.len() != constraint_count {
                let label_count = line_labels.len();
                return Err(ParserError::token_error_with_file(
                    lex.span(),
                    &if constraint_count == 1 {
                        format!(
                            "a single label, since this line stands for one constraint, but found {label_count}"
                        )
                    } else {
                        format!(
                            "one label for each of the {constraint_count} constraints this line stands for, but found {label_count}"
                        )
                    },
                    filename.as_ref().to_string_lossy().to_string(),
                    line_number,
                ));
            }
            for (offset, label) in line_labels.into_iter().enumerate() {
                labels.insert(label, (formula.len() + 1 + offset) as isize);
            }
            Some(constraint)
        } else {
            match token {
                None | Some(Ok(OPBToken::Comment)) => continue,
                Some(Ok(first @ (OPBToken::Minimize | OPBToken::Maximize))) => {
                    // the development design notes §XPB Grammar:
                    //
                    //     xpb ::= {xpb_skip}, [xpb_objective], {xpb_skip | xpb_constraint}
                    //
                    // — at most one objective, and it precedes every constraint.
                    // The reader used to *assign* on `min:`/`max:` wherever it
                    // appeared, so a second objective silently replaced the
                    // first and an objective written after the constraints was
                    // accepted as if it led the file. That is the same "data
                    // silently dropped" shape as wrong verdicts 25 and 26 — not
                    // itself a wrong verdict, because under the grammar such a
                    // file is malformed and has no correct reading, but the only
                    // honest response to it is a refusal, not a quiet choice of
                    // which objective to keep. The independent second reader
                    // draws the same line on its own terms
                    // (`veripb-second-reader`, `read_opb`).
                    if formula.objective.is_some() {
                        return Err(ParserError::token_error_with_file(
                            lex.span(),
                            "at most one objective (the development design notes §XPB allows a \
                             single `min:`/`max:` line; a second one would silently \
                             replace the first)",
                            filename.as_ref().to_string_lossy().to_string(),
                            line_number,
                        ));
                    }
                    if !formula.constraints.is_empty() {
                        return Err(ParserError::token_error_with_file(
                            lex.span(),
                            "the objective before the first constraint \
                             (the development design notes §XPB: `xpb ::= {skip}, [objective], \
                             {skip | constraint}`)",
                            filename.as_ref().to_string_lossy().to_string(),
                            line_number,
                        ));
                    }
                    let is_maximization = first == OPBToken::Maximize;
                    formula.objective = Some(parse_opb_objective(
                        &mut lex,
                        var_name_manager,
                        is_maximization,
                    )?);
                    None
                }
                Some(Ok(OPBToken::Preserved)) => {
                    // A second `preserved:` list would silently replace the
                    // first — the same dropped-data shape as the objective
                    // above. The XPB grammar does not define `preserved:` at all
                    // (it is an extension this checker reads), so there is no
                    // grammar placement to restate here: the list stays legal
                    // anywhere in the file
                    // (`parse_refuses_a_second_preserved_list_but_not_a_late_one`
                    // pins that) — but only once.
                    if preserved_vars.is_some() {
                        return Err(ParserError::token_error_with_file(
                            lex.span(),
                            "at most one `preserved:` line (a second one would \
                             silently replace the first)",
                            filename.as_ref().to_string_lossy().to_string(),
                            line_number,
                        ));
                    }
                    preserved_vars = Some(
                        parse_preserved_vars(&mut lex, var_name_manager)
                            .map_err(add_file_and_line)?,
                    );
                    None
                }
                Some(Ok(
                    first @ (OPBToken::Integer
                    | OPBToken::GreaterEqual
                    | OPBToken::LessEqual
                    | OPBToken::Equal
                    | OPBToken::Var
                    | OPBToken::Negation),
                )) => Some(
                    parse_opb_constraint(&mut lex, first, var_name_manager)
                        .map_err(add_file_and_line)?,
                ),
                Some(Err(_)) | Some(Ok(_)) => {
                    return Err(ParserError::token_error_with_file(
                        lex.span(),
                        "'*', 'min:', 'max:', 'preserved:', a literal, '>=', '<=', '=', or integer",
                        filename.as_ref().to_string_lossy().to_string(),
                        line_number,
                    ));
                }
            }
        };
        // One line, one item. the development design notes makes the XPB format
        // line-oriented -- every production ends with optional *spaces* (which
        // do not include a newline) and then end-of-line -- but this loop lexed
        // a line, parsed one item and moved on, so anything after the first `;`
        // was silently discarded and the formula was checked against a strict
        // subset of itself. No error, no warning at any verbosity, and `f <n>`
        // could not catch it because `n` is compared against the truncated
        // count.
        //
        // `1 x1 >= 1 ; 1 ~x1 >= 1 ;` on one line is unsatisfiable and verified
        // as `s VERIFIED SATISFIABLE` at exit 0 under default flags; the same
        // two constraints on two lines were correctly refused. The objective
        // and `preserved:` lines had the same hole, and so did the independent
        // second reader -- so `--kernel-verify` reported the formula
        // cross-check as passing on exactly that input.
        //
        // Checked here rather than inside the item parsers because those are
        // shared with the proof parser, where a constraint is legitimately
        // followed by a witness or a hint.
        if lex.next().is_some() {
            return Err(ParserError::token_error_with_file(
                lex.span(),
                "end of line (a formula file holds one constraint, objective or \
                 `preserved:` list per line)",
                filename.as_ref().to_string_lossy().to_string(),
                line_number,
            ));
        }
        if let Some((geq_constraint, leq_constraint)) = result {
            if let Some(constraint) = geq_constraint {
                formula.constraints.push(constraint);
            }
            if let Some(constraint) = leq_constraint {
                formula.constraints.push(constraint);
            }
        }
    }

    Ok((formula, labels, preserved_vars))
}

fn parse_preserved_vars(
    lex: &mut Lexer<OPBToken>,
    var_name_manager: &mut VarNameManager,
) -> Result<AHashSet<VarIdx>, ParserError> {
    let mut vars = AHashSet::new();
    while let Some(token) = lex.next() {
        match token {
            Ok(OPBToken::Var) => vars.insert(var_name_manager.add_by_name(lex.slice())),
            Ok(OPBToken::Semicolon) => return Ok(vars),
            _ => return Err(ParserError::token_error(lex.span(), "variable or ';'")),
        };
    }
    Err(ParserError::token_error(lex.span(), "';'"))
}

/// Parse an objective specified in OPB format.
pub fn parse_opb_objective<V: VarNameRecorder>(
    lex: &mut Lexer<OPBToken>,
    var_name_manager: &mut V,
    is_maximization: bool,
) -> Result<PBObjective, ParserError> {
    let mut terms = Vec::new();
    let mut integer = BigInt::zero();
    match lex.next() {
        Some(Ok(OPBToken::Integer)) => integer = lex.slice().parse().unwrap(),
        Some(Ok(OPBToken::Semicolon)) | None => {
            return Ok(PBObjective::from_terms(terms, integer, is_maximization));
        }
        _ => return Err(ParserError::token_error(lex.span(), "integer or ';'")),
    }

    while let Some(token) = lex.next() {
        // Expect the next literal.
        let lit = match token {
            Ok(OPBToken::Var) => Lit::from_var(var_name_manager.add_by_name(lex.slice()), false),
            Ok(OPBToken::Negation) => {
                if lex.next() == Some(Ok(OPBToken::Var)) {
                    Lit::from_var(var_name_manager.add_by_name(lex.slice()), true)
                } else {
                    return Err(ParserError::token_error(lex.span(), "variable name"));
                }
            }
            Ok(OPBToken::Semicolon) => {
                return Ok(PBObjective::from_terms(terms, integer, is_maximization));
            }
            _ => return Err(ParserError::token_error(lex.span(), "literal or ';'")),
        };

        terms.push(GeneralPBTerm::new(integer, lit));

        // Expect the next integer or end.
        match lex.next() {
            Some(Ok(OPBToken::Integer)) => integer = lex.slice().parse().unwrap(),
            Some(Ok(OPBToken::Semicolon)) | None => {
                return Ok(PBObjective::from_terms(
                    terms,
                    BigInt::zero(),
                    is_maximization,
                ));
            }
            _ => return Err(ParserError::token_error(lex.span(), "integer or ';'")),
        }
    }

    Ok(PBObjective::from_terms(terms, integer, is_maximization))
}

/// Parse a single OPB constraint.
///
/// **Note:** Reification shorthands are an extension of the OPB format introduced with version 3
/// of the proof format and are not accepted here, as this function parses constraints that are
/// embedded in a version 2 proof.
pub fn parse_single_constraint<V: VarNameRecorder>(
    lex: &mut Lexer<OPBToken>,
    var_names: &mut V,
) -> Result<(Constraint, OptionalConstraint), ParserError> {
    let (geq_constraint, leq_constraint) = match lex.next() {
        Some(Ok(
            first @ (OPBToken::Integer
            | OPBToken::GreaterEqual
            | OPBToken::LessEqual
            | OPBToken::Equal),
        )) => parse_opb_constraint_dyn(lex, first, var_names, &Reification::None)?,
        _ => {
            return Err(ParserError::token_error(
                lex.span(),
                "'*', 'min:', '>=', '<=', '=', or integer",
            ));
        }
    };
    // A `<=` constraint is returned as the `<=` direction of a constraint pair, but it is a single
    // constraint.
    match geq_constraint {
        Some(geq_constraint) => Ok((geq_constraint, leq_constraint)),
        None => Ok((leq_constraint.unwrap(), None)),
    }
}

/// Parse an OPB constraint, which can be written using a reification shorthand.
///
/// **Note:** When this function is called the lexer has already parsed the first token of the
/// constraint, which is given as `first`.
fn parse_opb_constraint<V: VarNameRecorder>(
    lex: &mut Lexer<OPBToken>,
    first: OPBToken,
    var_name_manager: &mut V,
) -> Result<OptionalConstraintPair, ParserError> {
    // Only a reification shorthand starts with a literal, in which case the constraint that is
    // reified follows the implication arrow.
    let (first, reification) = match first {
        OPBToken::Var | OPBToken::Negation => {
            let reification = parse_reification(lex, first, var_name_manager)?;
            match lex.next() {
                Some(Ok(
                    token @ (OPBToken::Integer
                    | OPBToken::GreaterEqual
                    | OPBToken::LessEqual
                    | OPBToken::Equal),
                )) => (token, reification),
                _ => {
                    return Err(ParserError::token_error(
                        lex.span(),
                        "'>=', '<=', '=', or integer",
                    ));
                }
            }
        }
        first => (first, Reification::None),
    };
    parse_opb_constraint_dyn(lex, first, var_name_manager, &reification)
}

/// Parse the literals of a reification shorthand, i.e., the literals up to and including the arrow.
///
/// A right implication (`==>`) takes one or more literals, which are read as their conjunction, while a left implication (`<==`) and an equivalence (`<==>`) take exactly one literal.
///
/// **Note:** When this function is called the lexer has already parsed the first token, which should start a literal.
fn parse_reification<V: VarNameRecorder>(
    lex: &mut Lexer<OPBToken>,
    first: OPBToken,
    var_name_manager: &mut V,
) -> Result<Reification, ParserError> {
    let mut token = Some(Ok(first));
    let mut literals = Vec::new();
    loop {
        let literal = match token {
            Some(Ok(OPBToken::Var)) => {
                Lit::from_var(var_name_manager.add_by_name(lex.slice()), false)
            }
            Some(Ok(OPBToken::Negation)) => {
                if lex.next() == Some(Ok(OPBToken::Var)) {
                    Lit::from_var(var_name_manager.add_by_name(lex.slice()), true)
                } else {
                    return Err(ParserError::token_error(lex.span(), "variable name"));
                }
            }
            _ => {
                return Err(ParserError::token_error(
                    lex.span(),
                    if literals.len() == 1 {
                        "literal, '<==', '<==>', or '==>'"
                    } else {
                        "literal or '==>'"
                    },
                ));
            }
        };
        literals.push(literal);

        token = lex.next();
        match token {
            Some(Ok(OPBToken::RightImplication)) => return Ok(Reification::LitsImplIneq(literals)),
            // A left implication and an equivalence reify a single literal, so once the arrow has
            // been read the number of literals in front of it is either right or a syntax error.
            Some(Ok(OPBToken::LeftImplication)) => {
                return single_literal(lex, &literals, "'<=='").map(Reification::IneqImplLit);
            }
            Some(Ok(OPBToken::Equivalence)) => {
                return single_literal(lex, &literals, "'<==>'").map(Reification::Equivalence);
            }
            _ => {}
        }
    }
}

/// The single literal a reification shorthand named by `arrow` reifies, or an error naming the
/// shorthand if `literals` holds more than one.
fn single_literal(
    lex: &Lexer<OPBToken>,
    literals: &[Lit],
    arrow: &str,
) -> Result<Lit, ParserError> {
    match literals {
        [literal] => Ok(*literal),
        _ => Err(ParserError::token_error(
            lex.span(),
            &format!("'==>', since {arrow} reifies a single literal"),
        )),
    }
}

/// Helper function to parse the terms, the comparator and the degree of a constraint.
///
/// This function iteratively tries to parse the constraint as [`i64`], then [`i128`] and finally as [`BigInt`] to get a constraint that has a small as possible size. The function returns the [`PBConstraintEnum`]s that the constraint stands for, which can directly be added to a database.
///
/// The `reification` is the shorthand the constraint is written with, if any.
///
/// The `is_overflow_safe` calls below are load-bearing, not an optimization.
/// [`generate_constraints`] turns `... <= degree` into `... >= -degree` with a plain unary minus on
/// every coefficient and on the degree, and `-N::MIN` is not representable, so with overflow checks
/// off in the release profile that negation wrapped silently and turned an infeasible constraint
/// such as `1 x1 <= -9223372036854775808` into a trivially true one — a wrong verdict this fork
/// fixed by negating with `checked_sub`. The guard now lives one level up: a width is only used
/// when [`GenericTerms::is_overflow_safe`] holds, and that in turn requires the absolute value of
/// the degree and the sum of the absolute values of the coefficients to be representable in `N`, so
/// the negation cannot wrap. Widening to `i128` and then to [`BigInt`] is what makes the check
/// total. Do not drop or weaken these calls without restoring a checked negation in
/// [`crate::terms`].
///
/// **Note:** When this function is called the lexer has already parsed the first token of the constraint, which is given as `first` and is either an integer, in which case the constraint has terms, or the comparator of a constraint without terms.
fn parse_opb_constraint_dyn<V: VarNameRecorder>(
    lex: &mut Lexer<OPBToken>,
    first: OPBToken,
    var_name_manager: &mut V,
    reification: &Reification,
) -> Result<OptionalConstraintPair, ParserError> {
    // A left implication or an equivalence of an equality would state that the literal is implied by both directions of the equality, i.e., by a tautology, so it is not a reification of the equality and is rejected.
    let is_equality_allowed = matches!(
        reification,
        Reification::None | Reification::LitsImplIneq(_)
    );
    // A constraint without terms starts with the comparator, which is directly followed by the degree.
    let mut comparator = match first {
        OPBToken::GreaterEqual => Some(Comparator::GreaterEqual),
        OPBToken::LessEqual => Some(Comparator::LessEqual),
        OPBToken::Equal if is_equality_allowed => Some(Comparator::Equal),
        OPBToken::Equal => return Err(ParserError::token_error(lex.span(), "'>=' or '<='")),
        _ => None,
    };
    if comparator.is_some() {
        is_integer(lex)?;
    }
    // Whether a narrower attempt already added the degree to the terms.
    let mut is_degree_added = false;

    // Try to parse into i64 first.
    let mut terms_i64 = GenericTerms::<i64>::default();
    if comparator.is_none() {
        comparator = parse_opb_terms(lex, var_name_manager, &mut terms_i64, is_equality_allowed)?;
    }
    if let Some(comparator) = comparator {
        is_degree_added = lex
            .slice()
            .parse()
            .is_ok_and(|degree| terms_i64.checked_add_degree(&degree));
        if is_degree_added && terms_i64.is_overflow_safe(reification) {
            check_constraint_end(lex)?;
            return Ok(generate_constraints(terms_i64, comparator, reification));
        }
    }

    // Try to parse into i128 next.
    let mut terms_i128 = GenericTerms::<i128>::from(terms_i64);
    if comparator.is_none() {
        comparator = parse_opb_terms(lex, var_name_manager, &mut terms_i128, is_equality_allowed)?;
    }
    if let Some(comparator) = comparator {
        if !is_degree_added {
            is_degree_added = lex
                .slice()
                .parse()
                .is_ok_and(|degree| terms_i128.checked_add_degree(&degree));
        }
        if is_degree_added && terms_i128.is_overflow_safe(reification) {
            check_constraint_end(lex)?;
            return Ok(generate_constraints(terms_i128, comparator, reification));
        }
    }

    // BigInt always succeeds.
    let mut terms_big = GenericTerms::<BigInt>::from(terms_i128);
    let comparator = match comparator {
        Some(comparator) => comparator,
        None => {
            parse_opb_terms(lex, var_name_manager, &mut terms_big, is_equality_allowed)?.unwrap()
        }
    };
    if !is_degree_added {
        terms_big.checked_add_degree(&lex.slice().parse().unwrap());
    }
    check_constraint_end(lex)?;
    Ok(generate_constraints(terms_big, comparator, reification))
}

/// Helper function to parse terms with generic parameter `N`.
///
/// The function returns an [`Err`] if the tokenization failed. The function returns [`Ok(None)`] if a coefficient is larger than the largest or smaller than the smallest number of the type `N`. Hence, the caller of the function should take care of adjusting the size of the coefficients accordingly, in which case the lexer is left on the coefficient that did not fit so that parsing can be resumed with a wider type. Otherwise, the lexer is left on the degree.
///
/// If `is_equality_allowed` is `false`, then `=` is not accepted as the comparator of the constraint.
///
/// **Note:** When this function is called the lexer has already parsed the first token, which should be an integer.
#[inline]
fn parse_opb_terms<N: Int, V: VarNameRecorder>(
    lex: &mut Lexer<OPBToken>,
    var_name_manager: &mut V,
    terms: &mut GenericTerms<N>,
    is_equality_allowed: bool,
) -> Result<Option<Comparator>, ParserError> {
    let mut coeff: N = match lex.slice().parse() {
        Ok(integer) => integer,
        Err(_) => return Ok(None),
    };

    loop {
        // The sum tracked by `terms` is over the absolute values of the coefficients, so a
        // negative coefficient is subtracted from it rather than added to it.
        let is_coeff_added = if coeff.is_negative() {
            terms.checked_sub_coefficient(&coeff)
        } else {
            terms.checked_add_coefficient(&coeff)
        };
        if !is_coeff_added {
            return Ok(None);
        }
        let lit = match lex.next() {
            Some(Ok(OPBToken::Var)) => {
                Lit::from_var(var_name_manager.add_by_name(lex.slice()), false)
            }
            Some(Ok(OPBToken::Negation)) => {
                if lex.next() == Some(Ok(OPBToken::Var)) {
                    Lit::from_var(var_name_manager.add_by_name(lex.slice()), true)
                } else {
                    return Err(ParserError::token_error(lex.span(), "variable name"));
                }
            }
            _ => {
                return Err(ParserError::token_error(lex.span(), "literal"));
            }
        };
        terms.add_term(coeff, lit);

        coeff = match lex.next() {
            Some(Ok(OPBToken::GreaterEqual)) => {
                is_integer(lex)?;
                return Ok(Some(Comparator::GreaterEqual));
            }
            Some(Ok(OPBToken::LessEqual)) => {
                is_integer(lex)?;
                return Ok(Some(Comparator::LessEqual));
            }
            Some(Ok(OPBToken::Equal)) if is_equality_allowed => {
                is_integer(lex)?;
                return Ok(Some(Comparator::Equal));
            }
            Some(Ok(OPBToken::Integer)) => match lex.slice().parse() {
                Ok(integer) => integer,
                Err(_) => return Ok(None),
            },
            _ => {
                return Err(ParserError::token_error(
                    lex.span(),
                    "'>=', '<=', or integer",
                ));
            }
        };
    }
}

/// Check if the next token is an integer
///
/// The function returns an [`Err`] if the next token is not an integer.
#[inline]
fn is_integer(lex: &mut Lexer<OPBToken>) -> Result<(), ParserError> {
    if lex.next() != Some(Ok(OPBToken::Integer)) {
        return Err(ParserError::token_error(lex.span(), "integer"));
    }
    Ok(())
}

/// Check that the constraint ends with `;`.
///
/// This is deliberately *not* where "and nothing follows" is enforced, because
/// this function is shared with the proof parser, where a constraint is
/// routinely followed on the same line by a witness or a hint. The formula file
/// is line-oriented and the proof is not, so the check belongs to the formula
/// reader's line dispatcher; see `parse_opb_from_file_given_var_manager`. Its
/// doc comment used to claim the check happened here, and the gap was a wrong
/// verdict. the development design notes makes the XPB format line-oriented — a
/// constraint is followed by optional *spaces* (which do not include a newline)
/// and then end-of-line — but the reader lexes one line, parses one constraint
/// and moves on, so a second constraint written after the first `;` on the same
/// line was silently discarded. The formula was then checked against a strict
/// subset of itself, with no error and no warning at any verbosity, and `f <n>`
/// could not catch it because `n` is compared against the truncated count.
///
/// `1 x1 >= 1 ; 1 ~x1 >= 1 ;` on one line is unsatisfiable and verified as
/// `s VERIFIED SATISFIABLE` at exit 0 under default flags. The same two
/// constraints on two lines are correctly refused.
///
/// It also defeated the independent cross-check: `veripb-second-reader` has the
/// same shape, so `--kernel-verify` reported "1 formula constraint(s)
/// cross-checked against the file on disk; nothing outside the proved fragment"
/// on exactly that input. Both readers are fixed; see `read_opb` there.
#[inline]
fn check_constraint_end(lex: &mut Lexer<OPBToken>) -> Result<(), ParserError> {
    if lex.next() != Some(Ok(OPBToken::Semicolon)) {
        Err(ParserError::token_error(lex.span(), "';'"))?;
    }

    Ok(())
}
