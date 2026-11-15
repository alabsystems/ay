//! Main parsing functions and structures for the VeriPB 3 parser.

use crate::error::ParserError;
use crate::io::MaybeCompressed;
use crate::pbp_parser::lexer::{IntegerParseMode, Lexer};
use crate::pbp_parser::proof_processor::ProofProcessor;
use crate::pbp_parser::utils::{PolToken, Position, Scope, Token};
use crate::terms::{
    Comparator, GenericTerms, OptionalConstraintPair, Reification, generate_constraints,
};
use ahash::AHashMap;
use malachite_bigint::{BigInt, Sign};
use num_traits::{Signed, identities::Zero};
use std::fs::File;
use std::io::BufRead;
use std::rc::Rc;
use veripb_formula::db_constraint::DBConstraint;
use veripb_formula::general_pb_term::GeneralPBTerm;
use veripb_formula::lit::Lit;
use veripb_formula::pb_objective::PBObjective;
use veripb_formula::prelude::PBConstraintEnum;
use veripb_formula::substitution::{Substitution, SubstitutionValue};
use veripb_formula::var_type::VarIdx;
use veripb_rules::prelude::*;

/// Settings for the parser.
pub struct ParserArgs {
    /// Show the progress bar for parsing the proof.
    pub show_progress: bool,
    /// Whether any form of tracing is enabled (`--trace`, `--trace-lines` or
    /// `--trace-ids`). This controls whether the proof file source is buffered
    /// for tracing; the per-rule decision of whether to actually print it is
    /// delegated to the [`ProofProcessor`].
    pub trace_enabled: bool,
    /// Whether the parser should store assertion annotations in the
    /// [`AssertionRule`] struct.
    pub store_assertion_annotations: bool,
}

/// VeriPB parser for the proof format version 3.
///
/// Each parsed rules is passed on to the [`ProofProcessor`], which handles each rule.
pub struct Parser<'a, P: ProofProcessor, R: BufRead> {
    lexer: Lexer<'a, R>,
    processor: &'a mut P,
    label_to_id: AHashMap<String, isize>,
    args: ParserArgs,
}

/// Construct a new parser for the proof file opened in the `reader` and handle each rule by the given [`ProofProcessor`] `processor`.
pub fn parse_proof<P: ProofProcessor>(
    file_size: Option<u64>,
    reader: &mut MaybeCompressed<File>,
    processor: &mut P,
    formula_labels: AHashMap<String, isize>,
    args: ParserArgs,
) -> Result<(), P::Error> {
    match reader {
        MaybeCompressed::Plain(r) => {
            Parser::new(file_size, r, processor, formula_labels, args).parse()
        }
        MaybeCompressed::Zstd(r) => {
            Parser::new(file_size, r, processor, formula_labels, args).parse()
        }
        MaybeCompressed::Gzip(r) => {
            Parser::new(file_size, r, processor, formula_labels, args).parse()
        }
        MaybeCompressed::Xz(r) => {
            Parser::new(file_size, r, processor, formula_labels, args).parse()
        }
    }
}

impl<'a, P: ProofProcessor, R: BufRead> Parser<'a, P, R> {
    /// Construct a new parser for the file opened in the `derivation_reader`.
    fn new(
        file_size: Option<u64>,
        derivation_reader: &'a mut R,
        processor: &'a mut P,
        formula_labels: AHashMap<String, isize>,
        args: ParserArgs,
    ) -> Self {
        Self {
            lexer: Lexer::new(file_size, derivation_reader, &args),
            processor,
            label_to_id: formula_labels,
            args,
        }
    }

    /// Initiate the parsing.
    fn parse(&mut self) -> Result<(), P::Error> {
        if self.args.show_progress {
            println!();
        };
        let token = self.lexer.get_next_token()?;
        self.proof(token)?;
        let token = self.optional_opb_whitespace()?;
        self.eof(token)
    }

    /// Trace the parsed rule, hand the rule of for processing to the [`ProofProcessor], and print the progress bar.
    #[inline]
    fn process_rule(&mut self, rule: VeriPBRule) -> Result<(), P::Error> {
        let line = self.lexer.get_line();
        if self.args.trace_enabled {
            // The proof file source has been buffered; only print it if this rule
            // is selected for tracing. Either way the buffer must be flushed so
            // that it does not carry over to the next traced rule.
            let do_print = self.processor.should_trace(line);
            self.lexer.flush_trace(do_print);
        }
        self.processor.process_rule(line, rule)?;
        if self.args.show_progress {
            let current = self.lexer.get_pos().pos as f32;
            match self.lexer.get_len() {
                Some(size) => print!(
                    "\x1B[?25lProgress: {:>6.2}%\x1B[?25h\r",
                    100. * current / size as f32
                ),
                None => print!("\x1B[?25lProgress: {current} bytes read\x1B[?25h\r"),
            }
        };
        Ok(())
    }

    /// Check if `token` is a [`Token::Space`] or [`Token::Tab`].
    fn is_space_or_tab(&mut self, token: &Token) -> bool {
        matches!(token, Token::Space(_) | Token::Tab(_))
    }

    /// Check if `token` is a whitespace ([`Token::Space`], [`Token::Tab`], [`Token::Eol`], or [`Token::Comment`]).
    fn is_white_space(&mut self, token: &Token) -> bool {
        matches!(
            token,
            Token::Space(_) | Token::Tab(_) | Token::Eol(_) | Token::Comment(_)
        )
    }

    /// Check if `token` is a constraint ID.
    fn is_constraint_id(&mut self, token: &Token) -> Result<bool, P::Error> {
        match token {
            Token::Integer64(Sign::NoSign, id) if *id != 0 => Ok(true),
            Token::Integer64(Sign::Minus, _) => Ok(true),
            Token::Label(_) => Ok(true),
            Token::Integer64(sign, _) => Err(self.lexer.report_error(
                format!(
                    "The constraint ID {} {}",
                    token,
                    if *sign == Sign::Plus {
                        "may not be prefixed with `+`"
                    } else {
                        "is not a valid constraint ID"
                    }
                ),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
            _ => Ok(false),
        }
    }

    /// Check if `token` is a variable.
    ///
    /// If `is_aux_allowed`, then the variable can be an auxiliary variable starting with `$`.
    fn is_variable(&mut self, token: &Token, is_aux_allowed: bool) -> Result<bool, P::Error> {
        match token {
            Token::Identifier(s) if s.len() > 1 => Ok(true),
            Token::Identifier(s) => Err(self.lexer.report_error(
                format!("Expected a variable of length at least two but only found `{s}`"),
                self.lexer.get_pos(),
                1,
            ))?,
            Token::AuxiliaryVariable(_) => Ok(is_aux_allowed),
            _ => Ok(false),
        }
    }

    /// Check if `token` is a specific type of variable.
    ///
    /// If `token` is a non-auxiliary variable, then return true iff `is_var_allowed`.
    /// If `token` is an auxiliary variable, then return true iff `is_aux_allowed`.
    fn is_any_variable(
        &mut self,
        token: &Token,
        is_var_allowed: bool,
        is_aux_allowed: bool,
    ) -> Result<bool, P::Error> {
        match token {
            Token::Identifier(s) if s.len() > 1 => Ok(is_var_allowed),
            Token::Identifier(s) if is_var_allowed => Err(self.lexer.report_error(
                format!("Expected a variable of length at least two but only found `{s}`"),
                self.lexer.get_pos(),
                1,
            ))?,
            Token::AuxiliaryVariable(_) => Ok(is_aux_allowed),
            _ => Ok(false),
        }
    }

    /// Check if `token` is a literal.
    ///
    /// If `is_aux_allowed`, then the variable of the literal can be an auxiliary variable.
    fn is_literal(&mut self, token: &Token, is_aux_allowed: bool) -> Result<bool, P::Error> {
        match token {
            Token::Tilde => Ok(true),
            token if self.is_variable(token, is_aux_allowed)? => Ok(true),
            _ => Ok(false),
        }
    }

    /// Parse grammar for proof.
    fn proof(&mut self, token: Token) -> Result<(), P::Error> {
        self.header(token)?;
        let token = self.optional_whitespace()?;
        let token = self.proof_lines(token, &Scope::TopLevel)?;
        self.footer(token)
    }

    /// Parse grammar for proof header.
    fn header(&mut self, token: Token) -> Result<(), P::Error> {
        self.keyword("pseudo-Boolean", token)?;
        self.space(1, true)?;
        let token = self.lexer.get_next_token()?;
        self.keyword("proof", token)?;
        self.space(1, true)?;
        let token = self.lexer.get_next_token()?;
        self.keyword("version", token)?;
        let token = self.space_or_tab(1, false)?;
        self.version(token)?;
        let token = self.space_or_tab(0, false)?;
        self.eol(token)?;
        self.process_rule(VeriPBRule::HeaderRule(HeaderRule))?;
        Ok(())
    }

    /// Parse at most an `expected` number of spaces. If the option `strict` is given, then exactly the number of `expected` spaces need to be parsed.
    fn space(&mut self, expected: usize, strict: bool) -> Result<(), P::Error> {
        match self.lexer.get_next_token()? {
            Token::Space(actual)
                if if strict {
                    actual == expected
                } else {
                    actual >= expected
                } =>
            {
                Ok(())
            }
            token => Err(self.lexer.report_error(
                format!(
                    "Expected {} {expected} space{} but found {}",
                    if strict { "exactly" } else { "at least" },
                    if expected == 1 { "" } else { "s" },
                    token,
                ),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        }
    }

    /// Parse at most an `expected` number of spaces or tabs. If the option `strict` is given, then exactly the number of `expected` spaces or tabs need to be parsed.
    fn space_or_tab(&mut self, expected: usize, strict: bool) -> Result<Token, P::Error> {
        let mut actual = 0;
        let mut token = self.lexer.get_next_token()?;
        while let Token::Space(count) | Token::Tab(count) = token {
            actual += count;
            token = self.lexer.get_next_token()?;
        }
        if if strict {
            actual == expected
        } else {
            actual >= expected
        } {
            Ok(token)
        } else {
            Err(self.lexer.report_error(
                format!(
                    "Expected {0} {expected} space{1}/character tabulator{1} but found {2}",
                    if strict { "exactly" } else { "at least" },
                    if expected == 1 { "" } else { "s" },
                    token,
                ),
                self.lexer.get_pos(),
                token.str_len(),
            ))?
        }
    }

    /// Parse the an end-of-line (eol) character.
    fn eol(&mut self, token: Token) -> Result<(), P::Error> {
        match token {
            Token::Eol(_) => Ok(()),
            token => Err(self.lexer.report_error(
                format!("Expected newline (`\\r`, `\\n` or `\\r\\n`) but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        }
    }

    /// Parse a whitespace character.
    ///
    /// If `is_mandatory` is true, then a whitespace character needs to be parsed.
    /// If `is_comments_allowed`, then a comment is accepted as a whitespace.
    fn whitespace(
        &mut self,
        is_mandatory: bool,
        is_comments_allowed: bool,
    ) -> Result<Token, P::Error> {
        let mut has_whitespace = false;
        let mut token = self.lexer.get_next_token()?;
        loop {
            match token {
                Token::Space(_) | Token::Tab(_) | Token::Eol(_) => has_whitespace = true,
                Token::Comment(_) if is_comments_allowed => has_whitespace = true,
                _ => break,
            }
            token = self.lexer.get_next_token()?;
        }
        // is_mandatory ==> has_whitespace
        if !is_mandatory || has_whitespace {
            Ok(token)
        } else {
            Err(self.lexer.report_error(
                format!("Expected mandatory whitespace but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?
        }
    }

    /// Parse a mandatory whitespace.
    fn mandatory_whitespace(&mut self) -> Result<Token, P::Error> {
        self.whitespace(true, true)
    }

    /// Parse an optional whitespace.
    fn optional_whitespace(&mut self) -> Result<Token, P::Error> {
        self.whitespace(false, true)
    }

    /// Parse an optional whitespace where comments are not allowed, which is used in OPB constraints.
    fn optional_opb_whitespace(&mut self) -> Result<Token, P::Error> {
        self.whitespace(false, false)
    }

    /// Parse a specific `keyword`.
    fn keyword(&mut self, keyword: &str, token: Token) -> Result<(), P::Error> {
        match token {
            Token::Identifier(s) if s == keyword => Ok(()),
            token => Err(self.lexer.report_error(
                format!("Expected `{keyword}` but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        }
    }

    /// Parse the version number of a VeriPB proof.
    fn version(&mut self, token: Token) -> Result<(), P::Error> {
        let pos = self.lexer.get_pos();
        let mut len = 0;
        let major = match token {
            Token::Integer64(Sign::NoSign, major) => {
                len += token.str_len();
                major
            }
            token @ Token::Integer64(_, _) => {
                return Err(self.lexer.report_error(
                    format!("The proof version {token} may not be prefixed with a sign"),
                    pos,
                    token.str_len(),
                ))?;
            }
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected an unsigned integer but found {token}"),
                    pos,
                    token.str_len(),
                ))?;
            }
        };
        match self.lexer.get_next_token()? {
            Token::Dot => len += 1,
            _ => return Err(self.lexer.report_error(
                format!("Expected proof version with major and minor version but only found major version `{major}`"),
                pos,
                len,
            ))?,
        };
        let minor = match self.lexer.get_next_token()? {
            Token::Integer64(Sign::NoSign, minor) => {
                len += token.str_len();
                minor
            },
            token @ Token::Integer64(_, _) => return Err(self.lexer.report_error(
                format!("The minor proof version {token} may not be prefixed with a sign"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
            Token::Space(_) |
            Token::Tab(_) |
            Token::Eol(_) |
            Token::Eof => return Err(self.lexer.report_error(
                format!("Expected proof version with major and minor version but only found `{major}.`"),
                pos,
                len,
            ))?,
            token => return Err(self.lexer.report_error(
                format!("Expected proof version with major and minor version but found `{major}.{}`", token.to_string().get(1..token.str_len() + 1).unwrap_or_default()),
                pos,
                len + token.str_len(),
            ))?,
        };
        if major > 3 || (major == 3 && minor > 0) {
            Err(self.lexer.report_error(
                format!("The current highest supported proof version is `3.0` but found version `{major}.{minor}`"),
                pos,
                len,
            ))?;
        } else if major == 2 && minor == 0 {
            self.processor.process_version(major, minor);
            Err(self.lexer.report_error(
                "Switch to 2.0 parser".to_string(),
                // Special position with all zeros to allow to fallback to old parser.
                Position {
                    pos: 0,
                    col: 1,
                    line: 0,
                },
                0,
            ))?;
        } else if major < 3 {
            Err(self.lexer.report_error(
                format!("Only proof version `3.0` (and `2.0`) are supported but found version `{major}.{minor}`"),
                pos,
                len,
            ))?;
        };
        self.processor.process_version(major, minor);
        Ok(())
    }

    /// Consume the `token` and check if the `token` is a colon `:`.
    fn colon(&mut self, token: Token) -> Result<(), P::Error> {
        match token {
            Token::Colon => Ok(()),
            token => Err(self.lexer.report_error(
                format!("Expected `:` but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        }
    }

    /// Consume the `token` and check if the `token` is a semicolon `;`.
    fn semicolon(&mut self, token: Token) -> Result<(), P::Error> {
        match token {
            Token::Semicolon => Ok(()),
            token => Err(self.lexer.report_error(
                format!("Expected `;` but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        }
    }

    /// Consume the `token` and check if the `token` is a colon `:` or semicolon `;` and return true if a semicolon is parsed.
    fn colon_or_semicolon(&mut self, token: Token) -> Result<bool, P::Error> {
        match token {
            Token::Colon => Ok(false),
            Token::Semicolon => Ok(true),
            token => Err(self.lexer.report_error(
                format!("Expected `:` or `;` but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        }
    }

    /// Parse and optional whitespace followed by a semicolon `;`.
    fn optional_white_space_semicolon(&mut self) -> Result<(), P::Error> {
        let token = self.optional_whitespace()?;
        self.semicolon(token)
    }

    /// Get the variable index of the current token.
    ///
    /// Aux vars and regular vars can be handled differently by the ProofProcessor
    /// via a flag.
    fn variable(&mut self, token: Token) -> Result<VarIdx, P::Error> {
        match token {
            Token::Identifier(variable) => {
                self.processor
                    .process_var_name(self.lexer.get_line(), &variable, false)
            }
            Token::AuxiliaryVariable(variable) => {
                self.processor
                    .process_var_name(self.lexer.get_line(), &variable, true)
            }
            _ => unreachable!(),
        }
    }

    /// Parse a list of variables.
    ///
    /// This function has the following parameters:
    /// - `is_var_allowed` specifies if non auxiliary variables are allowed in the list
    /// - `is_aux_allowed` specifies if auxiliary variables are allowed to be in the list
    fn variables(
        &mut self,
        token: Token,
        is_var_allowed: bool,
        is_aux_allowed: bool,
    ) -> Result<(Token, Vec<VarIdx>), P::Error> {
        let mut token = token;
        let mut variables = Vec::new();
        while token != Token::Semicolon {
            match token {
                token if self.is_any_variable(&token, is_var_allowed, is_aux_allowed)? => {
                    variables.push(self.variable(token)?)
                }
                token => {
                    Err(self.lexer.report_error(
                        format!(
                            "Expected {}{}{} but found {}",
                            if is_var_allowed { "a variable" } else { "" },
                            if is_var_allowed && is_aux_allowed {
                                " or "
                            } else {
                                ""
                            },
                            if is_aux_allowed {
                                "an auxiliary variable"
                            } else {
                                ""
                            },
                            token
                        ),
                        self.lexer.get_pos(),
                        token.str_len(),
                    ))?;
                }
            };
            token = match self.lexer.get_next_token()? {
                token if self.is_white_space(&token) => self.optional_whitespace()?,
                Token::Semicolon => Token::Semicolon,
                token => return Err(self.lexer.report_error(
                    format!("Expected mandatory whitespace (before the next variable) or `;` but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?,
            };
        }
        Ok((Token::Semicolon, variables))
    }

    /// Parse a literal.
    ///
    /// If `is_aux_allowed`, then the variable of the literal can be an auxiliary variable.
    fn literal(&mut self, token: Token, is_aux_allowed: bool) -> Result<Lit, P::Error> {
        let (token, is_positive) = if Token::Tilde == token {
            (self.lexer.get_next_token()?, false)
        } else {
            (token, true)
        };
        match token {
            token if self.is_variable(&token, is_aux_allowed)? => {
                Ok(Lit::from_var(self.variable(token)?, !is_positive))
            }
            token if !is_positive => Err(self.lexer.report_error(
                format!("Expected a variable after `~` to form a literal but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
            token => Err(self.lexer.report_error(
                format!("Expected a literal but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        }
    }

    /// Parse a list of literals.
    ///
    /// If `is_aux_allowed`, then the variable of the literal can be an auxiliary variable. If `is_colon_ending`, then the list is expected to end with a colon and if `is_reification_ending`, then the list is expected to end with a reification arrow (`==>` or `<==`).
    fn literals(
        &mut self,
        token: Token,
        is_aux_allowed: bool,
        is_colon_ending: bool,
        is_reification_ending: bool,
    ) -> Result<(Token, Vec<Lit>), P::Error> {
        let mut token = token;
        let mut count = 0;
        let mut literals = Vec::new();
        loop {
            match token {
                token if self.is_literal(&token, is_aux_allowed)? => {
                    literals.push(self.literal(token, is_aux_allowed)?);
                }
                token => {
                    Err(self.lexer.report_error(
                        format!(
                            "Expected a literal{} but found {}",
                            if is_reification_ending {
                                if count > 1 {
                                    " or `==>`"
                                } else {
                                    ", `<==` or `==>`"
                                }
                            } else if is_colon_ending {
                                ", `:` or `;`"
                            } else {
                                " or `;`"
                            },
                            token
                        ),
                        self.lexer.get_pos(),
                        token.str_len(),
                    ))?;
                }
            };
            count += 1;
            token = match self.lexer.get_next_token()? {
                token if self.is_white_space(&token) => self.optional_whitespace()?,
                Token::Colon if is_colon_ending && !is_reification_ending => Token::Colon,
                Token::Semicolon if !is_reification_ending => Token::Semicolon,
                Token::LeftImplication if is_reification_ending && count == 1 => {
                    Token::LeftImplication
                }
                Token::RightImplication if is_reification_ending => Token::RightImplication,
                token => return Err(self.lexer.report_error(
                    format!(
                        "Expected mandatory whitespace (before the next literal){} but found {}",
                        if is_reification_ending {
                            if count > 1 {
                                " or `==>`"
                            } else {
                                ", `<==` or `==>`"
                            }
                        } else if is_colon_ending {
                            ", `:` or `;`"
                        } else {
                            " or `;`"
                        },
                        token
                    ),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?,
            };
            if if is_reification_ending {
                (token == Token::LeftImplication && count == 1) || token == Token::RightImplication
            } else {
                token == Token::Semicolon || (is_colon_ending && token == Token::Colon)
            } {
                return Ok((token, literals));
            };
        }
    }

    /// Parse an objective function.
    ///
    /// If `is_colon_ending`, then the objective might end with a colon.
    /// If `is_opb`, then the objective can not contain any comments as comments.
    fn objective(
        &mut self,
        token: Token,
        is_colon_ending: bool,
        is_opb: bool,
    ) -> Result<(Token, PBObjective), P::Error> {
        let mut is_empty = true;
        let mut token = token;
        let mut coefficient = None;
        let mut terms = Vec::new();
        while let Token::IntegerAny(_, integer) = token {
            coefficient = Some(integer);
            is_empty = false;
            token = self.lexer.get_next_token()?;
            token = match token {
                token if !is_opb && self.is_white_space(&token) => self.optional_whitespace()?,
                token if is_opb && self.is_space_or_tab(&token) => self.space_or_tab(0, false)?,
                Token::Colon if is_colon_ending => break,
                Token::Semicolon => break,
                token => {
                    return Err(self.lexer.report_error(
                        format!(
                            "Expected mandatory {} (before the literal){} or `;` but found {}",
                            if is_opb {
                                "spaces/character tabulators"
                            } else {
                                "whitespace"
                            },
                            if is_colon_ending { ", `:`" } else { "" },
                            token
                        ),
                        self.lexer.get_pos(),
                        token.str_len(),
                    ))?;
                }
            };
            let literal = match token {
                Token::Colon if is_colon_ending => break,
                Token::Semicolon => break,
                token => self.literal(token, !is_opb)?,
            };
            terms.push(GeneralPBTerm::new(coefficient.unwrap(), literal));
            coefficient = None;
            token = if is_opb {
                self.space_or_tab(0, false)?
            } else {
                self.optional_whitespace()?
            };
        }
        self.lexer.disable_dynamic_integer_parse_mode();
        let objective =
            PBObjective::from_terms(terms, coefficient.unwrap_or_else(BigInt::zero), false);
        match token {
            token if is_empty => Err(self.lexer.report_error(
                format!("Expected a coefficient (signed integer) but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
            Token::Colon if is_colon_ending => Ok((Token::Colon, objective)),
            Token::Semicolon => Ok((Token::Semicolon, objective)),
            token => Err(self.lexer.report_error(
                format!(
                    "Expected mandatory {} (before the next coefficient){} or `;` but found {}",
                    if is_opb {
                        "spaces/character tabulators"
                    } else {
                        "whitespace"
                    },
                    if is_colon_ending { ", `:`" } else { "" },
                    token
                ),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        }
    }

    /// Parse an OPB objective.
    fn opb_objective(&mut self, token: Token) -> Result<(Token, Option<PBObjective>), P::Error> {
        let (token, objective) = self.objective(token, false, true)?;
        Ok((token, Some(objective)))
    }

    /// Parse a reification/implication constraint (a constraint containing `==>` or `<==`).
    fn reification(&mut self, token: Token) -> Result<(Token, Reification), P::Error> {
        let (token, literals) = self.literals(token, true, false, true)?;
        let reification = if token == Token::RightImplication {
            Reification::LitsImplIneq(literals)
        } else {
            // A left implication reifies a single literal, which `literals` has checked.
            Reification::IneqImplLit(literals[0])
        };
        let token = self.optional_whitespace()?;
        Ok((token, reification))
    }

    /// Parse terms with 64-bit coefficients.
    ///
    /// If `is_opb`, then comments are not considered whitespace.
    /// If `is_eq_allowed`, then the terms can be terminated by and equals sign `=`.
    fn terms_64(
        &mut self,
        mut token: Token,
        is_opb: bool,
        is_eq_allowed: bool,
        mut terms: GenericTerms<i64>,
    ) -> Result<(Token, Option<GenericTerms<i64>>), P::Error> {
        loop {
            match token {
                Token::Integer64(sign, coefficient) => {
                    let is_coeff_added = if coefficient.is_negative() {
                        terms.checked_sub_coefficient(&coefficient)
                    } else {
                        terms.checked_add_coefficient(&coefficient)
                    };
                    if !is_coeff_added {
                        self.lexer.set_integer_parse_mode(IntegerParseMode::Bits128);
                        return Ok((
                            Token::Integer128(sign, i128::from(coefficient)),
                            Some(terms),
                        ));
                    };
                    token = if is_opb {
                        self.space_or_tab(1, false)?
                    } else {
                        self.mandatory_whitespace()?
                    };
                    let literal = self.literal(token, !is_opb)?;
                    terms.add_term(coefficient, literal);
                }
                token => return Ok((token, Some(terms))),
            };
            token = match self.lexer.get_next_token()? {
                token if !is_opb && self.is_white_space(&token) => self.optional_whitespace()?,
                token if is_opb && self.is_space_or_tab(&token) => self.space_or_tab(0, false)?,
                Token::GreaterEqual => return Ok((Token::GreaterEqual, Some(terms))),
                Token::LessEqual => return Ok((Token::LessEqual, Some(terms))),
                Token::Equal if is_eq_allowed => return Ok((Token::Equal, Some(terms))),
                token => return Err(self.lexer.report_error(
                    format!(
                        "Expected mandatory whitespace (before the next coefficient),{} `>=` or `<=` but found {}",
                        if is_eq_allowed {" `=`,"} else {""},
                        token
                    ),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?,
            };
        }
    }

    /// Parse terms with 128-bit coefficients.
    ///
    /// If `is_opb`, then comments are not considered whitespace.
    /// If `is_eq_allowed`, then the terms can be terminated by and equals sign `=`.
    fn terms_128(
        &mut self,
        mut token: Token,
        is_opb: bool,
        is_eq_allowed: bool,
        mut terms: GenericTerms<i128>,
    ) -> Result<(Token, Option<GenericTerms<i128>>), P::Error> {
        loop {
            match token {
                Token::Integer128(sign, coefficient) => {
                    let is_coeff_added = if coefficient.is_negative() {
                        terms.checked_sub_coefficient(&coefficient)
                    } else {
                        terms.checked_add_coefficient(&coefficient)
                    };
                    if !is_coeff_added {
                        self.lexer.set_integer_parse_mode(IntegerParseMode::BitsAny);
                        return Ok((
                            Token::IntegerAny(sign, BigInt::from(coefficient)),
                            Some(terms),
                        ));
                    };
                    token = if is_opb {
                        self.space_or_tab(1, false)?
                    } else {
                        self.mandatory_whitespace()?
                    };
                    let literal = self.literal(token, !is_opb)?;
                    terms.add_term(coefficient, literal);
                }
                token => return Ok((token, Some(terms))),
            };
            token = match self.lexer.get_next_token()? {
                token if !is_opb && self.is_white_space(&token) => self.optional_whitespace()?,
                token if is_opb && self.is_space_or_tab(&token) => self.space_or_tab(0, false)?,
                Token::GreaterEqual => return Ok((Token::GreaterEqual, Some(terms))),
                Token::LessEqual => return Ok((Token::LessEqual, Some(terms))),
                Token::Equal if is_eq_allowed => return Ok((Token::Equal, Some(terms))),
                token => return Err(self.lexer.report_error(
                    format!(
                        "Expected mandatory whitespace (before the next coefficient),{} `>=` or `<=` but found {}",
                        if is_eq_allowed {" `=`,"} else {""},
                        token
                    ),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?,
            };
        }
    }

    /// Parse terms with arbitrary sized coefficients.
    ///
    /// If `is_opb`, then comments are not considered whitespace.
    /// If `is_eq_allowed`, then the terms can be terminated by and equals sign `=`.
    fn terms_any(
        &mut self,
        mut token: Token,
        is_opb: bool,
        is_eq_allowed: bool,
        mut terms: GenericTerms<BigInt>,
    ) -> Result<(Token, Option<GenericTerms<BigInt>>), P::Error> {
        loop {
            match token {
                Token::IntegerAny(_, coefficient) => {
                    if coefficient.is_negative() {
                        terms.checked_sub_coefficient(&coefficient);
                    } else {
                        terms.checked_add_coefficient(&coefficient);
                    }
                    token = if is_opb {
                        self.space_or_tab(1, false)?
                    } else {
                        self.mandatory_whitespace()?
                    };
                    let literal = self.literal(token, !is_opb)?;
                    terms.add_term(coefficient, literal);
                }
                token => return Ok((token, Some(terms))),
            };
            token = match self.lexer.get_next_token()? {
                token if !is_opb && self.is_white_space(&token) => self.optional_whitespace()?,
                token if is_opb && self.is_space_or_tab(&token) => self.space_or_tab(0, false)?,
                Token::GreaterEqual => return Ok((Token::GreaterEqual, Some(terms))),
                Token::LessEqual => return Ok((Token::LessEqual, Some(terms))),
                Token::Equal if is_eq_allowed => return Ok((Token::Equal, Some(terms))),
                token => return Err(self.lexer.report_error(
                    format!(
                        "Expected mandatory whitespace (before the next coefficient),{} `>=` or `<=` but found {}",
                        if is_eq_allowed {" `=`,"} else {""},
                        token
                    ),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?,
            };
        }
    }

    /// Parse a constraint.
    ///
    /// If `is_opb`, then comments are not considered whitespace.
    /// If `is_eq_allowed`, then the constraint can have an equal sign `=` as an comparator.
    fn constraint(
        &mut self,
        token: Token,
        is_opb: bool,
        is_eq_allowed: bool,
    ) -> Result<OptionalConstraintPair, P::Error> {
        // A constraint that starts with a literal is written with a reification shorthand, so read
        // the literals and the `==>` or `<==` that follows them.
        let (mut token, reification) = if !is_opb && self.is_literal(&token, true)? {
            self.reification(token)?
        } else {
            (token, Reification::None)
        };
        let mut terms_64: Option<GenericTerms<i64>> = Some(GenericTerms::<i64>::default());
        let mut terms_128: Option<GenericTerms<i128>> = None;
        let mut terms_any: Option<GenericTerms<BigInt>> = None;
        (token, terms_64) = self.terms_64(token, is_opb, is_eq_allowed, terms_64.unwrap())?;
        if let Token::Integer128(_, _) = token {
            (terms_64, (token, terms_128)) = (
                None,
                self.terms_128(
                    token,
                    is_opb,
                    is_eq_allowed,
                    GenericTerms::<i128>::from(terms_64.unwrap()),
                )?,
            );
        };
        if let Token::IntegerAny(_, _) = token {
            if terms_64.is_some() {
                (terms_64, (token, terms_any)) = (
                    None,
                    self.terms_any(
                        token,
                        is_opb,
                        is_eq_allowed,
                        GenericTerms::<BigInt>::from(terms_64.unwrap()),
                    )?,
                );
            } else {
                (terms_128, (token, terms_any)) = (
                    None,
                    self.terms_any(
                        token,
                        is_opb,
                        is_eq_allowed,
                        GenericTerms::<BigInt>::from(terms_128.unwrap()),
                    )?,
                );
            }
        };
        let comparator =
            match token {
                Token::GreaterEqual => Comparator::GreaterEqual,
                Token::LessEqual => Comparator::LessEqual,
                Token::Equal if is_eq_allowed => Comparator::Equal,
                token => return Err(self.lexer.report_error(
                    format!(
                        "Expected {}a coefficient (signed integer),{} `>=` or `<=` but found {}",
                        if !is_opb && reification == Reification::None {
                            "a literal, "
                        } else {
                            ""
                        },
                        if is_eq_allowed { " `=`," } else { "" },
                        token
                    ),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?,
            };
        token = if is_opb {
            self.space_or_tab(0, false)?
        } else {
            self.optional_whitespace()?
        };
        match token {
            Token::Integer64(_, _) | Token::Integer128(_, _) | Token::IntegerAny(_, _) => {}
            ref token => {
                Err(self.lexer.report_error(
                    format!("Expected a coefficient (signed integer) but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        if let Token::Integer64(sign, degree) = token {
            let mut terms = terms_64.unwrap();
            if terms.checked_add_degree(&degree) {
                terms_64 = Some(terms);
            } else {
                token = Token::Integer128(sign, i128::from(degree));
                (terms_64, terms_128) = (None, Some(GenericTerms::<i128>::from(terms)));
            };
        };
        if let Token::Integer128(sign, degree) = token {
            if terms_64.is_some() {
                (terms_64, terms_128) = (None, Some(GenericTerms::<i128>::from(terms_64.unwrap())));
            };
            let mut terms = terms_128.unwrap();
            if terms.checked_add_degree(&degree) {
                terms_128 = Some(terms);
            } else {
                token = Token::IntegerAny(sign, BigInt::from(degree));
                (terms_128, terms_any) = (None, Some(GenericTerms::<BigInt>::from(terms)));
            };
        };
        if let Token::IntegerAny(_, degree) = token {
            if terms_64.is_some() {
                (terms_64, terms_any) =
                    (None, Some(GenericTerms::<BigInt>::from(terms_64.unwrap())));
            } else if terms_128.is_some() {
                (terms_128, terms_any) =
                    (None, Some(GenericTerms::<BigInt>::from(terms_128.unwrap())));
            };
            let mut terms = terms_any.unwrap();
            terms.checked_add_degree(&degree);
            terms_any = Some(terms);
        };
        if terms_64.is_some() {
            let terms = terms_64.unwrap();
            if terms.is_overflow_safe(&reification) {
                terms_64 = Some(terms);
            } else {
                (terms_64, terms_128) = (None, Some(GenericTerms::<i128>::from(terms)));
            };
        };
        if terms_128.is_some() {
            let terms = terms_128.unwrap();
            if terms.is_overflow_safe(&reification) {
                terms_128 = Some(terms);
            } else {
                (terms_128, terms_any) = (None, Some(GenericTerms::<BigInt>::from(terms)));
            };
        };
        let result = match () {
            _ if terms_64.is_some() => {
                generate_constraints(terms_64.unwrap(), comparator, &reification)
            }
            _ if terms_128.is_some() => {
                generate_constraints(terms_128.unwrap(), comparator, &reification)
            }
            _ => generate_constraints(terms_any.unwrap(), comparator, &reification),
        };
        self.lexer.disable_dynamic_integer_parse_mode();
        Ok(result)
    }

    /// Parse a single constraint.
    fn single_constraint(&mut self, token: Token) -> Result<PBConstraintEnum, P::Error> {
        let (geq_constraint, leq_constraint) = self.constraint(token, false, false)?;
        Ok(geq_constraint.or(leq_constraint).unwrap())
    }

    /// Parse a constraint ID.
    fn constraint_id(&mut self, token: Token) -> Result<isize, P::Error> {
        match token {
            token if !self.is_constraint_id(&token)? => Err(self.lexer.report_error(
                format!("Expected a constraint ID (label or signed integer) but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
            Token::Integer64(_, id) => Ok(id as isize),
            Token::Label(ref label) => match self.label_to_id.get(label) {
                Some(id) => Ok(*id),
                None => Err(self.lexer.report_error(
                    format!("The label {token} is not assigned to a constraint ID"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?,
            },
            _ => unreachable!(),
        }
    }

    /// Parse a list of constraint IDs.
    ///
    /// If `is_colon_ending`, then the list might end with a colon.
    /// If `is_tilde_allowed`, then the list of constraint might contain a tilde `~`, which represented the negated constraint.
    fn constraint_ids(
        &mut self,
        token: Token,
        is_colon_ending: bool,
        is_tilde_allowed: bool,
    ) -> Result<(Token, Vec<isize>), P::Error> {
        let mut token = token;
        let mut ids = if is_tilde_allowed {
            vec![0]
        } else {
            Vec::new()
        };
        loop {
            match token {
                token if self.is_constraint_id(&token)? => ids.push(self.constraint_id(token)?),
                Token::Tilde if is_tilde_allowed => ids.push(0),
                token => return Err(self.lexer.report_error(
                    format!(
                        "Expected a constraint ID ({}label or signed integer) or `;` but found {}",
                        if is_tilde_allowed { "`~`, " } else { "" },
                        token
                    ),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?,
            };
            token = match self.lexer.get_next_token()? {
                token if self.is_white_space(&token) => self.optional_whitespace()?,
                Token::Colon if is_colon_ending => Token::Colon,
                Token::Semicolon => Token::Semicolon,
                token => return Err(self.lexer.report_error(
                    format!("Expected mandatory whitespace (before the next constraint ID){} or `;` but found {}", if is_colon_ending {" , `:`"} else {""}, token),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?,
            };
            if token == Token::Semicolon || (is_colon_ending && token == Token::Colon) {
                return Ok((token, ids));
            };
        }
    }

    /// Parse a line in the proof with the current `scope`.
    fn proof_lines(&mut self, token: Token, scope: &Scope) -> Result<Token, P::Error> {
        let mut token = token;
        loop {
            let label = if let Token::Label(label) = token {
                token = self.mandatory_whitespace()?;
                Some(label)
            } else {
                None
            };
            match token {
                Token::Identifier(ref s) if *scope == Scope::TopLevel && s == "output" => {
                    return Ok(token);
                }
                Token::Identifier(ref s)
                    if (*scope == Scope::Specification || *scope == Scope::Scope) && s == "end" =>
                {
                    return Ok(token);
                }
                Token::Identifier(ref s)
                    if (*scope == Scope::Subproof
                        || *scope == Scope::Proof
                        || *scope == Scope::Proofgoal)
                        && s == "qed" =>
                {
                    return Ok(token);
                }
                Token::Identifier(s) => {
                    self.rule(&s, label.is_some(), scope)?;
                    token = self.optional_whitespace()?;
                    if let Some(label) = label {
                        let id = self
                            .processor
                            .last_returned_constraint_id()
                            .expect("ProofProcessor did not return a constraint id.");
                        self.label_to_id.insert(label, id);
                    };
                }
                ref token => {
                    let additional_allowed = match (scope, label.is_some()) {
                        (Scope::TopLevel, false) => " or `output`",
                        (Scope::Specification, false) => " or `end`",
                        (Scope::Subproof, false) => ", `scope`, `proofgoal` or `qed`",
                        (Scope::Proof, false) => ", `proofgoal` or `qed`",
                        (Scope::Scope, false) => ", `proofgoal` or `end`",
                        (Scope::Proofgoal, false) => " or `qed`",
                        (_, true) => "",
                    };
                    Err(self.lexer.report_error(
                        format!(
                            "Expected a {} {}rule name{additional_allowed} but found {}",
                            scope.as_str(),
                            if label.is_some() { "output " } else { "" },
                            token,
                        ),
                        self.lexer.get_pos(),
                        token.str_len(),
                    ))?;
                }
            };
        }
    }

    /// Check if a `rule` can be used at this point in the proof.
    ///
    /// This function has the following parameters:
    /// - `is_output_context`: If a constraint or constraint ID is expected to be returned by this rule.
    /// - `scope_context`: The current scope.
    /// - `is_output_rule`: If the rule returns a constraint or constraint ID.
    /// - `rule_scope`: The maximum scope in which the rule can be used.
    fn check_rule_usage(
        &mut self,
        rule: &str,
        is_output_context: bool,
        scope_context: &Scope,
        is_output_rule: bool,
        rule_scope: Scope,
    ) -> Result<bool, P::Error> {
        if is_output_context && !is_output_rule {
            Err(self.lexer.report_error(
                format!("The rule `{rule}` cannot be prefixed with a label"),
                self.lexer.get_pos(),
                rule.len(),
            ))?;
        };
        if *scope_context > rule_scope {
            Err(self.lexer.report_error(
                format!(
                    "The rule `{}` is not allowed in a {} context",
                    rule,
                    scope_context.as_str()
                ),
                self.lexer.get_pos(),
                rule.len(),
            ))?;
        };
        Ok(true)
    }

    /// Check if a proofgoal can be used in this `scope_context` and if `is_output_context` is false.
    fn check_proofgoal_usage(
        &mut self,
        is_output_context: bool,
        scope_context: &Scope,
    ) -> Result<bool, P::Error> {
        if is_output_context {
            Err(self.lexer.report_error(
                "A proofgoal cannot be prefixed with a label".to_string(),
                self.lexer.get_pos(),
                9,
            ))?;
        };
        if *scope_context == Scope::Proofgoal
            || *scope_context == Scope::Specification
            || *scope_context == Scope::TopLevel
        {
            Err(self.lexer.report_error(
                format!(
                    "A proofgoal is not allowed in a {} context",
                    scope_context.as_str()
                ),
                self.lexer.get_pos(),
                9,
            ))?;
        };
        Ok(true)
    }

    /// Check if a subproof scope can be used in the current `scope_context` and if `is_output_context` is false.
    fn check_scope_usage(
        &mut self,
        is_output_context: bool,
        scope_context: &Scope,
    ) -> Result<bool, P::Error> {
        if is_output_context {
            Err(self.lexer.report_error(
                "A scope cannot be prefixed with a label".to_string(),
                self.lexer.get_pos(),
                5,
            ))?;
        };
        if *scope_context != Scope::Subproof {
            Err(self.lexer.report_error(
                format!(
                    "A scope is not allowed in a {} context",
                    scope_context.as_str()
                ),
                self.lexer.get_pos(),
                5,
            ))?;
        };
        Ok(true)
    }

    /// Parse a rule. This function takes care of detecting the type of rule within the current `scope`.
    ///
    /// If `is_output`, then it is expected that the rule returns a constraint or constraint ID.
    fn rule(&mut self, rule: &str, is_output: bool, scope: &Scope) -> Result<(), P::Error> {
        match rule {
            // <top_rule>
            "del" if self.check_rule_usage(rule, is_output, scope, false, Scope::TopLevel)? => {
                self.del_rule()
            }
            "delc" if self.check_rule_usage(rule, is_output, scope, false, Scope::TopLevel)? => {
                self.delc_rule()
            }
            "deld" if self.check_rule_usage(rule, is_output, scope, false, Scope::TopLevel)? => {
                self.deld_rule()
            }
            "obju" if self.check_rule_usage(rule, is_output, scope, false, Scope::TopLevel)? => {
                self.obju_rule()
            }
            "load_order"
                if self.check_rule_usage(rule, is_output, scope, false, Scope::TopLevel)? =>
            {
                self.load_order_rule()
            }
            "core" if self.check_rule_usage(rule, is_output, scope, false, Scope::TopLevel)? => {
                self.core_rule()
            }
            "setlvl"
                if self.check_rule_usage(rule, is_output, scope, false, Scope::TopLevel)? =>
            {
                self.setlvl_rule()
            }
            "wiplvl"
                if self.check_rule_usage(rule, is_output, scope, false, Scope::TopLevel)? =>
            {
                self.wiplvl_rule()
            }
            "strengthening_to_core"
                if self.check_rule_usage(rule, is_output, scope, false, Scope::TopLevel)? =>
            {
                self.strengthening_to_core_rule()
            }
            "sol" if self.check_rule_usage(rule, is_output, scope, false, Scope::TopLevel)? => {
                self.sol_rule()
            }
            "epreserved"
                if self.check_rule_usage(rule, is_output, scope, false, Scope::TopLevel)? =>
            {
                self.preserved_equals_rule()
            }
            "preserved_add"
                if self.check_rule_usage(rule, is_output, scope, false, Scope::TopLevel)? =>
            {
                self.preserved_add_rule()
            }
            "preserved_rm"
                if self.check_rule_usage(rule, is_output, scope, false, Scope::TopLevel)? =>
            {
                self.preserved_rm_rule()
            }
            "def_order"
                if self.check_rule_usage(rule, is_output, scope, false, Scope::TopLevel)? =>
            {
                self.def_order_rule()
            }
            // <top_output_rule>
            "dom" if self.check_rule_usage(rule, is_output, scope, true, Scope::TopLevel)? => {
                self.dom_rule()
            }
            "soli" if self.check_rule_usage(rule, is_output, scope, true, Scope::TopLevel)? => {
                self.soli_rule()
            }
            "obji" if self.check_rule_usage(rule, is_output, scope, true, Scope::TopLevel)? => {
                self.obji_rule()
            }
            "solx" if self.check_rule_usage(rule, is_output, scope, true, Scope::TopLevel)? => {
                self.solx_rule()
            }
            // <specification_output_rule>
            "red"
                if self.check_rule_usage(rule, is_output, scope, true, Scope::Specification)? =>
            {
                self.red_rule()
            }
            // <rule>
            "f" if self.check_rule_usage(rule, is_output, scope, false, Scope::Proofgoal)? => {
                self.f_rule()
            }
            "eobj" if self.check_rule_usage(rule, is_output, scope, false, Scope::Proofgoal)? => {
                self.eobj_rule()
            }
            "eord_def"
                if self.check_rule_usage(rule, is_output, scope, false, Scope::Proofgoal)? =>
            {
                self.eord_def_rule()
            }
            "eord_loaded"
                if self.check_rule_usage(rule, is_output, scope, false, Scope::Proofgoal)? =>
            {
                self.eord_loaded_rule()
            }
            "start_time"
                if self.check_rule_usage(rule, is_output, scope, false, Scope::Proofgoal)? =>
            {
                self.start_time_rule()
            }
            "end_time"
                if self.check_rule_usage(rule, is_output, scope, false, Scope::Proofgoal)? =>
            {
                self.end_time_rule()
            }
            "is_deleted"
                if self.check_rule_usage(rule, is_output, scope, false, Scope::Proofgoal)? =>
            {
                self.is_deleted_rule()
            }
            "fail" if self.check_rule_usage(rule, is_output, scope, false, Scope::Proofgoal)? => {
                self.fail_rule()
            }
            // <output_rule>
            "pol" if self.check_rule_usage(rule, is_output, scope, true, Scope::Proofgoal)? => {
                self.pol_rule()
            }
            "rup" if self.check_rule_usage(rule, is_output, scope, true, Scope::Proofgoal)? => {
                self.rup_rule()
            }
            "pbc" if self.check_rule_usage(rule, is_output, scope, true, Scope::Proofgoal)? => {
                self.pbc_rule()
            }
            "e" if self.check_rule_usage(rule, is_output, scope, true, Scope::Proofgoal)? => {
                self.e_rule()
            }
            "i" if self.check_rule_usage(rule, is_output, scope, true, Scope::Proofgoal)? => {
                self.i_rule()
            }
            "ia" if self.check_rule_usage(rule, is_output, scope, true, Scope::Proofgoal)? => {
                self.ia_rule()
            }
            "a" if self.check_rule_usage(rule, is_output, scope, true, Scope::Proofgoal)? => {
                self.a_rule()
            }
            // <proofgoal>
            "proofgoal" if self.check_proofgoal_usage(is_output, scope)? => self.proofgoal_rule(),
            // <scope>
            "scope" if self.check_scope_usage(is_output, scope)? => self.scope_rule(),
            rule => {
                let additional_allowed = match (scope, is_output) {
                    (Scope::TopLevel, false) => " or `output`",
                    (Scope::Specification, false) => " or `end`",
                    (Scope::Subproof, false) => ", `scope`, `proofgoal` or `qed`",
                    (Scope::Proof, false) => ", `proofgoal` or `qed`",
                    (Scope::Scope, false) => ", `proofgoal` or `end`",
                    (Scope::Proofgoal, false) => " or `qed`",
                    (_, true) => "",
                };
                Err(self.lexer.report_error(
                    format!(
                        "Expected a {} {}rule name{additional_allowed} but found `{rule}`",
                        scope.as_str(),
                        if is_output { "output " } else { "" },
                    ),
                    self.lexer.get_pos(),
                    rule.len(),
                ))?
            }
        }
    }

    /// Parse a substitution witness.
    fn witness(&mut self) -> Result<(Token, Substitution), P::Error> {
        let mut witness = Substitution::default();
        let mut token = self.optional_whitespace()?;
        loop {
            let variable = match token {
                Token::Semicolon => return Ok((Token::Semicolon, witness)),
                Token::Colon => return Ok((Token::Colon, witness)),
                token if self.is_variable(&token, true)? => self.variable(token)?,
                token => {
                    return Err(self.lexer.report_error(
                        format!("Expected a variable, `:` or `;` but found {token}"),
                        self.lexer.get_pos(),
                        token.str_len(),
                    ))?;
                }
            };
            token = match self.mandatory_whitespace()? {
                Token::MapsTo => self.mandatory_whitespace()?,
                Token::Integer64(Sign::NoSign, 0) => Token::Integer64(Sign::NoSign, 0),
                Token::Integer64(Sign::NoSign, 1) => Token::Integer64(Sign::NoSign, 1),
                token if self.is_literal(&token, true)? => token,
                token => return Err(self.lexer.report_error(
                    format!("Expected `->` (before the assigned value), a literal, `0` or `1` but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?,
            };
            let value = match token {
                Token::Integer64(Sign::NoSign, 0) => SubstitutionValue::FALSE,
                Token::Integer64(Sign::NoSign, 1) => SubstitutionValue::TRUE,
                token if self.is_literal(&token, true)? => {
                    SubstitutionValue::lit(self.literal(token, true)?)
                }
                token => {
                    return Err(self.lexer.report_error(
                        format!("Expected a literal, `0` or `1` but found {token}"),
                        self.lexer.get_pos(),
                        token.str_len(),
                    ))?;
                }
            };
            witness.set(variable, value);
            token = match self.lexer.get_next_token()? {
                token if self.is_white_space(&token) => self.optional_whitespace()?,
                Token::Semicolon => return Ok((Token::Semicolon, witness)),
                Token::Colon => return Ok((Token::Colon, witness)),
                token => return Err(self.lexer.report_error(
                    format!("Expected mandatory whitespace (before the next variable), `:` or `;` but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?,
            };
        }
    }

    /// Parse a subproof.
    fn subproof(&mut self, rule: &str) -> Result<(), P::Error> {
        let token = self.optional_whitespace()?;
        self.keyword("subproof", token)?;
        let token = self.mandatory_whitespace()?;
        self.proof_lines(token, &Scope::Subproof)?;
        let optional_hint = self.subproof_qed(rule)?;
        self.process_rule(VeriPBRule::EndSubproof(EndSubproof::new(optional_hint)))?;
        Ok(())
    }

    /// Parse the `qed` end of a subproof with the optional `rule` name.
    fn subproof_qed(&mut self, rule: &str) -> Result<Option<isize>, P::Error> {
        let token = match self.lexer.get_next_token()? {
            token if self.is_white_space(&token) => self.optional_whitespace()?,
            Token::Colon => Token::Colon,
            Token::Semicolon => Token::Semicolon,
            token => return Err(self.lexer.report_error(
                format!("Expected mandatory whitespace (before the optional `{rule}`), `:` or `;` but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        };
        match token {
            Token::Semicolon => Ok(None),
            Token::Colon => self.subproof_hint(),
            Token::Identifier(s) if s == rule => match self.optional_whitespace()? {
                Token::Semicolon => Ok(None),
                Token::Colon => self.subproof_hint(),
                token => Err(self.lexer.report_error(
                    format!("Expected `:` or `;` but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?,
            },
            token => Err(self.lexer.report_error(
                format!("Expected the optional `{rule}`, `:` or `;` but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        }
    }

    /// Parse the contradiction hint for a subproof `qed` end.
    fn subproof_hint(&mut self) -> Result<Option<isize>, P::Error> {
        let token = self.optional_whitespace()?;
        let constraint_id = self.constraint_id(token)?;
        self.optional_white_space_semicolon()?;
        Ok(Some(constraint_id))
    }

    /// Parse the `del`-rule.
    fn del_rule(&mut self) -> Result<(), P::Error> {
        let option = match self.mandatory_whitespace()? {
            Token::Identifier(s) if s == "id" => {
                return self.del_common("del", DeletionOrigin::Unknown);
            }
            Token::Identifier(s) if s == "spec" => {
                self.lexer.enable_dynamic_integer_parse_mode();
                let token = self.mandatory_whitespace()?;
                let constraint = self.single_constraint(token)?;
                DeletionOption::Spec(Rc::new(DBConstraint::from(constraint)))
            }
            Token::Identifier(s) if s == "range" => {
                let token = self.mandatory_whitespace()?;
                let start_id = self.constraint_id(token)?;
                let token = self.mandatory_whitespace()?;
                let end_id = self.constraint_id(token)?;
                DeletionOption::Range((start_id, end_id))
            }
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected `id`, `spec` or `range` but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        let token = self.optional_whitespace()?;
        let has_witness = !self.colon_or_semicolon(token)?;
        let (token, witness) = if has_witness {
            self.witness()?
        } else {
            (Token::Semicolon, Substitution::default())
        };
        let has_subproof = has_witness && !self.colon_or_semicolon(token)?;
        self.process_rule(VeriPBRule::Deletion(Deletion::new(
            option,
            witness,
            has_subproof,
            DeletionOrigin::Unknown,
        )))?;
        if has_subproof {
            self.subproof("del")
        } else {
            Ok(())
        }
    }

    /// Parse the `delc`-rule.
    fn delc_rule(&mut self) -> Result<(), P::Error> {
        self.del_common("delc", DeletionOrigin::Core)
    }

    /// Parse the `deld`-rule.
    fn deld_rule(&mut self) -> Result<(), P::Error> {
        let constraint_ids = match self.lexer.get_next_token()? {
            token if self.is_white_space(&token) => {
                let token = self.optional_whitespace()?;
                let (token, constraint_ids) = self.constraint_ids(token, false, false)?;
                self.semicolon(token)?;
                constraint_ids
            },
            Token::Semicolon => Vec::with_capacity(0),
            token => return Err(self.lexer.report_error(
                format!("Expected mandatory whitespace (before the next constraint ID) or `;` but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        };
        self.process_rule(VeriPBRule::Deletion(Deletion::new(
            DeletionOption::Id(constraint_ids),
            Substitution::default(),
            false,
            DeletionOrigin::Derived,
        )))?;
        Ok(())
    }

    /// Parse a deletion by constraint IDs and optionally parse a deletion subproof.
    fn del_common(&mut self, rule: &str, origin: DeletionOrigin) -> Result<(), P::Error> {
        let token = match self.lexer.get_next_token()? {
            token if self.is_white_space(&token) => self.optional_whitespace()?,
            Token::Colon => Token::Colon,
            Token::Semicolon => Token::Semicolon,
            token => return Err(self.lexer.report_error(
                format!("Expected mandatory whitespace (before the next constraint ID), `:` or `;` but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        };
        let (token, constraint_ids) = match token {
            token if self.is_constraint_id(&token)? => self.constraint_ids(token, true, false)?,
            Token::Colon | Token::Semicolon => (token, Vec::with_capacity(0)),
            token => {
                return Err(self.lexer.report_error(
                    format!(
                    "Expected a constraint ID (label or signed integer), `:` or `;` but found {token}"
                ),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?
            }
        };
        let has_witness = !self.colon_or_semicolon(token)?;
        let (token, witness) = if has_witness {
            self.witness()?
        } else {
            (Token::Semicolon, Substitution::default())
        };
        let has_subproof = has_witness && !self.colon_or_semicolon(token)?;
        self.process_rule(VeriPBRule::Deletion(Deletion::new(
            DeletionOption::Id(constraint_ids),
            witness,
            has_subproof,
            origin,
        )))?;
        if has_subproof {
            self.subproof(rule)
        } else {
            Ok(())
        }
    }

    /// Parse the `obju` rule.
    fn obju_rule(&mut self) -> Result<(), P::Error> {
        let update_type = match self.mandatory_whitespace()? {
            Token::Identifier(s) if s == "new" => ObjectiveUpdateType::New,
            Token::Identifier(s) if s == "diff" => ObjectiveUpdateType::Diff,
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected `new` or `diff` but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        self.lexer.enable_dynamic_integer_parse_mode();
        self.lexer.set_integer_parse_mode(IntegerParseMode::BitsAny);
        let token = self.mandatory_whitespace()?;
        let (token, objective) = self.objective(token, true, false)?;
        let has_subproof = !self.colon_or_semicolon(token)?;
        self.process_rule(VeriPBRule::ObjectiveUpdateRule(ObjectiveUpdateRule::new(
            objective,
            update_type,
            has_subproof,
        )))?;
        if has_subproof {
            self.subproof("obju")
        } else {
            Ok(())
        }
    }

    /// Parse the `load_order`-rule.
    pub fn load_order_rule(&mut self) -> Result<(), P::Error> {
        let (optional_name, literals) = self.order_load_literals()?;
        self.process_rule(VeriPBRule::LoadOrderRule(LoadOrderRule::new(
            optional_name,
            literals,
        )))?;
        Ok(())
    }

    /// Parse an order name and a list of literals.
    fn order_load_literals(&mut self) -> Result<(Option<String>, Vec<Lit>), P::Error> {
        let token = match self.lexer.get_next_token()? {
            token if self.is_white_space(&token) => self.optional_whitespace()?,
            Token::Semicolon => return Ok((None, Vec::with_capacity(0))),
            token => return Err(self.lexer.report_error(
                format!(
                    "Expected mandatory whitespace (before the order name) or `;` but found {token}"
                ),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        };
        let name = match token {
            Token::Identifier(name) => Some(name),
            Token::Semicolon => return Ok((None, Vec::with_capacity(0))),
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected a order name but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        match self.lexer.get_next_token()? {
            token if self.is_white_space(&token) => {
                let token = self.optional_whitespace()?;
                let (token, literals) = self.literals(token, false, false, false)?;
                self.semicolon(token)?;
                Ok((name, literals))
            }
            Token::Semicolon => Ok((name, Vec::with_capacity(0))),
            token => Err(self.lexer.report_error(
                format!(
                    "Expected mandatory whitespace (before the literals) or `;` but found {token}"
                ),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        }
    }

    /// Parse the `core`-rule.
    fn core_rule(&mut self) -> Result<(), P::Error> {
        match self.mandatory_whitespace()? {
            Token::Identifier(s) if s == "id" => {
                let token = match self.lexer.get_next_token()? {
                    token if self.is_white_space(&token) => self.optional_whitespace()?,
                    Token::Semicolon => Token::Semicolon,
                    token => return Err(self.lexer.report_error(
                        format!("Expected mandatory whitespace (before the next constraint ID) or `;` but found {token}"),
                        self.lexer.get_pos(),
                        token.str_len(),
                    ))?,
                };
                let constraint_ids = match token {
                    token if self.is_constraint_id(&token)? => {
                        let (token, constraint_ids) = self.constraint_ids(token, false, false)?;
                        self.semicolon(token)?;
                        constraint_ids
                    },
                    Token::Semicolon => Vec::with_capacity(0),
                    token => return Err(self.lexer.report_error(
                        format!("Expected a constraint ID (label or signed integer) or `;` but found {token}"),
                        self.lexer.get_pos(),
                        token.str_len(),
                    ))?,
                };
                self.process_rule(VeriPBRule::MoveToCoreRule(MoveToCoreRule::new(
                    IdentifierOption::Id,
                    constraint_ids,
                )))?;
                Ok(())
            }
            Token::Identifier(s) if s == "range" => {
                let token = self.mandatory_whitespace()?;
                let start_id = self.constraint_id(token)?;
                let token = self.mandatory_whitespace()?;
                let end_id = self.constraint_id(token)?;
                self.optional_white_space_semicolon()?;
                self.process_rule(VeriPBRule::MoveToCoreRule(MoveToCoreRule::new(
                    IdentifierOption::Range,
                    vec![start_id, end_id],
                )))?;
                Ok(())
            }
            token => Err(self.lexer.report_error(
                format!("Expected `id` or `range` but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        }
    }

    /// Parse the `setlvl`-rule.
    fn setlvl_rule(&mut self) -> Result<(), P::Error> {
        match self.mandatory_whitespace()? {
            Token::Integer64(Sign::NoSign, value) => {
                self.optional_white_space_semicolon()?;
                self.process_rule(VeriPBRule::SetLevelRule(SetLevelRule::new(value as usize)))?;
                Ok(())
            }
            token => Err(self.lexer.report_error(
                format!("Expected an unsigned integer but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        }
    }

    /// Parse the `wiplvl`-rule
    fn wiplvl_rule(&mut self) -> Result<(), P::Error> {
        match self.mandatory_whitespace()? {
            Token::Integer64(Sign::NoSign, value) => {
                self.optional_white_space_semicolon()?;
                self.process_rule(VeriPBRule::Deletion(Deletion::new(
                    DeletionOption::Wipe(value as usize),
                    Substitution::default(),
                    false,
                    DeletionOrigin::Unknown,
                )))?;
                Ok(())
            }
            token => Err(self.lexer.report_error(
                format!("Expected an unsigned integer but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        }
    }

    /// Parse the `strengthening_to_core`-rule.
    fn strengthening_to_core_rule(&mut self) -> Result<(), P::Error> {
        let enable = match self.mandatory_whitespace()? {
            Token::Identifier(s) if s == "on" => true,
            Token::Identifier(s) if s == "off" => false,
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected `on` or `off` but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        self.optional_white_space_semicolon()?;
        self.process_rule(VeriPBRule::StrengtheningToCoreRule(
            StrengtheningToCoreRule::new(enable),
        ))?;
        Ok(())
    }

    /// Parse the `sol`-rule.
    fn sol_rule(&mut self) -> Result<(), P::Error> {
        self.sol_common(SolutionRuleOutput::None)
    }

    /// Parse a solution with an optional objective value.
    fn sol_common(&mut self, rule_output: SolutionRuleOutput) -> Result<(), P::Error> {
        let is_value_allowed = rule_output != SolutionRuleOutput::Excluding;
        let token = match self.lexer.get_next_token()? {
            token if self.is_white_space(&token) => self.optional_whitespace()?,
            Token::Colon if is_value_allowed => Token::Colon,
            Token::Semicolon => Token::Semicolon,
            token => {
                return Err(self.lexer.report_error(
                    format!(
                        "Expected mandatory whitespace (before the solution){} or `;` but found {token}",
                        if is_value_allowed { ", `:`" } else { "" }
                    ),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?
            }
        };
        let (token, solution) = match token {
            token if self.is_literal(&token, false)? => self.literals(token, false, true, false)?,
            Token::Colon if is_value_allowed => (Token::Colon, Vec::with_capacity(0)),
            Token::Semicolon => (Token::Semicolon, Vec::with_capacity(0)),
            token => {
                return Err(self.lexer.report_error(
                    format!(
                        "Expected a literal{} or `;` but found {}",
                        if is_value_allowed { ", `:`" } else { "" },
                        token
                    ),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        self.lexer.enable_dynamic_integer_parse_mode();
        self.lexer.set_integer_parse_mode(IntegerParseMode::BitsAny);
        let (token, optional_value) = match token {
            Token::Colon if is_value_allowed => {
                let value = match self.optional_whitespace()? {
                    Token::Integer64(_, value) => BigInt::from(value),
                    Token::Integer128(_, value) => BigInt::from(value),
                    Token::IntegerAny(_, value) => value,
                    token => {
                        return Err(self.lexer.report_error(
                            format!(
                                "Expected an objective value (signed integer) but found {token}"
                            ),
                            self.lexer.get_pos(),
                            token.str_len(),
                        ))?;
                    }
                };
                (self.optional_whitespace()?, Some(value))
            }
            Token::Semicolon => (Token::Semicolon, None),
            token => {
                return Err(self.lexer.report_error(
                    format!(
                        "Expected a literal{} or `;` but found {}",
                        if is_value_allowed { ", `:`" } else { "" },
                        token
                    ),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        self.lexer.disable_dynamic_integer_parse_mode();
        self.semicolon(token)?;
        self.process_rule(VeriPBRule::SolutionRule(SolutionRule::new(
            solution,
            rule_output,
            optional_value,
        )))?;
        Ok(())
    }

    /// Parse the `epreserved`-rule.
    fn preserved_equals_rule(&mut self) -> Result<(), P::Error> {
        let token = match self.lexer.get_next_token()? {
            token if self.is_white_space(&token) => self.optional_whitespace()?,
            Token::Semicolon => Token::Semicolon,
            token => return Err(self.lexer.report_error(
                format!(
                    "Expected mandatory whitespace (before the variables) or `;` but found {token}"
                ),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        };
        let (token, vars) = match token {
            token if self.is_variable(&token, false)? => self.variables(token, true, false)?,
            Token::Semicolon => (Token::Semicolon, Vec::new()),
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected a variable or `;` but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        self.semicolon(token)?;
        self.process_rule(VeriPBRule::PreservedEqualsRule(PreservedEqualsRule::new(
            vars,
        )))
    }

    /// Parse the `preserved_add`-rule.
    fn preserved_add_rule(&mut self) -> Result<(), P::Error> {
        let var = match self.mandatory_whitespace()? {
            token if self.is_variable(&token, false)? => self.variable(token)?,
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected a variable but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        let token = self.optional_whitespace()?;
        self.colon(token)?;
        let token = self.optional_whitespace()?;
        let constraint = self.single_constraint(token)?;
        let token = self.optional_whitespace()?;
        let has_subproof = !self.colon_or_semicolon(token)?;
        self.process_rule(VeriPBRule::PreservedAddRule(PreservedAddRule::new(
            var,
            constraint,
            has_subproof,
        )))?;
        if has_subproof {
            self.subproof("preserved_add")
        } else {
            Ok(())
        }
    }

    /// Parse the `preserved_rm`-rule.
    fn preserved_rm_rule(&mut self) -> Result<(), P::Error> {
        let var = match self.mandatory_whitespace()? {
            token if self.is_variable(&token, false)? => self.variable(token)?,
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected a variable but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        let token = self.optional_whitespace()?;
        self.colon(token)?;
        let token = self.optional_whitespace()?;
        let constraint = self.single_constraint(token)?;
        let token = self.optional_whitespace()?;
        let has_subproof = !self.colon_or_semicolon(token)?;
        self.process_rule(VeriPBRule::PreservedRemoveRule(PreservedRemoveRule::new(
            var,
            constraint,
            has_subproof,
        )))?;
        if has_subproof {
            self.subproof("preserved_rm")
        } else {
            Ok(())
        }
    }

    /// Parse the `def_order`-rule.
    fn def_order_rule(&mut self) -> Result<(), P::Error> {
        let order_name = match self.mandatory_whitespace()? {
            Token::Identifier(name) => name,
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected an order name but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        self.process_rule(VeriPBRule::DefineOrderRule(DefineOrderRule::new(
            order_name,
        )))?;
        let token = self.mandatory_whitespace()?;
        self.order_vars(token)?;
        let token = self.optional_whitespace()?;
        let token = match token {
            Token::Identifier(ref s) if s == "spec" => {
                self.order_spec(token)?;
                self.optional_whitespace()?
            }
            Token::Identifier(ref s) if s == "def" => token,
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected `spec` or `def` but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        self.order_constraints(false, token)?;
        let token = self.optional_whitespace()?;
        let token = match token {
            Token::Identifier(ref s) if s == "transitivity" => {
                self.order_transitivity(token)?;
                self.optional_whitespace()?
            }
            Token::Identifier(ref s) if s == "reflexivity" => token,
            Token::Identifier(ref s) if s == "end" => token,
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected `transitivity`, `reflexivity` or `end` but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        match token {
            Token::Identifier(ref s) if s == "reflexivity" => {
                self.order_reflexivity(token)?;
                let token = self.optional_whitespace()?;
                self.keyword("end", token)?;
            }
            Token::Identifier(ref s) if s == "end" => {}
            token => {
                Err(self.lexer.report_error(
                    format!("Expected `reflexivity` or `end` but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        self.order_end_environment("def_order")
    }

    /// Parse a list of variables in an order. If `is_aux`, then only auxiliary variables are allowed in the list.
    fn order_variables_list(&mut self, is_aux: bool) -> Result<Vec<VarIdx>, P::Error> {
        let token = match self.lexer.get_next_token()? {
            token if self.is_white_space(&token) => self.optional_whitespace()?,
            Token::Semicolon => return Ok(Vec::with_capacity(0)),
            token => return Err(self.lexer.report_error(
                format!(
                    "Expected mandatory whitespace (before the variables) or `;` but found {token}"
                ),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        };
        match token {
            token if self.is_any_variable(&token, !is_aux, is_aux)? => {
                let (token, variables) = self.variables(token, !is_aux, is_aux)?;
                self.semicolon(token)?;
                Ok(variables)
            }
            Token::Semicolon => Ok(Vec::with_capacity(0)),
            token => Err(self.lexer.report_error(
                format!(
                    "Expected a{} variable or `;` but found {}",
                    if is_aux { "n auxiliary" } else { "" },
                    token
                ),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        }
    }

    /// Parse the `end` or an order definition `environment`.
    fn order_end_environment(&mut self, environment: &str) -> Result<(), P::Error> {
        let token = match self.lexer.get_next_token()? {
            token if self.is_white_space(&token) => self.optional_whitespace()?,
            Token::Semicolon => Token::Semicolon,
            token => return Err(self.lexer.report_error(
                format!("Expected mandatory whitespace (before the optional `{environment}`) or `;` but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        };
        match token {
            Token::Semicolon => {}
            Token::Identifier(ref s) if s == environment => {
                self.optional_white_space_semicolon()?;
            }
            token => {
                Err(self.lexer.report_error(
                    format!("Expected the optional `{environment}` or `;` but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        self.process_rule(VeriPBRule::EndSubproof(EndSubproof::new(None)))?;
        Ok(())
    }

    /// Parse the `proof` for and order property.
    fn order_proof(&mut self, token: Token) -> Result<(), P::Error> {
        self.keyword("proof", token)?;
        let token = self.mandatory_whitespace()?;
        self.process_rule(VeriPBRule::OrderProofRule(OrderProofRule))?;
        let mut label_to_id = AHashMap::new();
        std::mem::swap(&mut label_to_id, &mut self.label_to_id);
        self.proof_lines(token, &Scope::Proof)?;
        self.label_to_id = label_to_id;
        let token = match self.lexer.get_next_token()? {
            token if self.is_white_space(&token) => self.optional_whitespace()?,
            Token::Semicolon => Token::Semicolon,
            token => return Err(self.lexer.report_error(
                format!("Expected mandatory whitespace (before the optional `proof`) or `;` but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        };
        let token = match token {
            Token::Semicolon => Token::Semicolon,
            Token::Identifier(s) if s == "proof" => self.optional_whitespace()?,
            token => Err(self.lexer.report_error(
                format!("Expected the optional `proof` or `;` but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        };
        self.semicolon(token)?;
        self.process_rule(VeriPBRule::EndSubproof(EndSubproof::new(None)))?;
        Ok(())
    }

    /// Parse `vars` environment for an order.
    fn order_vars(&mut self, token: Token) -> Result<(), P::Error> {
        self.keyword("vars", token)?;
        let token = self.mandatory_whitespace()?;
        self.process_rule(VeriPBRule::OrderVariablesRule(OrderVariablesRule))?;
        self.keyword("left", token)?;
        let left_variables = self.order_variables_list(false)?;
        self.process_rule(VeriPBRule::OrderLeftVariablesRule(
            OrderLeftVariablesRule::new(left_variables),
        ))?;
        let token = self.optional_whitespace()?;
        self.keyword("right", token)?;
        let right_variables = self.order_variables_list(false)?;
        self.process_rule(VeriPBRule::OrderRightVariablesRule(
            OrderRightVariablesRule::new(right_variables),
        ))?;
        match self.optional_whitespace()? {
            Token::Identifier(ref s) if s == "aux" => {
                let aux_variables = self.order_variables_list(true)?;
                self.process_rule(VeriPBRule::OrderAuxVariablesRule(
                    OrderAuxVariablesRule::new(aux_variables),
                ))?;
                let token = self.optional_whitespace()?;
                self.keyword("end", token)?;
            }
            Token::Identifier(ref s) if s == "end" => {}
            token => {
                Err(self.lexer.report_error(
                    format!("Expected `aux` or `end` but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        self.order_end_environment("vars")
    }

    /// Parse the auxiliary `spec` environment of an order.
    fn order_spec(&mut self, token: Token) -> Result<(), P::Error> {
        self.keyword("spec", token)?;
        let token = self.mandatory_whitespace()?;
        self.process_rule(VeriPBRule::OrderSpecificationRule(OrderSpecificationRule))?;
        let mut label_to_id = AHashMap::new();
        std::mem::swap(&mut label_to_id, &mut self.label_to_id);
        self.proof_lines(token, &Scope::Specification)?;
        self.label_to_id = label_to_id;
        self.order_end_environment("spec")
    }

    /// Parse the constraints defining an order.
    fn order_constraints(&mut self, is_spec: bool, token: Token) -> Result<(), P::Error> {
        let keyword = if is_spec { "spec" } else { "def" };
        self.keyword(keyword, token)?;
        self.lexer.enable_dynamic_integer_parse_mode();
        let mut token = self.mandatory_whitespace()?;
        if is_spec {
            self.process_rule(VeriPBRule::UnimplementedRule(UnimplementedRule::new(
                "eord_def.spec".to_string(),
            )))?;
        } else {
            self.process_rule(VeriPBRule::OrderDefRule(OrderDefRule))?;
        };
        loop {
            match token {
                Token::Identifier(ref s) if s == "end" => {
                    return self.order_end_environment(keyword)
                }
                Token::Integer64(_, _) | Token::Integer128(_, _) | Token::IntegerAny(_, _) | Token::GreaterEqual | Token::LessEqual => {}
                ref token if self.is_literal(token, is_spec)? => {}
                token => {
                    return Err(self.lexer.report_error(
                        format!("Expected a coefficient (signed integer), a literal or `end` but found {token}"),
                        self.lexer.get_pos(),
                        token.str_len(),
                    ))?
                }
            };
            let constraint = self.single_constraint(token)?;
            self.optional_white_space_semicolon()?;
            if is_spec {
                self.process_rule(VeriPBRule::UnimplementedRule(UnimplementedRule::new(
                    "eord_def.spec.constraint".to_string(),
                )))?;
            } else {
                self.process_rule(VeriPBRule::OrderDefConstraintRule(
                    OrderDefConstraintRule::new(constraint),
                ))?;
            };
            self.lexer.enable_dynamic_integer_parse_mode();
            token = self.optional_whitespace()?;
        }
    }

    /// Parse the transitivity property environment.
    fn order_transitivity(&mut self, token: Token) -> Result<(), P::Error> {
        self.keyword("transitivity", token)?;
        let token = self.mandatory_whitespace()?;
        self.process_rule(VeriPBRule::OrderTransitivityRule(OrderTransitivityRule))?;
        self.keyword("vars", token)?;
        let token = self.mandatory_whitespace()?;
        self.process_rule(VeriPBRule::OrderVariablesRule(OrderVariablesRule))?;
        self.keyword("fresh_right", token)?;
        let fresh_right_variables = self.order_variables_list(false)?;
        self.process_rule(VeriPBRule::OrderFreshRightVariablesRule(
            OrderFreshRightVariablesRule::new(fresh_right_variables),
        ))?;
        match self.optional_whitespace()? {
            Token::Identifier(ref s) if s == "fresh_aux_1" => {
                let fresh_aux_1_variables = self.order_variables_list(true)?;
                let token = self.optional_whitespace()?;
                self.process_rule(VeriPBRule::OrderFreshAux1Rule(OrderFreshAux1Rule::new(
                    fresh_aux_1_variables,
                )))?;
                self.keyword("fresh_aux_2", token)?;
                let fresh_aux_2_variables = self.order_variables_list(true)?;
                let token = self.optional_whitespace()?;
                self.process_rule(VeriPBRule::OrderFreshAux2Rule(OrderFreshAux2Rule::new(
                    fresh_aux_2_variables,
                )))?;
                self.keyword("end", token)?;
            }
            Token::Identifier(ref s) if s == "end" => {}
            token => {
                Err(self.lexer.report_error(
                    format!("Expected `fresh_aux_1` or `end` but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        self.order_end_environment("vars")?;
        let token = self.optional_whitespace()?;
        self.order_proof(token)?;
        let token = self.optional_whitespace()?;
        self.keyword("end", token)?;
        self.order_end_environment("transitivity")
    }

    /// Parse the reflexivity property environment.
    fn order_reflexivity(&mut self, token: Token) -> Result<(), P::Error> {
        self.keyword("reflexivity", token)?;
        let token = self.mandatory_whitespace()?;
        self.process_rule(VeriPBRule::OrderReflexivityRule(OrderReflexivityRule))?;
        self.order_proof(token)?;
        let token = self.optional_whitespace()?;
        self.keyword("end", token)?;
        self.order_end_environment("reflexivity")
    }

    /// Parse the `dom`-rule.
    fn dom_rule(&mut self) -> Result<(), P::Error> {
        self.lexer.enable_dynamic_integer_parse_mode();
        let token = self.mandatory_whitespace()?;
        let constraint = self.single_constraint(token)?;
        let token = self.optional_whitespace()?;
        if self.colon_or_semicolon(token)? {
            log::warn!(
                "A witness must be specified for the dom-rule ending on line {} col {}.",
                self.lexer.get_pos().line,
                self.lexer.get_pos().col,
            );
            self.process_rule(VeriPBRule::DominanceBasedStrengtheningRule(
                DominanceBasedStrengtheningRule::new(constraint, Substitution::default(), false),
            ))?;
            return Ok(());
        };
        let (token, witness) = self.witness()?;
        if self.colon_or_semicolon(token)? {
            self.process_rule(VeriPBRule::DominanceBasedStrengtheningRule(
                DominanceBasedStrengtheningRule::new(constraint, witness, false),
            ))?;
            return Ok(());
        };
        self.process_rule(VeriPBRule::DominanceBasedStrengtheningRule(
            DominanceBasedStrengtheningRule::new(constraint, witness, true),
        ))?;
        self.subproof("dom")
    }

    /// Parse the `soli`-rule.
    fn soli_rule(&mut self) -> Result<(), P::Error> {
        self.sol_common(SolutionRuleOutput::Improving)
    }

    /// Parse the `obji`- rule.
    fn obji_rule(&mut self) -> Result<(), P::Error> {
        self.lexer.enable_dynamic_integer_parse_mode();
        self.lexer.set_integer_parse_mode(IntegerParseMode::BitsAny);
        let objective_value = match self.mandatory_whitespace()? {
            Token::IntegerAny(_, value) => value,
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected an objective value (signed integer) but found {token}",),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        self.lexer.disable_dynamic_integer_parse_mode();
        self.optional_white_space_semicolon()?;
        self.process_rule(VeriPBRule::ObjectiveValueRule(ObjectiveValueRule::new(
            objective_value,
        )))?;
        Ok(())
    }

    /// Parse the `solx`-rule.
    fn solx_rule(&mut self) -> Result<(), P::Error> {
        self.sol_common(SolutionRuleOutput::Excluding)
    }

    /// Parse the `red`-rule.
    fn red_rule(&mut self) -> Result<(), P::Error> {
        self.lexer.enable_dynamic_integer_parse_mode();
        let token = self.mandatory_whitespace()?;
        let constraint = self.single_constraint(token)?;
        let token = self.optional_whitespace()?;
        if self.colon_or_semicolon(token)? {
            log::warn!(
                "A witness must be specified for the red-rule ending on line {} col {}.",
                self.lexer.get_pos().line,
                self.lexer.get_pos().col,
            );
            self.process_rule(VeriPBRule::RedundanceBasedStrengtheningRule(
                RedundanceBasedStrengtheningRule::new(constraint, Substitution::default(), false),
            ))?;
            return Ok(());
        };
        let (token, witness) = self.witness()?;
        if self.colon_or_semicolon(token)? {
            self.process_rule(VeriPBRule::RedundanceBasedStrengtheningRule(
                RedundanceBasedStrengtheningRule::new(constraint, witness, false),
            ))?;
            return Ok(());
        };
        self.process_rule(VeriPBRule::RedundanceBasedStrengtheningRule(
            RedundanceBasedStrengtheningRule::new(constraint, witness, true),
        ))?;
        self.subproof("red")
    }

    /// Parse the `f`-rule.
    fn f_rule(&mut self) -> Result<(), P::Error> {
        match self.mandatory_whitespace()? {
            Token::Integer64(Sign::NoSign, value) => {
                self.optional_white_space_semicolon()?;
                self.process_rule(VeriPBRule::FormulaCheck(FormulaCheck::new(value as usize)))?;
                Ok(())
            }
            token => Err(self.lexer.report_error(
                format!("Expected an unsigned integer but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        }
    }

    /// Parse the `eobj`-rule.
    fn eobj_rule(&mut self) -> Result<(), P::Error> {
        self.lexer.enable_dynamic_integer_parse_mode();
        self.lexer.set_integer_parse_mode(IntegerParseMode::BitsAny);
        let token = self.mandatory_whitespace()?;
        let (token, objective) = self.objective(token, false, false)?;
        self.semicolon(token)?;
        self.process_rule(VeriPBRule::EqualsObjectiveRule(EqualsObjectiveRule::new(
            objective,
        )))?;
        Ok(())
    }

    /// Parse the `eord_def`-rule.
    fn eord_def_rule(&mut self) -> Result<(), P::Error> {
        let _order_name = match self.mandatory_whitespace()? {
            Token::Identifier(name) => name,
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected an order name but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        let token = self.mandatory_whitespace()?;
        self.process_rule(VeriPBRule::UnimplementedRule(UnimplementedRule::new(
            "eord_def".to_string(),
        )))?;
        self.order_vars(token)?;
        let token = self.optional_whitespace()?;
        let token = match token {
            Token::Identifier(ref s) if s == "spec" => {
                self.order_constraints(true, token)?;
                self.optional_whitespace()?
            }
            Token::Identifier(ref s) if s == "def" => token,
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected `spec` or `def` but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        self.order_constraints(false, token)?;
        let token = self.optional_whitespace()?;
        self.keyword("end", token)?;
        self.order_end_environment("eord_def")
    }

    /// Parse the `eord_loaded`-rule.
    fn eord_loaded_rule(&mut self) -> Result<(), P::Error> {
        let (_optional_name, _literals) = self.order_load_literals()?;
        self.process_rule(VeriPBRule::UnimplementedRule(UnimplementedRule::new(
            "eord_loaded".to_string(),
        )))?;
        Ok(())
    }

    /// Parse the `start_time`-rule.
    fn start_time_rule(&mut self) -> Result<(), P::Error> {
        let timer_name = match self.mandatory_whitespace()? {
            Token::Identifier(name) => name,
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected a timer name but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        self.optional_white_space_semicolon()?;
        self.process_rule(VeriPBRule::StartTimerRule(StartTimerRule::new(timer_name)))?;
        Ok(())
    }

    /// Parse the `end_time`-rule.
    fn end_time_rule(&mut self) -> Result<(), P::Error> {
        let timer_name = match self.mandatory_whitespace()? {
            Token::Identifier(name) => name,
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected a timer name but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        self.optional_white_space_semicolon()?;
        self.process_rule(VeriPBRule::EndTimerRule(EndTimerRule::new(timer_name)))?;
        Ok(())
    }

    /// Parse the `is_deleted`-rule.
    fn is_deleted_rule(&mut self) -> Result<(), P::Error> {
        self.lexer.enable_dynamic_integer_parse_mode();
        let token = self.mandatory_whitespace()?;
        let constraint = self.single_constraint(token)?;
        self.optional_white_space_semicolon()?;
        self.process_rule(VeriPBRule::IsDeletedCheck(IsDeletedCheck::new(constraint)))?;
        Ok(())
    }

    /// Parse the `fail`-rule.
    fn fail_rule(&mut self) -> Result<(), P::Error> {
        self.optional_white_space_semicolon()?;
        self.process_rule(VeriPBRule::FailRule(FailRule))?;
        Ok(())
    }

    /// Parse the `pol`-rule.
    fn pol_rule(&mut self) -> Result<(), P::Error> {
        let mut positive_integer = None;
        let mut variable = None;
        let mut stack_size = 0;
        let mut instructions = Vec::new();
        self.lexer.enable_dynamic_integer_parse_mode();
        let mut token = self.mandatory_whitespace()?;
        loop {
            let operand = match token {
                Token::Plus if stack_size >= 2 => {
                    stack_size -= 1;
                    instructions.push(Instruction::Add);
                    None
                }
                // The binary operators below each consume an operand (a positive
                // integer for the arithmetic ones, a variable for `w`) that must
                // have been recognised on the preceding token. Guarding on its
                // presence as well as `stack_size` means a malformed line such as
                // `pol 1 2 2 2 * * *` (an operator with nothing to consume) falls
                // through to `pol_parse_error` rather than unwrapping a `None`.
                Token::Minus if stack_size >= 2 && positive_integer.is_some() => {
                    stack_size -= 1;
                    instructions.push(Instruction::LowerRHS(positive_integer.take().unwrap()));
                    None
                }
                Token::Star if stack_size >= 2 && positive_integer.is_some() => {
                    stack_size -= 1;
                    instructions.push(Instruction::Multiply(positive_integer.take().unwrap()));
                    None
                }
                Token::Identifier(ref s)
                    if stack_size >= 2 && positive_integer.is_some() && s == "d" =>
                {
                    stack_size -= 1;
                    instructions.push(Instruction::NormalizedFormDivide(
                        positive_integer.take().unwrap(),
                    ));
                    None
                }
                Token::Identifier(ref s)
                    if stack_size >= 2 && positive_integer.is_some() && s == "c" =>
                {
                    stack_size -= 1;
                    instructions.push(Instruction::VariableFormDivide(
                        positive_integer.take().unwrap(),
                    ));
                    None
                }
                Token::Identifier(ref s)
                    if stack_size >= 2 && positive_integer.is_some() && s == "n" =>
                {
                    stack_size -= 1;
                    instructions.push(Instruction::NormalizedFormMIR(
                        positive_integer.take().unwrap(),
                    ));
                    None
                }
                Token::Identifier(ref s)
                    if stack_size >= 2 && positive_integer.is_some() && s == "m" =>
                {
                    stack_size -= 1;
                    instructions.push(Instruction::VariableFormMIR(
                        positive_integer.take().unwrap(),
                    ));
                    None
                }
                Token::Identifier(ref s) if stack_size >= 1 && s == "s" => {
                    instructions.push(Instruction::Saturate);
                    positive_integer = None;
                    None
                }
                Token::Identifier(ref s) if stack_size >= 2 && variable.is_some() && s == "w" => {
                    stack_size -= 1;
                    instructions.push(Instruction::Weaken(variable.take().unwrap()));
                    None
                }
                Token::Integer64(Sign::NoSign, id) => {
                    Some(PolToken::NonNegativeIntegerOrID(id as isize))
                }
                token if self.is_constraint_id(&token)? => {
                    Some(PolToken::ConstraintId(self.constraint_id(token)?))
                }
                Token::Integer128(Sign::NoSign, id) if stack_size > 0 && id != 0 => {
                    self.lexer.set_integer_parse_mode(IntegerParseMode::Bits64);
                    Some(PolToken::PositiveInteger(BigInt::from(id)))
                }
                Token::IntegerAny(Sign::NoSign, id) if stack_size > 0 && !id.is_zero() => {
                    self.lexer.set_integer_parse_mode(IntegerParseMode::Bits64);
                    Some(PolToken::PositiveInteger(id))
                }
                Token::Tilde => Some(PolToken::Literal(self.literal(token, true)?)),
                ref token @ (Token::Identifier(ref s) | Token::AuxiliaryVariable(ref s))
                    if s != "d"
                        && s != "c"
                        && s != "n"
                        && s != "m"
                        && s != "s"
                        && s != "w"
                        && self.is_literal(token, true)? =>
                {
                    Some(PolToken::Literal(self.literal(token.clone(), true)?))
                }
                Token::Semicolon if stack_size == 1 => {
                    self.lexer.disable_dynamic_integer_parse_mode();
                    self.process_rule(VeriPBRule::PolRule(PolRule::new(instructions)))?;
                    return Ok(());
                }
                token => return Err(self.pol_parse_error(token, stack_size, None))?,
            };
            stack_size += operand.is_some() as usize;
            token = match self.lexer.get_next_token()? {
                token if self.is_white_space(&token) => self.optional_whitespace()?,
                Token::Semicolon if stack_size == 1 => Token::Semicolon,
                token => return Err(self.lexer.report_error(
                    format!("Expected mandatory whitespace (before the next operand or operator){} but found {} (there are {} element{} on the stack)", if stack_size == 1 {" or `;`"} else {""}, token, stack_size, if stack_size == 1 {""} else {"s"}),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?,
            };
            // Lookahead to ensure the right kind of token is present for the next operator (if any).
            match (&token, operand) {
                (_, None) => {}
                (Token::Star, Some(PolToken::NonNegativeIntegerOrID(integer))) => {
                    positive_integer = Some(BigInt::from(integer))
                }
                (Token::Star, Some(PolToken::PositiveInteger(integer))) => {
                    positive_integer = Some(integer)
                }
                (Token::Identifier(s), Some(PolToken::NonNegativeIntegerOrID(integer)))
                    if s == "d" || s == "c" || s == "m" || s == "n" =>
                {
                    if integer == 0 {
                        Err(self.lexer.report_error(
                            "Division by 0 is not possible! This was caused by division"
                                .to_string(),
                            self.lexer.get_pos(),
                            token.str_len(),
                        ))?
                    }
                    positive_integer = Some(BigInt::from(integer))
                }
                (Token::Identifier(s), Some(PolToken::PositiveInteger(integer)))
                    if s == "d" || s == "c" || s == "m" || s == "n" =>
                {
                    positive_integer = Some(integer)
                }
                (Token::Minus, Some(PolToken::NonNegativeIntegerOrID(integer))) => {
                    positive_integer = Some(BigInt::from(integer))
                }
                (Token::Minus, Some(PolToken::PositiveInteger(integer))) => {
                    positive_integer = Some(integer)
                }
                (Token::Identifier(s), Some(PolToken::Literal(literal)))
                    if s == "w" && !literal.is_negated() =>
                {
                    variable = Some(literal.get_var())
                }
                (Token::Star, operand) => {
                    return Err(self.pol_parse_error(token, stack_size, operand).into());
                }
                (Token::Identifier(s), operand)
                    if s == "c" || s == "d" || s == "m" || s == "n" || s == "w" =>
                {
                    return Err(self.pol_parse_error(token, stack_size, operand).into());
                }
                (_, Some(PolToken::ConstraintId(id)))
                | (_, Some(PolToken::NonNegativeIntegerOrID(id))) => {
                    instructions.push(Instruction::ConstraintId(id))
                }
                (_, Some(PolToken::Literal(literal))) => {
                    instructions.push(Instruction::LiteralAxiom(literal))
                }
                (_, operand) => {
                    return Err(self.pol_parse_error(token, stack_size, operand).into());
                }
            };
        }
    }

    /// Generate a parsing error for a `pol`-rule.
    fn pol_parse_error(
        &mut self,
        token: Token,
        stack_size: usize,
        operand: Option<PolToken>,
    ) -> ParserError {
        let allowed = match operand {
            _ if stack_size == 0 => "a constraint ID (label or signed integer) or a literal",
            _ if stack_size == 1 => {
                "a constraint ID (label or signed integer), a literal, a variable, an unsigned positive integer, an unary operator (`s`) or `;`"
            }
            Some(PolToken::NonNegativeIntegerOrID(_)) => {
                "a constraint ID (label or signed integer), a literal, a variable, an unsigned positive integer, an unary operator (`s`) or a binary operator (`+`, `*`, or `d`)"
            }
            Some(PolToken::PositiveInteger(_)) => {
                "a constraint ID (label or signed integer), a literal, a variable, an unsigned positive integer or a binary operator (`*`, or `d`)"
            }
            Some(PolToken::Literal(literal)) if !literal.is_negated() => {
                "a constraint ID (label or signed integer), a literal, a variable, an unsigned positive integer, an unary operator (`s`) or a binary operator (`+` or `w`)"
            }
            _ => {
                "a constraint ID (label or signed integer), a literal, a variable, an unsigned positive integer, an unary operator (`s`) or a binary operator (`+`)"
            }
        };
        self.lexer.report_error(
            format!(
                "Expected {allowed} but found {} (there are {} element{} on the stack)",
                token,
                stack_size,
                if stack_size == 1 { "" } else { "s" }
            ),
            self.lexer.get_pos(),
            token.str_len(),
        )
    }

    /// Parse the `rup`-rule.
    fn rup_rule(&mut self) -> Result<(), P::Error> {
        self.lexer.enable_dynamic_integer_parse_mode();
        let token = self.mandatory_whitespace()?;
        let constraint = self.single_constraint(token)?;
        let token = self.optional_whitespace()?;
        if self.colon_or_semicolon(token)? {
            self.process_rule(VeriPBRule::RUPRule(RUPRule::new(constraint, None)))?;
            return Ok(());
        }
        let token = self.optional_whitespace()?;
        if token == Token::Semicolon {
            self.process_rule(VeriPBRule::RUPRule(RUPRule::new(constraint, Some(vec![0]))))?;
            return Ok(());
        };
        let (token, hints) = self.constraint_ids(token, false, true)?;
        self.semicolon(token)?;
        self.process_rule(VeriPBRule::RUPRule(RUPRule::new(constraint, Some(hints))))?;
        Ok(())
    }

    /// Parse the `pbc`-rule.
    fn pbc_rule(&mut self) -> Result<(), P::Error> {
        self.lexer.enable_dynamic_integer_parse_mode();
        let token = self.mandatory_whitespace()?;
        let constraint = self.single_constraint(token)?;
        let token = self.optional_whitespace()?;
        let has_subproof = !self.colon_or_semicolon(token)?;
        self.process_rule(VeriPBRule::ProofByContradiction(ProofByContradiction::new(
            constraint,
            has_subproof,
        )))?;
        if has_subproof {
            self.subproof("pbc")
        } else {
            Ok(())
        }
    }

    /// Parse the `e`-rule.
    fn e_rule(&mut self) -> Result<(), P::Error> {
        self.lexer.enable_dynamic_integer_parse_mode();
        let token = self.mandatory_whitespace()?;
        let constraint = self.single_constraint(token)?;
        let token = self.optional_whitespace()?;
        if self.colon_or_semicolon(token)? {
            self.process_rule(VeriPBRule::EqualsRule(EqualsRule::new(
                constraint, None, false,
            )))?;
            return Ok(());
        }
        let token = self.optional_whitespace()?;
        let hint = self.constraint_id(token)?;
        self.optional_white_space_semicolon()?;
        self.process_rule(VeriPBRule::EqualsRule(EqualsRule::new(
            constraint,
            Some(hint),
            false,
        )))?;
        Ok(())
    }

    /// Parse the `i`-rule.
    fn i_rule(&mut self) -> Result<(), P::Error> {
        self.i_common(false)
    }

    /// Parse the `ia`-rule.
    fn ia_rule(&mut self) -> Result<(), P::Error> {
        self.i_common(true)
    }

    /// Parse an syntactic implication rule consisting a constraint and an optional constraint ID.
    fn i_common(&mut self, add_result: bool) -> Result<(), P::Error> {
        self.lexer.enable_dynamic_integer_parse_mode();
        let token = self.mandatory_whitespace()?;
        let constraint = self.single_constraint(token)?;
        let token = self.optional_whitespace()?;
        if self.colon_or_semicolon(token)? {
            self.process_rule(VeriPBRule::ImpliesRule(ImpliesRule::new(
                constraint, None, add_result,
            )))?;
            return Ok(());
        }
        let token = self.optional_whitespace()?;
        let hint = self.constraint_id(token)?;
        self.optional_white_space_semicolon()?;
        self.process_rule(VeriPBRule::ImpliesRule(ImpliesRule::new(
            constraint,
            Some(hint),
            add_result,
        )))?;
        Ok(())
    }

    /// Generate and forward an assertion rule, where the additional information is stored if `store_assertion_annotations` is true.
    fn process_assertion(
        &mut self,
        constraint: PBConstraintEnum,
        id_list: Option<Vec<isize>>,
        name: Option<String>,
        free_text: Option<String>,
    ) -> Result<(), P::Error> {
        let rule = if self.args.store_assertion_annotations {
            AssertionRule::new(constraint, id_list, name, free_text)
        } else {
            AssertionRule::without_annotation(constraint)
        };
        self.process_rule(VeriPBRule::AssertionRule(rule))
    }

    /// Parse the `a`-rule.
    fn a_rule(&mut self) -> Result<(), P::Error> {
        self.lexer.enable_dynamic_integer_parse_mode();
        let token = self.mandatory_whitespace()?;
        let constraint = self.single_constraint(token)?;

        let token = self.optional_whitespace()?;
        if self.colon_or_semicolon(token)? {
            return self.process_assertion(constraint, None, None, None);
        }

        // Parse optional antecedent ids.
        let (token, id_list) = match self.optional_whitespace()? {
            Token::Colon => (Token::Colon, vec![]),
            Token::Semicolon => (Token::Semicolon, vec![]),
            token if self.is_constraint_id(&token)? => {
                self.constraint_ids(token.clone(), true, false)?
            }
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected a constraint ID (label or signed integer), `:` or `;` but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        if self.colon_or_semicolon(token)? {
            return self.process_assertion(constraint, Some(id_list), None, None);
        }

        // Parse optional assertion name.
        let (token, name) = match self.optional_whitespace()? {
            Token::Colon => (Token::Colon, None),
            Token::Semicolon => (Token::Semicolon, None),
            Token::Identifier(s) => (self.optional_whitespace()?, Some(s)),
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected an identifier name, `:` or `;` but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        if self.colon_or_semicolon(token)? {
            return self.process_assertion(constraint, Some(id_list), name, None);
        }

        // Parse free-text annotation data up to the terminating `;`.
        let free_text = if self.args.store_assertion_annotations {
            Some(self.lexer.read_to_semicolon("free-text assertion data")?)
        } else {
            self.lexer.skip_to_semicolon("free-text assertion data")?;
            None
        };
        self.process_assertion(constraint, Some(id_list), name, free_text)
    }

    /// Parse the `scope`-rule.
    fn scope_rule(&mut self) -> Result<(), P::Error> {
        let scope_id = match self.mandatory_whitespace()? {
            Token::Identifier(ref s) if s == "leq" => ScopeId::LessEqual,
            Token::Identifier(ref s) if s == "geq" => ScopeId::GreaterEqual,
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected `leq` or `geq` but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        let token = self.mandatory_whitespace()?;
        self.process_rule(VeriPBRule::ScopeRule(ScopeRule::new(scope_id)))?;
        self.proof_lines(token, &Scope::Scope)?;
        let token = match self.lexer.get_next_token()? {
            token if self.is_white_space(&token) => self.optional_whitespace()?,
            Token::Semicolon => Token::Semicolon,
            token => return Err(self.lexer.report_error(
                format!(
                    "Expected mandatory whitespace (before the optional `scope`) or `;` but found {token}"
                ),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        };
        let token = match token {
            Token::Semicolon => Token::Semicolon,
            Token::Identifier(s) if s == "scope" => self.optional_whitespace()?,
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected the optional `scope` or `;` but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        self.semicolon(token)?;
        self.process_rule(VeriPBRule::EndSubproof(EndSubproof::new(None)))?;
        Ok(())
    }

    /// Parse the `proofgoal`-rule.
    fn proofgoal_rule(&mut self) -> Result<(), P::Error> {
        let (proofgoal, id) = match self.mandatory_whitespace()? {
            token @ Token::ProofgoalID(id) => (token, ProofgoalID::Internal(id)),
            token if self.is_constraint_id(&token)? => (token.clone(), ProofgoalID::Database(self.constraint_id(token)?)),
            token => return Err(self.lexer.report_error(
                format!("Expected a proofgoal ID or a constraint ID (label or signed integer) but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        };
        self.process_rule(VeriPBRule::ProofgoalRule(ProofgoalRule::new(id)))?;
        let token = self.mandatory_whitespace()?;
        self.proof_lines(token, &Scope::Proofgoal)?;
        let token = match self.lexer.get_next_token()? {
            token if self.is_white_space(&token) => self.optional_whitespace()?,
            Token::Colon => Token::Colon,
            Token::Semicolon => Token::Semicolon,
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected mandatory whitespace (before the optional {proofgoal}), `:` or `;` but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?
            }
        };
        let optional_hint = match token {
            Token::Semicolon => None,
            Token::Colon => self.subproof_hint()?,
            token if token == proofgoal => match self.optional_whitespace()? {
                Token::Semicolon => None,
                Token::Colon => self.subproof_hint()?,
                token => {
                    return Err(self.lexer.report_error(
                        format!("Expected `:` or `;` but found {token}"),
                        self.lexer.get_pos(),
                        token.str_len(),
                    ))?;
                }
            },
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected the optional {proofgoal}, `:` or `;` but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        self.process_rule(VeriPBRule::EndSubproof(EndSubproof::new(optional_hint)))?;
        Ok(())
    }

    /// Parse the footer of the proof.
    fn footer(&mut self, token: Token) -> Result<(), P::Error> {
        self.output(token)?;
        let token = self.optional_whitespace()?;
        self.conclusion(token)?;
        let token = self.optional_whitespace()?;
        self.keyword("end", token)?;
        self.space(1, true)?;
        let token = self.lexer.get_next_token()?;
        self.keyword("pseudo-Boolean", token)?;
        self.space(1, true)?;
        let token = self.lexer.get_next_token()?;
        self.keyword("proof", token)?;
        self.optional_white_space_semicolon()?;
        self.process_rule(VeriPBRule::EndProof(EndProof))?;
        Ok(())
    }

    /// Parse the `output` section.
    fn output(&mut self, token: Token) -> Result<(), P::Error> {
        self.keyword("output", token)?;
        match self.mandatory_whitespace()? {
            Token::Identifier(s) if s == "NONE" => self.output_guarantee_none(),
            Token::Identifier(s) if s == "DERIVABLE" => self.output_guarantee_other(OutputGuarantee::Derivable),
            Token::Identifier(s) if s == "EQUISATISFIABLE" => self.output_guarantee_other(OutputGuarantee::Equisatisfiable),
            Token::Identifier(s) if s == "EQUIOPTIMAL" => self.output_guarantee_other(OutputGuarantee::Equioptimal),
            Token::Identifier(s) if s == "EQUIENUMERABLE" => self.output_guarantee_other(OutputGuarantee::Equienumerable),
            token => Err(self.lexer.report_error(
                format!(
                    "Expected an output guarantee (`NONE`, `DERIVABLE`, `EQUISATISFIABLE`, `EQUIOPTIMAL`, `EQUIENUMERABLE`) but found {token}"
                ),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        }
    }

    /// Parse the output with guarantee `NONE`.
    fn output_guarantee_none(&mut self) -> Result<(), P::Error> {
        self.optional_white_space_semicolon()?;
        self.process_rule(VeriPBRule::OutputRule(OutputRule::new(
            OutputGuarantee::None,
            OutputType::None,
        )))?;
        Ok(())
    }

    /// Parse the output with other guarantees, which requires parsing the output type.
    fn output_guarantee_other(
        &mut self,
        output_guarantee: OutputGuarantee,
    ) -> Result<(), P::Error> {
        match self.mandatory_whitespace()? {
            Token::Identifier(s) if s == "FILE" => self.output_type_file(output_guarantee),
            Token::Identifier(s) if s == "CONSTRAINTS" => self.output_type_constraints(output_guarantee),
            Token::Identifier(s) if s == "IMPLICIT" => self.output_type_implicit(output_guarantee),
            Token::Identifier(s) if s == "PERMUTATION" => self.output_type_permutation(output_guarantee),
            token => Err(self.lexer.report_error(
                format!("Expected an output type (`FILE`, `CONSTRAINTS`, `IMPLICIT`, `PERMUTATION`) but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        }
    }

    /// Parse the output type `FILE`.
    fn output_type_file(&mut self, output_guarantee: OutputGuarantee) -> Result<(), P::Error> {
        self.optional_white_space_semicolon()?;
        self.process_rule(VeriPBRule::OutputRule(OutputRule::new(
            output_guarantee,
            OutputType::File,
        )))?;
        Ok(())
    }

    /// Parse the output type `CONSTRAINTS`.
    fn output_type_constraints(
        &mut self,
        _output_guarantee: OutputGuarantee,
    ) -> Result<(), P::Error> {
        let mut token = self.mandatory_whitespace()?;
        self.keyword("opb", token)?;
        self.lexer.enable_dynamic_integer_parse_mode();
        token = self.whitespace(true, false)?;
        let mut _objective = None;
        let mut constraints = Vec::new();
        loop {
            match token {
                Token::Star => self.lexer.skip_to_eol()?,
                Token::Identifier(ref s) if s == "min" || s == "max" => {
                    token = self.space_or_tab(0, false)?;
                    self.colon(token)?;
                    self.lexer.enable_dynamic_integer_parse_mode();
                    self.lexer.set_integer_parse_mode(IntegerParseMode::BitsAny);
                    token = self.space_or_tab(0, false)?;
                    (token, _objective) = self.opb_objective(token)?;
                    self.semicolon(token)?;
                    self.lexer.enable_dynamic_integer_parse_mode();
                    token = self.optional_opb_whitespace()?;
                    break;
                },
                Token::Label(_) |
                Token::Integer64(_, _) |
                Token::Integer128(_, _) |
                Token::IntegerAny(_, _) => break,
                Token::Identifier(ref s) if s == "end" => break,
                token => return Err(self.lexer.report_error(
                    format!("Expected an opb comment (starting with `*`), an obp objective (starting with `min` or `max`), an opb constraint (starting with a signed integer or relational operator), a label or `end` but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?,
            };
            token = self.optional_opb_whitespace()?;
        }
        loop {
            // A constraint carries one label for each constraint it stands for.
            let mut label_count = 0;
            while let Token::Label(_) = token {
                label_count += 1;
                token = self.space_or_tab(1, false)?;
            }
            let has_label = label_count > 0;
            match token {
                Token::Star if !has_label => self.lexer.skip_to_eol()?,
                Token::Integer64(_, _) |
                Token::Integer128(_, _) |
                Token::IntegerAny(_, _) |
                Token::GreaterEqual |
                Token::LessEqual |
                Token::Equal => {
                    let (geq_constraint, leq_constraint) = self.constraint(token, true, label_count != 1)?;
                    let constraint_count = usize::from(geq_constraint.is_some()) + usize::from(leq_constraint.is_some());
                    if has_label && label_count != constraint_count {
                        Err(self.lexer.report_error(
                            if constraint_count == 1 {
                                format!("Expected a single label, since this line stands for one constraint, but found {label_count}")
                            } else {
                                format!("Expected one label for each of the {constraint_count} constraints this line stands for but found {label_count}")
                            },
                            self.lexer.get_pos(),
                            0,
                        ))?;
                    };
                    if let Some(constraint) = geq_constraint {
                        constraints.push(constraint);
                    };
                    if let Some(constraint) = leq_constraint {
                        constraints.push(constraint);
                    };
                    self.lexer.enable_dynamic_integer_parse_mode();
                    token = self.space_or_tab(0, false)?;
                    self.semicolon(token)?;
                },
                Token::Identifier(ref s) if !has_label && s == "end" => break,
                token => return Err(self.lexer.report_error(
                    format!(
                        "Expected {}an opb constraint (starting with a signed integer or relational operator){} but found {}",
                        if has_label { "" } else { "an opb comment (starting with `*`), " },
                        if has_label { "" } else { " or `end`" },
                        token
                    ),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?,
            };
            token = self.optional_opb_whitespace()?;
        }
        self.lexer.disable_dynamic_integer_parse_mode();
        token = match self.lexer.get_next_token()? {
            token if self.is_white_space(&token) => self.optional_whitespace()?,
            Token::Semicolon => Token::Semicolon,
            token => {
                return Err(self.lexer.report_error(
                    format!(
                        "Expected mandatory whitespace (before the optional `opb`) or `;` but found {token}"
                    ),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        token = match token {
            Token::Identifier(s) if s == "opb" => self.optional_whitespace()?,
            Token::Semicolon => Token::Semicolon,
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected the optional `opb` or `;` but found {token}"),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        self.semicolon(token)?;
        self.process_rule(VeriPBRule::UnimplementedRule(UnimplementedRule::new(
            "output.CONSTRAINTS".to_string(),
        )))?;
        Ok(())
    }

    /// Parse the output type `IMPLICIT`.
    fn output_type_implicit(&mut self, output_guarantee: OutputGuarantee) -> Result<(), P::Error> {
        self.optional_white_space_semicolon()?;
        self.process_rule(VeriPBRule::OutputRule(OutputRule::new(
            output_guarantee,
            OutputType::Implicit,
        )))?;
        Ok(())
    }

    /// Parse the output type `PERMUTATION`.
    fn output_type_permutation(
        &mut self,
        _output_guarantee: OutputGuarantee,
    ) -> Result<(), P::Error> {
        let token = match self.lexer.get_next_token()? {
            token if self.is_white_space(&token) => self.optional_whitespace()?,
            Token::Semicolon => Token::Semicolon,
            token => return Err(self.lexer.report_error(
                format!("Expected mandatory whitespace (before the next constraint ID) or `;` but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        };
        let (token, _constraint_ids) = match token {
            token if self.is_constraint_id(&token)? => self.constraint_ids(token, false, false)?,
            Token::Semicolon => (Token::Semicolon, Vec::with_capacity(0)),
            token => return Err(self.lexer.report_error(
                format!(
                    "Expected a constraint ID (label or signed integer) or `;` but found {token}"
                ),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        };
        self.semicolon(token)?;
        self.process_rule(VeriPBRule::UnimplementedRule(UnimplementedRule::new(
            "output.PERMUTATION".to_string(),
        )))?;
        Ok(())
    }

    /// Parse the `conclusion` section.
    fn conclusion(&mut self, token: Token) -> Result<(), P::Error> {
        self.keyword("conclusion", token)?;
        match self.mandatory_whitespace()? {
            Token::Identifier(s) if s == "NONE" => self.conclusion_none(),
            Token::Identifier(s) if s == "SAT" => self.conclusion_sat(),
            Token::Identifier(s) if s == "UNSAT" => self.conclusion_unsat(),
            Token::Identifier(s) if s == "ENUMERATION_COMPLETE" => self.conclusion_enum_complete(),
            Token::Identifier(s) if s == "ENUMERATION_PARTIAL" => self.conclusion_enum_partial(),
            Token::Identifier(s) if s == "BOUNDS" => self.conclusion_bounds(),
            token => Err(self.lexer.report_error(
                format!(
                    "Expected a conclusion (`NONE`, `SAT`, `UNSAT`, `BOUNDS`, `ENUMERATION_COMPLETE`, or `ENUMERATION_PARTIAL`) but found {token}"
                ),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        }
    }

    /// Parse the conclusion `NONE`.
    fn conclusion_none(&mut self) -> Result<(), P::Error> {
        self.optional_white_space_semicolon()?;
        self.process_rule(VeriPBRule::ConclusionRule(ConclusionRule::new(
            ConclusionResult::None,
            None,
            None,
            None,
            None,
        )))?;
        Ok(())
    }

    /// Parse the conclusion `SAT`.
    fn conclusion_sat(&mut self) -> Result<(), P::Error> {
        let token = self.optional_whitespace()?;
        let solution_hint = if self.colon_or_semicolon(token)? {
            None
        } else {
            match self.optional_whitespace()? {
                token if self.is_literal(&token, false)? => {
                    let (token, literals) = self.literals(token, false, false, false)?;
                    self.semicolon(token)?;
                    Some(literals)
                }
                Token::Semicolon => None,
                token => {
                    return Err(self.lexer.report_error(
                        format!("Expected a literal or `;` but found {token}"),
                        self.lexer.get_pos(),
                        token.str_len(),
                    ))?;
                }
            }
        };
        self.process_rule(VeriPBRule::ConclusionRule(ConclusionRule::new(
            ConclusionResult::Satisfiable,
            None,
            None,
            None,
            solution_hint,
        )))?;
        Ok(())
    }

    /// Parse the conclusion `UNSAT`.
    fn conclusion_unsat(&mut self) -> Result<(), P::Error> {
        let token = self.optional_whitespace()?;
        let constraint_id_hint = if self.colon_or_semicolon(token)? {
            None
        } else {
            let token = self.optional_whitespace()?;
            let constraint_id = self.constraint_id(token)?;
            self.optional_white_space_semicolon()?;
            Some(constraint_id)
        };
        self.process_rule(VeriPBRule::ConclusionRule(ConclusionRule::new(
            ConclusionResult::Unsatisfiable,
            None,
            None,
            constraint_id_hint,
            None,
        )))?;
        Ok(())
    }

    /// Parse the conclusion `ENUMERATION_COMPLETE`.
    fn conclusion_enum_complete(&mut self) -> Result<(), P::Error> {
        self.lexer.enable_dynamic_integer_parse_mode();
        self.lexer.set_integer_parse_mode(IntegerParseMode::BitsAny);
        let expected_solutions = match self.mandatory_whitespace()? {
            Token::IntegerAny(_, value) if value >= BigInt::zero() => value,
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected a number of solutions (unsigned integer) but found {token}",),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        self.lexer.disable_dynamic_integer_parse_mode();
        let token = self.optional_whitespace()?;
        let constraint_id_hint = if self.colon_or_semicolon(token)? {
            None
        } else {
            let token = self.optional_whitespace()?;
            let constraint_id = self.constraint_id(token)?;
            self.optional_white_space_semicolon()?;
            Some(constraint_id)
        };
        self.process_rule(VeriPBRule::ConclusionRule(ConclusionRule::new(
            ConclusionResult::EnumerationComplete,
            Some(Bound::Bounded(expected_solutions)),
            None,
            constraint_id_hint,
            None,
        )))?;
        Ok(())
    }

    /// Parse the conclusion `ENUMERATION_PARTIAL`.
    fn conclusion_enum_partial(&mut self) -> Result<(), P::Error> {
        self.lexer.enable_dynamic_integer_parse_mode();
        self.lexer.set_integer_parse_mode(IntegerParseMode::BitsAny);
        let expected_solutions = match self.mandatory_whitespace()? {
            Token::IntegerAny(_, value) if value >= BigInt::zero() => value,
            token => {
                return Err(self.lexer.report_error(
                    format!("Expected a number of solutions (unsigned integer) but found {token}",),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?;
            }
        };
        self.lexer.disable_dynamic_integer_parse_mode();
        self.optional_white_space_semicolon()?;
        self.process_rule(VeriPBRule::ConclusionRule(ConclusionRule::new(
            ConclusionResult::EnumerationPartial,
            Some(Bound::Bounded(expected_solutions)),
            None,
            None,
            None,
        )))?;
        Ok(())
    }

    /// Parse the conclusion `BOUNDS`.
    fn conclusion_bounds(&mut self) -> Result<(), P::Error> {
        self.lexer.enable_dynamic_integer_parse_mode();
        self.lexer.set_integer_parse_mode(IntegerParseMode::BitsAny);
        let token = self.mandatory_whitespace()?;
        let lower_bound = Some(self.bound(token, false)?);
        let token = match self.lexer.get_next_token()? {
            token if self.is_white_space(&token) => self.optional_whitespace()?,
            Token::Colon => Token::Colon,
            token => {
                return Err(self.lexer.report_error(
                    format!(
                    "Expected mandatory whitespace (before the upper bound) or `:` but found {token}"
                ),
                    self.lexer.get_pos(),
                    token.str_len(),
                ))?
            }
        };
        let (token, constraint_id_hint) = if let Token::Colon = token {
            self.lexer.disable_dynamic_integer_parse_mode();
            let token = self.optional_whitespace()?;
            let constraint_id = self.constraint_id(token)?;
            self.lexer.enable_dynamic_integer_parse_mode();
            self.lexer.set_integer_parse_mode(IntegerParseMode::BitsAny);
            (self.mandatory_whitespace()?, Some(constraint_id))
        } else {
            (token, None)
        };
        let upper_bound = Some(self.bound(token, true)?);
        self.lexer.disable_dynamic_integer_parse_mode();
        let token = self.optional_whitespace()?;
        let solution_hint = if self.colon_or_semicolon(token)? {
            None
        } else {
            match self.optional_whitespace()? {
                token if self.is_literal(&token, false)? => {
                    let (token, literals) = self.literals(token, false, false, false)?;
                    self.semicolon(token)?;
                    Some(literals)
                }
                Token::Semicolon => None,
                token => {
                    return Err(self.lexer.report_error(
                        format!("Expected a literal or `;` but found {token}"),
                        self.lexer.get_pos(),
                        token.str_len(),
                    ))?;
                }
            }
        };
        self.process_rule(VeriPBRule::ConclusionRule(ConclusionRule::new(
            ConclusionResult::Bounds,
            lower_bound,
            upper_bound,
            constraint_id_hint,
            solution_hint,
        )))?;
        Ok(())
    }

    /// Parse a bound for a conclusion `BOUNDS`.
    fn bound(&mut self, token: Token, is_colon_ending: bool) -> Result<Bound, P::Error> {
        match token {
            Token::IntegerAny(_, coefficient) => Ok(Bound::Bounded(coefficient)),
            Token::Identifier(s) if s == "INF" => Ok(Bound::Unbounded),
            token => Err(self.lexer.report_error(
                format!(
                    "Expected {}a signed integer or `INF` but found {}",
                    if is_colon_ending { "`:`, " } else { "" },
                    token
                ),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        }
    }

    /// Parse the end-of-file.
    fn eof(&mut self, token: Token) -> Result<(), P::Error> {
        match token {
            Token::Eof => Ok(()),
            token => Err(self.lexer.report_error(
                format!("Expected end of file (EOF) but found {token}"),
                self.lexer.get_pos(),
                token.str_len(),
            ))?,
        }
    }
}
