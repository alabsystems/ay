use std::{
    io::{BufRead, Error, ErrorKind},
    path::Path,
    rc::Rc,
    str::FromStr,
};

use colored::Colorize;
use logos::{Lexer as LogosLexer, Logos};
use malachite_bigint::{BigInt, Sign};
use veripb_formula::prelude::*;
use veripb_rules::{
    AssertionRule, Comment, ConclusionResult, ConclusionRule, DefineOrderRule, Deletion,
    DeletionOption, DeletionOrigin, DominanceBasedStrengtheningRule, EndProof, EndSubproof,
    EndTimerRule, EqualsObjectiveRule, EqualsRule, FailRule, FormulaCheck, HeaderRule,
    IdentifierOption, ImpliesRule, Instruction, IsDeletedCheck, LoadOrderRule, MoveToCoreRule,
    ObjectiveUpdateRule, ObjectiveUpdateType, OrderAuxVariablesRule, OrderDefConstraintRule,
    OrderDefRule, OrderFreshAux1Rule, OrderFreshAux2Rule, OrderFreshRightVariablesRule,
    OrderLeftVariablesRule, OrderProofRule, OrderReflexivityRule, OrderRightVariablesRule,
    OrderSpecificationRule, OrderTransitivityRule, OrderVariablesRule, OutputGuarantee, OutputRule,
    OutputType, PolRule, ProofgoalRule, RUPRule, RedundanceBasedStrengtheningRule, SetLevelRule,
    SolutionRule, SolutionRuleOutput, StartTimerRule, StrengtheningToCoreRule, VeriPBRule,
};

use crate::{
    error::ParserError,
    io::read_line,
    opb_parser::{parse_opb_objective, parse_single_constraint},
    opb_token::OPBToken,
    pbp_parser::{legacy_v2::tokens::*, proof_processor::ProofProcessor},
};

/// Parse a substitution in VeriPB format into the [`Substitution`] data structure.
///
/// The substitution is parsed from a lexer that generates tokens of the substitution. A format of a substitution is a list of mappings. A the domain of the mapping are variables and the range of the mapping is `0`, `1`, or a literal.
pub fn parse_substitution<V: VarNameRecorder>(
    lex: &mut LogosLexer<SubstitutionToken>,
    var_names: &mut V,
) -> Result<Substitution, Error> {
    let mut sub = Substitution::default();
    while let Some(token) = lex.next() {
        // Parse the domain variable of the substitution map.
        let var = match token {
            Ok(SubstitutionToken::PositiveLit) => var_names.add_by_name(lex.slice()),
            Ok(SubstitutionToken::Semicolon) => break,
            Ok(_) => return Err(Error::new(ErrorKind::InvalidData, "Expected variable.")),
            Err(_) => return Err(Error::new(ErrorKind::InvalidData, "Unrecognized token.")),
        };

        // Parse the image of the parsed variable.
        if let Some(token) = lex.next() {
            let already_set = match token {
                Ok(SubstitutionToken::Zero) => sub.set(var, SubstitutionValue::FALSE),
                Ok(SubstitutionToken::One) => sub.set(var, SubstitutionValue::TRUE),
                Ok(SubstitutionToken::PositiveLit) => sub.set(
                    var,
                    SubstitutionValue::lit(Lit::from_var(
                        var_names.add_by_name(lex.slice()),
                        false,
                    )),
                ),
                Ok(SubstitutionToken::NegativeLit) => sub.set(
                    var,
                    SubstitutionValue::lit(Lit::from_var(
                        var_names.add_by_name(&lex.slice()[1..]),
                        true,
                    )),
                ),
                Ok(_) => {
                    return Err(Error::new(
                        ErrorKind::InvalidData,
                        "Expected '0', '1', or literal.",
                    ));
                }
                Err(_) => return Err(Error::new(ErrorKind::InvalidData, "Unrecognized token.")),
            };
            if already_set {
                return Err(Error::new(
                    ErrorKind::InvalidData,
                    "A variable is assigned twice in the substitution.",
                ));
            }
        } else {
            return Err(Error::new(
                ErrorKind::InvalidData,
                "Substitution ended unexpectedly after variable.",
            ));
        }
    }

    Ok(sub)
}

/// Parse an assignment from a lexer to a raw [`Vec<Lit>`].
///
/// This vector can be used to initialize an assignment or a propagation trail.
pub fn parse_bool_assignment_to_raw_vec<V: VarNameRecorder>(
    lex: &mut LogosLexer<AssignmentToken>,
    var_names: &mut V,
) -> Result<Vec<Lit>, Error> {
    let mut assignment = Vec::new();

    while let Some(lit) = lex.next() {
        match lit {
            Ok(AssignmentToken::PositiveVar) => {
                let var = var_names.add_by_name(lex.slice());
                assignment.push(Lit::from_var(var, false));
            }
            Ok(AssignmentToken::NegativeVar) => {
                let var = var_names.add_by_name(&lex.slice()[1..]);
                assignment.push(Lit::from_var(var, true));
            }
            Err(_) => {
                return Err(Error::new(
                    ErrorKind::InvalidData,
                    format!("The token '{}' is not a literal!", lex.slice()),
                ));
            }
        }
    }

    Ok(assignment)
}

// Constants used by `parse_output_rule`.
const DERIVABLE: &str = "DERIVABLE";
const NONE: &str = "NONE";
const FILE: &str = "FILE;";

pub struct Version2Parser<'a, P: ProofProcessor> {
    processor: &'a mut P,
    inside_order_definition: bool,
    /// Whether `end pseudo-Boolean proof` has been read.
    ///
    /// The version-3 grammar ends the file there -- anything after it is
    /// "Expected end of file (EOF) but found ...". This parser had no such
    /// notion, so it read on and executed whatever followed: a version-2 proof
    /// could carry rules after its own end marker and have them checked as part
    /// of the proof. They were checked *normally*, so nothing false was
    /// accepted, and a second `conclusion` is refused on its own terms -- but
    /// the format says those lines are not part of the proof, and the two
    /// dialects disagreeing about what a file contains is the seam that
    /// produced wrong verdicts 23 and 24.
    seen_end_proof: bool,
}

impl<'a, P: ProofProcessor> Version2Parser<'a, P> {
    pub fn new(processor: &'a mut P) -> Self {
        Self {
            processor,
            inside_order_definition: false,
            seen_end_proof: false,
        }
    }

    pub fn parse<F: AsRef<Path>, R: BufRead>(
        &mut self,
        filename: F,
        derivation_reader: R,
    ) -> Result<(), P::Error> {
        // Iterate over the lines of the proof.
        let proof_lines = derivation_reader.lines();
        for (line_number, line) in proof_lines.enumerate() {
            // Do NOT swallow this error: ending the iteration here would
            // silently drop the rest of the proof and let the checker report a
            // result for rules it never saw (bug A).
            let line = read_line(line, &filename, line_number)?;
            let lex = RuleToken::lexer(&line);
            if self.processor.should_trace(line_number) {
                println!(
                    "{}",
                    format!("line {:>4}: {}", line_number + 1, lex.source()).bright_black(),
                );
            }

            // Parse the new rule.
            let rule = self.line_to_rule(lex).map_err(|e| {
                e.add_file_and_line(filename.as_ref().to_string_lossy().to_string(), line_number)
            })?;

            // Nothing but comments may follow the end marker. See
            // `Self::seen_end_proof`.
            if self.seen_end_proof && !matches!(rule, VeriPBRule::Comment(_)) {
                return Err(ParserError::token_error(0..line.len(), "end of file")
                    .add_file_and_line(
                        filename.as_ref().to_string_lossy().to_string(),
                        line_number,
                    ))?;
            }
            if matches!(rule, VeriPBRule::EndProof(_)) {
                self.seen_end_proof = true;
            }

            self.processor.process_rule(line_number, rule)?;
        }

        Ok(())
    }

    /// Parse a line in the derivation file into a [`VeriPBRule`].
    #[inline]
    pub fn line_to_rule(
        &mut self,
        mut lex: LogosLexer<'_, RuleToken>,
    ) -> Result<VeriPBRule, ParserError> {
        if self.inside_order_definition {
            let mut lex = lex.morph();
            return match lex.next() {
                None => Ok(VeriPBRule::Comment(Comment)),
                Some(Ok(ConstraintDefRuleToken::Comment)) => Ok(VeriPBRule::Comment(Comment)),
                Some(Ok(ConstraintDefRuleToken::End)) => {
                    self.inside_order_definition = false;
                    Ok(VeriPBRule::EndSubproof(
                        self.parse_end_subproof(lex.morph(), RuleToken::EndSubproof)?,
                    ))
                }
                Some(Err(_)) => Ok(VeriPBRule::OrderDefConstraintRule(
                    self.parse_order_def_constraint(lex.morph(), RuleToken::OrderDef)?,
                )),
            };
        }

        match lex.next() {
            None => Ok(VeriPBRule::Comment(Comment)),
            Some(Ok(RuleToken::Comment)) => Ok(VeriPBRule::Comment(Comment)),
            Some(Ok(token @ RuleToken::Header)) => {
                Ok(VeriPBRule::HeaderRule(self.parse_header(lex, token)?))
            }
            Some(Ok(token @ RuleToken::CheckFormula)) => Ok(VeriPBRule::FormulaCheck(
                self.parse_formula_check(lex, token)?,
            )),
            Some(Ok(token @ RuleToken::Proofgoal)) => {
                Ok(VeriPBRule::ProofgoalRule(self.parse_proofgoal(lex, token)?))
            }
            Some(Ok(token @ RuleToken::EndSubproof)) => Ok(VeriPBRule::EndSubproof(
                self.parse_end_subproof(lex, token)?,
            )),
            Some(Ok(
                token @ (RuleToken::DelRule
                | RuleToken::SingleCharDelRule
                | RuleToken::DelFromCoreRule
                | RuleToken::DelFromDerivedRule
                | RuleToken::WipeLevel),
            )) => Ok(VeriPBRule::Deletion(self.parse_deletion(lex, token)?)),
            Some(Ok(token @ RuleToken::CoreRule)) => Ok(VeriPBRule::MoveToCoreRule(
                self.parse_move_to_core(lex, token)?,
            )),
            Some(Ok(token @ RuleToken::OutputRule)) => {
                Ok(VeriPBRule::OutputRule(self.parse_output_rule(lex, token)?))
            }
            Some(Ok(token @ RuleToken::ConclusionRule)) => Ok(VeriPBRule::ConclusionRule(
                self.parse_conclusion(lex, token)?,
            )),
            Some(Ok(token @ (RuleToken::EqualsRule | RuleToken::EqualsAddRule))) => {
                Ok(VeriPBRule::EqualsRule(self.parse_equals(lex, token)?))
            }
            Some(Ok(RuleToken::EndProof)) => Ok(VeriPBRule::EndProof(EndProof)),
            Some(Ok(token @ RuleToken::RedRule)) => Ok(
                VeriPBRule::RedundanceBasedStrengtheningRule(self.parse_red(lex, token)?),
            ),
            Some(Ok(token @ RuleToken::PolRule)) => {
                Ok(VeriPBRule::PolRule(self.parse_pol(lex, token)?))
            }
            Some(Ok(token @ (RuleToken::ImpliesRule | RuleToken::ImpliesAddRule))) => {
                Ok(VeriPBRule::ImpliesRule(self.parse_implies(lex, token)?))
            }
            Some(Ok(token @ RuleToken::RUPRule)) => {
                Ok(VeriPBRule::RUPRule(self.parse_rup(lex, token)?))
            }
            Some(Ok(token @ RuleToken::AssertionRule)) => {
                Ok(VeriPBRule::AssertionRule(self.parse_assertion(lex, token)?))
            }
            Some(Ok(token @ (RuleToken::SolRule | RuleToken::SolxRule | RuleToken::SoliRule))) => {
                Ok(VeriPBRule::SolutionRule(self.parse_solution(lex, token)?))
            }
            Some(Ok(token @ RuleToken::IsDeletedCheck)) => Ok(VeriPBRule::IsDeletedCheck(
                self.parse_is_deleted(lex, token)?,
            )),
            Some(Ok(token @ RuleToken::DomRule)) => Ok(
                VeriPBRule::DominanceBasedStrengtheningRule(self.parse_dom(lex, token)?),
            ),
            Some(Ok(token @ RuleToken::DefineOrder)) => Ok(VeriPBRule::DefineOrderRule(
                self.parse_define_order(lex, token)?,
            )),
            Some(Ok(RuleToken::OrderVariables)) => {
                Ok(VeriPBRule::OrderVariablesRule(OrderVariablesRule))
            }
            Some(Ok(token @ RuleToken::OrderLeftVariables)) => Ok(
                VeriPBRule::OrderLeftVariablesRule(self.parse_order_left_vars(lex, token)?),
            ),
            Some(Ok(token @ RuleToken::OrderRightVariables)) => Ok(
                VeriPBRule::OrderRightVariablesRule(self.parse_order_right_vars(lex, token)?),
            ),
            Some(Ok(token @ RuleToken::OrderAuxVariables)) => Ok(
                VeriPBRule::OrderAuxVariablesRule(self.parse_order_aux_vars(lex, token)?),
            ),
            Some(Ok(RuleToken::OrderDef)) => {
                self.inside_order_definition = true;
                Ok(VeriPBRule::OrderDefRule(OrderDefRule))
            }
            Some(Ok(RuleToken::OrderTransitivity)) => {
                Ok(VeriPBRule::OrderTransitivityRule(OrderTransitivityRule))
            }
            Some(Ok(RuleToken::OrderReflexivity)) => {
                Ok(VeriPBRule::OrderReflexivityRule(OrderReflexivityRule))
            }
            Some(Ok(token @ RuleToken::OrderFreshRightVars)) => Ok(
                VeriPBRule::OrderFreshRightVariablesRule(self.parse_order_fresh_right(lex, token)?),
            ),
            Some(Ok(token @ RuleToken::OrderFreshAux1)) => Ok(VeriPBRule::OrderFreshAux1Rule(
                self.parse_order_fresh_aux1(lex, token)?,
            )),
            Some(Ok(token @ RuleToken::OrderFreshAux2)) => Ok(VeriPBRule::OrderFreshAux2Rule(
                self.parse_order_fresh_aux2(lex, token)?,
            )),
            Some(Ok(RuleToken::OrderBeginProof)) => Ok(VeriPBRule::OrderProofRule(OrderProofRule)),
            Some(Ok(token @ RuleToken::LoadOrder)) => Ok(VeriPBRule::LoadOrderRule(
                self.parse_load_order(lex, token)?,
            )),
            Some(Ok(RuleToken::OrderSpecification)) => {
                Ok(VeriPBRule::OrderSpecificationRule(OrderSpecificationRule))
            }
            Some(Ok(token @ RuleToken::SetLevel)) => {
                Ok(VeriPBRule::SetLevelRule(self.parse_set_level(lex, token)?))
            }
            Some(Ok(token @ RuleToken::ObjuRule)) => Ok(VeriPBRule::ObjectiveUpdateRule(
                self.parse_objective_update(lex, token)?,
            )),
            Some(Ok(token @ RuleToken::EqualsObjective)) => Ok(VeriPBRule::EqualsObjectiveRule(
                self.parse_equal_objective(lex, token)?,
            )),
            Some(Ok(RuleToken::FailProof)) => Ok(VeriPBRule::FailRule(FailRule)),
            Some(Ok(token @ RuleToken::StrengtheningToCore)) => Ok(
                VeriPBRule::StrengtheningToCoreRule(self.parse_strengthening_to_core(lex, token)?),
            ),
            Some(Ok(token @ RuleToken::EndTimer)) => {
                Ok(VeriPBRule::EndTimerRule(self.parse_end_timer(lex, token)?))
            }
            Some(Ok(token @ RuleToken::StartTimer)) => Ok(VeriPBRule::StartTimerRule(
                self.parse_start_timer(lex, token)?,
            )),
            Some(Err(_)) => Err(ParserError::token_error(
                lex.span(),
                "rule identifier (e.g., 'pol', 'red', 'rup', ...) or comment",
            )),
        }
    }

    #[inline]
    fn parse_header(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<HeaderRule, ParserError> {
        let mut lex = lex.morph();
        let major = IntegerToken::parse(&mut lex)?;
        // Skip the dot separating major and minor version.
        lex.bump(1);
        let minor = IntegerToken::parse(&mut lex)?;
        self.processor.process_version(major as i64, minor as i64);

        Ok(HeaderRule)
    }

    fn parse_assertion(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<AssertionRule, ParserError> {
        let mut lex = lex.morph();
        let (geq_constraint, leq_constraint) = parse_single_constraint(&mut lex, self.processor)?;
        if leq_constraint.is_some() {
            Err(ParserError::token_error(
                0..lex.span().end,
                "inequality constraint",
            ))
        } else {
            let mut lex = lex.morph();
            match IntegerToken::parse_optional(&mut lex)? {
                Some(integer) => {
                    let mut hint = vec![0, integer];
                    while let Some(integer) = IntegerToken::parse_optional(&mut lex)? {
                        hint.push(integer);
                    }
                    Ok(AssertionRule::without_annotation(geq_constraint))
                }
                None => Ok(AssertionRule::without_annotation(geq_constraint)),
            }
        }
    }

    #[inline]
    pub fn parse_move_to_core(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<MoveToCoreRule, ParserError> {
        let mut lex = lex.morph();
        let option = parse_identifier_option(&mut lex)?;
        let mut rule = MoveToCoreRule::new(option, Vec::new());
        match rule.identifier_option {
            IdentifierOption::Id => {
                let mut lex = lex.morph();
                while let Some(constraint_id) = IntegerToken::parse_optional(&mut lex)? {
                    rule.constraint_ids.push(constraint_id);
                }
            }
            IdentifierOption::Range => {
                let mut lex = lex.morph();
                rule.constraint_ids.push(IntegerToken::parse(&mut lex)?);
                rule.constraint_ids.push(IntegerToken::parse(&mut lex)?);
            }
            IdentifierOption::Specification => {
                return Err(ParserError::token_error(lex.span(), "'id' or 'range'"));
            }
        }

        Ok(rule)
    }

    #[inline]
    pub fn parse_define_order(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<DefineOrderRule, ParserError> {
        Ok(DefineOrderRule {
            name: Name::parse(&mut lex.morph())?,
        })
    }

    pub fn parse_deletion(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        token: RuleToken,
    ) -> Result<Deletion, ParserError> {
        match token {
            RuleToken::WipeLevel => {
                let mut lex = lex.morph();
                let level = IntegerToken::parse(&mut lex)?;
                if level.is_negative() {
                    return Err(ParserError::token_error(lex.span(), "non-negative integer"));
                }
                Ok(Deletion {
                    identifier: DeletionOption::Wipe(level as usize),
                    witness: Substitution::default(),
                    has_subproof: false,
                    origin: DeletionOrigin::Unknown,
                })
            }
            RuleToken::SingleCharDelRule
            | RuleToken::DelFromCoreRule
            | RuleToken::DelFromDerivedRule => {
                let origin = match token {
                    RuleToken::DelFromCoreRule => DeletionOrigin::Core,
                    RuleToken::DelFromDerivedRule => DeletionOrigin::Derived,
                    _ => DeletionOrigin::Unknown,
                };
                let mut constraint_ids = Vec::new();
                let mut lex = lex.morph();
                while let Some(constraint_id) = IntegerOrSemicolonToken::parse(&mut lex)? {
                    constraint_ids.push(constraint_id);
                }
                constraint_ids.sort_unstable();
                constraint_ids.dedup();
                let mut lex = lex.morph();
                let witness = parse_substitution(&mut lex, self.processor)?;
                let has_subproof = SubproofBeginToken::parsed_begin(&mut lex.morph())?;
                Ok(Deletion {
                    identifier: DeletionOption::Id(constraint_ids),
                    witness,
                    has_subproof,
                    origin,
                })
            }
            _ => {
                // V2RuleToken::DelRule
                let mut lex = lex.morph();
                let witness;
                let has_subproof;
                let identifier = match parse_identifier_option(&mut lex)? {
                    IdentifierOption::Id => {
                        let mut constraint_ids = Vec::new();
                        let mut lex = lex.morph();
                        while let Some(constraint_id) = IntegerOrSemicolonToken::parse(&mut lex)? {
                            constraint_ids.push(constraint_id);
                        }
                        constraint_ids.sort_unstable();
                        constraint_ids.dedup();
                        let mut lex = lex.morph();
                        witness = parse_substitution(&mut lex, self.processor)?;
                        has_subproof = SubproofBeginToken::parsed_begin(&mut lex.morph())?;
                        DeletionOption::Id(constraint_ids)
                    }
                    IdentifierOption::Range => {
                        let mut lex = lex.morph();
                        let start_id = IntegerToken::parse(&mut lex)?;
                        let end_id = IntegerToken::parse(&mut lex)?;
                        let mut lex = lex.morph();
                        witness = parse_substitution(&mut lex, self.processor)?;
                        has_subproof = SubproofBeginToken::parsed_begin(&mut lex.morph())?;
                        DeletionOption::Range((start_id, end_id))
                    }
                    IdentifierOption::Specification => {
                        let mut lex = lex.morph();
                        let (constraint, leq_constraint) =
                            parse_single_constraint(&mut lex, self.processor)?;
                        if leq_constraint.is_some() {
                            return Err(ParserError::token_error(
                                0..lex.span().end,
                                "inequality constraint",
                            ));
                        }
                        let mut lex = lex.morph();
                        witness = parse_substitution(&mut lex, self.processor)?;
                        has_subproof = SubproofBeginToken::parsed_begin(&mut lex.morph())?;
                        DeletionOption::Spec(Rc::new(DBConstraint::from(constraint)))
                    }
                };
                Ok(Deletion {
                    identifier,
                    witness,
                    has_subproof,
                    origin: DeletionOrigin::Unknown,
                })
            }
        }
    }

    pub fn parse_dom(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<DominanceBasedStrengtheningRule, ParserError> {
        // Parse constraint.
        let mut lex = lex.morph();
        let (geq_constraint, leq_constraint) = parse_single_constraint(&mut lex, self.processor)?;
        if leq_constraint.is_some() {
            return Err(ParserError::token_error(
                0..lex.span().end,
                "inequality constraint",
            ));
        }

        // Parse witness.
        let mut lex = lex.morph();
        let witness = parse_substitution(&mut lex, self.processor)?;

        // Parse optional subproof begin.
        let has_subproof = SubproofBeginToken::parsed_begin(&mut lex.morph())?;

        Ok(DominanceBasedStrengtheningRule {
            constraint: Rc::new(geq_constraint.into()),
            witness,
            has_subproof,
        })
    }

    #[inline]
    pub fn parse_end_subproof(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<EndSubproof, ParserError> {
        Ok(EndSubproof {
            optional_hint: IntegerToken::parse_optional(&mut lex.morph())?,
        })
    }

    pub fn parse_equal_objective(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<EqualsObjectiveRule, ParserError> {
        let objective = parse_opb_objective(&mut lex.morph(), self.processor, false)?;

        Ok(EqualsObjectiveRule { objective })
    }

    #[inline]
    pub fn parse_equals(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        token: RuleToken,
    ) -> Result<EqualsRule, ParserError> {
        let add_result = token == RuleToken::EqualsAddRule;
        let mut lex = lex.morph();
        let (geq_constraint, leq_constraint) = parse_single_constraint(&mut lex, self.processor)?;
        if leq_constraint.is_some() {
            return Err(ParserError::token_error(
                0..lex.span().end,
                "inequality constraint",
            ));
        }
        let hint = IntegerToken::parse_optional(&mut lex.morph())?;
        Ok(EqualsRule {
            constraint: Rc::new(DBConstraint::from(geq_constraint)),
            hint,
            add_result,
        })
    }

    pub fn parse_formula_check(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<FormulaCheck, ParserError> {
        let size = IntegerToken::parse(&mut lex.morph())? as usize;
        Ok(FormulaCheck { size })
    }

    #[inline]
    pub fn parse_implies(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        token: RuleToken,
    ) -> Result<ImpliesRule, ParserError> {
        let add_result = token == RuleToken::ImpliesAddRule;
        let mut lex = lex.morph();
        let (geq_constraint, leq_constraint) = parse_single_constraint(&mut lex, self.processor)?;
        if leq_constraint.is_some() {
            return Err(ParserError::token_error(
                0..lex.span().end,
                "inequality constraint",
            ));
        }
        let hint = IntegerToken::parse_optional(&mut lex.morph())?;
        Ok(ImpliesRule {
            constraint: Rc::new(DBConstraint::from(geq_constraint)),
            hint,
            add_result,
        })
    }

    pub fn parse_is_deleted(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<IsDeletedCheck, ParserError> {
        let mut lex = lex.morph();
        let (geq_constraint, leq_constraint) = parse_single_constraint(&mut lex, self.processor)?;
        if leq_constraint.is_some() {
            Err(ParserError::token_error(
                0..lex.span().end,
                "inequality constraint",
            ))
        } else {
            Ok(IsDeletedCheck {
                constraint: Rc::new(DBConstraint::from(geq_constraint)),
            })
        }
    }

    pub fn parse_load_order(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<LoadOrderRule, ParserError> {
        let mut lex = lex.morph();
        let name = Name::parse_optional(&mut lex)?;

        let mut lits = Vec::new();
        let mut lex = lex.morph();
        while let Some(lit) = LiteralToken::parse_optional(&mut lex, self.processor)? {
            lits.push(lit);
        }

        Ok(LoadOrderRule { name, lits })
    }

    pub fn parse_objective_update(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<ObjectiveUpdateRule, ParserError> {
        let mut lex = lex.morph();
        let update_type = parse_objective_update_type(&mut lex)?;

        let mut lex = lex.morph();
        let objective = parse_opb_objective(&mut lex, self.processor, false)?;

        let has_subproof = SubproofBeginToken::parsed_begin(&mut lex.morph())?;

        Ok(ObjectiveUpdateRule {
            objective,
            update_type,
            has_subproof,
        })
    }

    pub fn parse_order_aux_vars(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<OrderAuxVariablesRule, ParserError> {
        let mut lex = lex.morph();
        let mut vars = Vec::new();

        while let Some(var) = VariableToken::parse_optional(&mut lex, self.processor)? {
            vars.push(var);
        }

        Ok(OrderAuxVariablesRule { vars })
    }

    pub fn parse_order_def_constraint(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<OrderDefConstraintRule, ParserError> {
        let mut lex = OPBToken::lexer(lex.source());
        let (geq_constraint, leq_constraint) = parse_single_constraint(&mut lex, self.processor)?;
        if leq_constraint.is_some() {
            Err(ParserError::token_error(
                0..lex.span().end,
                "inequality constraint",
            ))
        } else {
            Ok(OrderDefConstraintRule {
                constraint: Rc::new(DBConstraint::from(geq_constraint)),
            })
        }
    }

    pub fn parse_order_fresh_aux1(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<OrderFreshAux1Rule, ParserError> {
        let mut lex = lex.morph();
        let mut vars = Vec::new();

        while let Some(var) = VariableToken::parse_optional(&mut lex, self.processor)? {
            vars.push(var);
        }

        Ok(OrderFreshAux1Rule { vars })
    }

    pub fn parse_order_fresh_aux2(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<OrderFreshAux2Rule, ParserError> {
        let mut lex = lex.morph();
        let mut vars = Vec::new();

        while let Some(var) = VariableToken::parse_optional(&mut lex, self.processor)? {
            vars.push(var);
        }

        Ok(OrderFreshAux2Rule { vars })
    }

    pub fn parse_order_fresh_right(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<OrderFreshRightVariablesRule, ParserError> {
        let mut lex = lex.morph();
        let mut vars = Vec::new();

        while let Some(var) = VariableToken::parse_optional(&mut lex, self.processor)? {
            vars.push(var);
        }

        Ok(OrderFreshRightVariablesRule { vars })
    }

    pub fn parse_order_left_vars(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<OrderLeftVariablesRule, ParserError> {
        let mut lex = lex.morph();
        let mut vars = Vec::new();
        while let Some(var) = VariableToken::parse_optional(&mut lex, self.processor)? {
            vars.push(var);
        }

        Ok(OrderLeftVariablesRule { vars })
    }

    pub fn parse_order_right_vars(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<OrderRightVariablesRule, ParserError> {
        let mut lex = lex.morph();
        let mut vars = Vec::new();

        while let Some(var) = VariableToken::parse_optional(&mut lex, self.processor)? {
            vars.push(var);
        }

        Ok(OrderRightVariablesRule { vars })
    }

    pub fn parse_output_rule(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<OutputRule, ParserError> {
        let mut lex = lex.morph();
        let guarantee = match lex.next() {
            Some(Ok(guarantee)) => guarantee,
            _ => {
                return Err(ParserError::token_error(
                    lex.span(),
                    &format!("output guarantee (e.g. '{NONE}', '{DERIVABLE}', ...)"),
                ));
            }
        };

        let mut lex = lex.morph();
        let output_type = match lex.next() {
            Some(Ok(output_type)) => output_type,
            None => {
                if guarantee != OutputGuarantee::None {
                    return Err(ParserError::token_error(
                        lex.span(),
                        &format!("output type (e.g. '{NONE}', '{FILE}', ...)"),
                    ));
                }
                OutputType::None
            }
            _ => {
                return Err(ParserError::token_error(
                    lex.span(),
                    &format!("output type (e.g. '{NONE}', '{FILE}', ...)"),
                ));
            }
        };

        Ok(OutputRule {
            guarantee,
            output_type,
        })
    }

    #[inline]
    pub fn parse_pol(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<PolRule, ParserError> {
        let mut lex = lex.morph();
        let mut instructions = Vec::new();
        let mut integer_buf: Option<&str> = None;
        let mut var_buffer: Option<VarIdx> = None;

        while let Some(token) = lex.next() {
            if let Some(slice) = integer_buf {
                integer_buf = None;
                match token {
                    Ok(PolToken::NormalizedFormDivide) => {
                        let divisor = BigInt::from_str(slice).unwrap();
                        if divisor.sign() != Sign::Plus {
                            return Err(ParserError::token_error(
                                lex.span(),
                                "positive integer as divisor",
                            ));
                        }
                        instructions.push(Instruction::NormalizedFormDivide(divisor));
                        continue;
                    }
                    Ok(PolToken::Multiply) => {
                        let factor = BigInt::from_str(slice).unwrap();
                        if factor.sign() == Sign::Minus {
                            return Err(ParserError::token_error(
                                lex.span(),
                                "non-negative integer as factor",
                            ));
                        }
                        instructions.push(Instruction::Multiply(factor));
                        continue;
                    }
                    // `?`, not `unwrap()`: the lexeme is `[+-]?[0-9]+`, which
                    // says nothing about fitting `isize`. `p 99999999999999999999999 +`
                    // is three tokens of ordinary proof text and used to abort
                    // the process here; the version-3 parser has always
                    // reported it as a syntax error, and now so does this one.
                    _ => instructions.push(Instruction::ConstraintId(slice.parse()?)),
                }
            } else if token == Ok(PolToken::NormalizedFormDivide) || token == Ok(PolToken::Multiply)
            {
                return Err(ParserError::token_error(
                    lex.span(),
                    "integer before division or multiplication in cutting planes step",
                ));
            }

            if let Some(var_idx) = var_buffer {
                var_buffer = None;
                match token {
                    Ok(PolToken::Weaken) => {
                        instructions.push(Instruction::Weaken(var_idx));
                        continue;
                    }
                    _ => {
                        instructions.push(Instruction::LiteralAxiom(Lit::from_var(var_idx, false)));
                    }
                }
            } else if token == Ok(PolToken::Weaken) {
                return Err(ParserError::token_error(
                    lex.span(),
                    "variable name before weakening rule",
                ));
            }

            match token {
                Ok(PolToken::Integer) => integer_buf = Some(lex.slice()),
                Ok(PolToken::Var) => var_buffer = Some(self.processor.add_by_name(lex.slice())),
                Ok(PolToken::NegatedVar) => instructions.push(Instruction::LiteralAxiom(
                    Lit::from_var(self.processor.add_by_name(&lex.slice()[1..]), true),
                )),
                Ok(PolToken::Saturate) => instructions.push(Instruction::Saturate),
                Ok(PolToken::Add) => instructions.push(Instruction::Add),
                Err(_) => {
                    return Err(ParserError::token_error(
                        lex.span(),
                        "integer, literal, '+', '*', 'd', 's', or 'w'",
                    ));
                }
                _ => {}
            }
        }

        if let Some(slice) = integer_buf {
            // Same reasoning as the in-loop push above: a trailing integer
            // that does not fit `isize` is a syntax error, not an abort.
            instructions.push(Instruction::ConstraintId(slice.parse()?))
        }

        if let Some(var_idx) = var_buffer {
            instructions.push(Instruction::LiteralAxiom(Lit::from_var(var_idx, false)));
        }

        Ok(PolRule { instructions })
    }

    pub fn parse_proofgoal(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<ProofgoalRule, ParserError> {
        let mut lex = lex.morph();
        let proofgoal_id = match lex.next() {
            Some(Ok(proofgoal_id)) => proofgoal_id,
            _ => return Err(ParserError::token_error(lex.span(), "proofgoal identifier")),
        };
        Ok(ProofgoalRule { proofgoal_id })
    }

    pub fn parse_red(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<RedundanceBasedStrengtheningRule, ParserError> {
        // Parse constraint.
        let mut lex = lex.morph();
        let (geq_constraint, leq_constraint) = parse_single_constraint(&mut lex, self.processor)?;
        if leq_constraint.is_some() {
            return Err(ParserError::token_error(
                0..lex.span().end,
                "inequality constraint",
            ));
        }

        // Parse witness.
        let mut lex = lex.morph();
        let witness = parse_substitution(&mut lex, self.processor)?;

        // Parse optional subproof begin.
        let has_subproof = SubproofBeginToken::parsed_begin(&mut lex.morph())?;

        Ok(RedundanceBasedStrengtheningRule {
            constraint: Rc::new(geq_constraint.into()),
            witness,
            has_subproof,
        })
    }

    pub fn parse_rup(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<RUPRule, ParserError> {
        let mut lex = lex.morph();
        let (geq_constraint, leq_constraint) = parse_single_constraint(&mut lex, self.processor)?;
        if leq_constraint.is_some() {
            Err(ParserError::token_error(
                0..lex.span().end,
                "inequality constraint",
            ))
        } else {
            let mut lex = lex.morph();
            match RUPHint::parse_optional(&mut lex)? {
                Some(integer) => {
                    let mut hint = vec![0, integer];
                    while let Some(integer) = RUPHint::parse_optional(&mut lex)? {
                        hint.push(integer);
                    }
                    Ok(RUPRule {
                        constraint: Rc::new(DBConstraint::from(geq_constraint)),
                        hint: Some(hint),
                    })
                }
                None => Ok(RUPRule {
                    constraint: Rc::new(DBConstraint::from(geq_constraint)),
                    hint: None,
                }),
            }
        }
    }

    #[inline]
    pub fn parse_set_level(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<SetLevelRule, ParserError> {
        let mut lex = lex.morph();
        let level = IntegerToken::parse(&mut lex)?;
        if level.is_negative() {
            return Err(ParserError::token_error(lex.span(), "non-negative integer"));
        }
        Ok(SetLevelRule {
            level: level as usize,
        })
    }

    pub fn parse_solution(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        token: RuleToken,
    ) -> Result<SolutionRule, ParserError> {
        let rule_output = match token {
            RuleToken::SolxRule => SolutionRuleOutput::Excluding,
            RuleToken::SoliRule => SolutionRuleOutput::Improving,
            _ => SolutionRuleOutput::None,
        };
        let solution = parse_bool_assignment_to_raw_vec(&mut lex.morph(), self.processor)?;

        Ok(SolutionRule {
            solution,
            rule_output,
            objective_value: None,
        })
    }

    #[inline]
    pub fn parse_strengthening_to_core(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<StrengtheningToCoreRule, ParserError> {
        let mut lex = lex.morph();
        match lex.next() {
            Some(Ok(OptionType::On)) => Ok(StrengtheningToCoreRule::new(true)),
            Some(Ok(OptionType::Off)) => Ok(StrengtheningToCoreRule::new(false)),
            _ => Err(ParserError::token_error(lex.span(), "`on` or `off`")),
        }
    }

    #[inline]
    pub fn parse_end_timer(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<EndTimerRule, ParserError> {
        Ok(EndTimerRule {
            name: Name::parse(&mut lex.morph())?,
        })
    }

    #[inline]
    pub fn parse_start_timer(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<StartTimerRule, ParserError> {
        Ok(StartTimerRule {
            name: Name::parse(&mut lex.morph())?,
        })
    }

    pub fn parse_conclusion(
        &mut self,
        lex: LogosLexer<'_, RuleToken>,
        _token: RuleToken,
    ) -> Result<ConclusionRule, ParserError> {
        let mut lex = lex.morph();
        match lex.next() {
            Some(Ok(ConclusionResult::None)) => Ok(ConclusionRule::new(
                ConclusionResult::None,
                None,
                None,
                None,
                None,
            )),
            Some(Ok(ConclusionResult::Unsatisfiable)) => {
                let mut rule =
                    ConclusionRule::new(ConclusionResult::Unsatisfiable, None, None, None, None);
                let mut lex = lex.morph();
                match lex.next() {
                    Some(Ok(V2ConclusionData::Hint)) => {
                        rule.constraint_id_hint = Some(IntegerToken::parse(&mut lex.morph())?)
                    }
                    None => {}
                    _ => {
                        return Err(ParserError::token_error(
                            lex.span(),
                            "':' to start hint or end-of-line",
                        ));
                    }
                }
                Ok(rule)
            }
            Some(Ok(ConclusionResult::Satisfiable)) => {
                let mut rule =
                    ConclusionRule::new(ConclusionResult::Satisfiable, None, None, None, None);
                let mut lex = lex.morph();
                match lex.next() {
                    Some(Ok(V2ConclusionData::Hint)) => {
                        rule.solution_hint = Some(parse_bool_assignment_to_raw_vec(
                            &mut lex.morph(),
                            self.processor,
                        )?);
                    }
                    None => {}
                    _ => {
                        return Err(ParserError::token_error(
                            lex.span(),
                            "':' to start hint or end-of-line",
                        ));
                    }
                }
                Ok(rule)
            }
            Some(Ok(ConclusionResult::Bounds)) => {
                let mut rule =
                    ConclusionRule::new(ConclusionResult::Bounds, None, None, None, None);
                let mut lex = lex.morph();
                match lex.next() {
                    Some(Ok(V2ConclusionData::Bound(bound))) => {
                        rule.lower_bound_or_count = Some(bound)
                    }
                    _ => {
                        return Err(ParserError::token_error(
                            lex.span(),
                            "integer or 'INF' for lower bound",
                        ));
                    }
                }
                rule.upper_bound = match lex.next() {
                    Some(Ok(V2ConclusionData::Bound(bound))) => Some(bound),
                    Some(Ok(V2ConclusionData::Hint)) => {
                        let mut lex_inner = lex.morph();
                        rule.constraint_id_hint = Some(IntegerToken::parse(&mut lex_inner)?);
                        let mut lex_inner = lex_inner.morph();
                        if let Some(Ok(V2ConclusionData::Bound(bound))) = lex_inner.next() {
                            lex = lex_inner.morph();
                            Some(bound)
                        } else {
                            return Err(ParserError::token_error(
                                lex_inner.span(),
                                "constraint ID for lower bounding constraint",
                            ));
                        }
                    }
                    _ => {
                        return Err(ParserError::token_error(
                            lex.span(),
                            "':' for hint or integer or 'INF' for upper bound",
                        ));
                    }
                };
                match lex.next() {
                    Some(Ok(V2ConclusionData::Hint)) => {
                        rule.solution_hint = Some(parse_bool_assignment_to_raw_vec(
                            &mut lex.morph(),
                            self.processor,
                        )?);
                    }
                    None => {}
                    _ => {
                        return Err(ParserError::token_error(
                            lex.span(),
                            "':' to start hint or end-of-line",
                        ));
                    }
                }
                Ok(rule)
            }
            _ => Err(ParserError::token_error(
                lex.span(),
                "conclusion result 'NONE', 'UNSAT', 'SAT', or 'BOUNDS'",
            )),
        }
    }
}

pub fn parse_objective_update_type(
    lex: &mut LogosLexer<ObjectiveUpdateType>,
) -> Result<ObjectiveUpdateType, ParserError> {
    match lex.next() {
        Some(Ok(option)) => Ok(option),
        _ => Err(ParserError::token_error(lex.span(), "'new', or 'diff'")),
    }
}

pub fn parse_identifier_option(
    lex: &mut LogosLexer<IdentifierOption>,
) -> Result<IdentifierOption, ParserError> {
    match lex.next() {
        Some(Ok(option)) => Ok(option),
        _ => Err(ParserError::token_error(
            lex.span(),
            "'id', 'range', 'spec', or 'find'",
        )),
    }
}
