use std::str::FromStr;

use logos::{Lexer as LogosLexer, Logos};
use malachite_bigint::BigInt;
use veripb_formula::{
    lit::Lit,
    prelude::{VarIdx, VarNameRecorder},
};
use veripb_rules::Bound;

use crate::error::ParserError;

/// VeriPB assignment token.
///
/// A token in an assignment is either a positive variable or a negative variable.
#[derive(Debug, Logos, PartialEq, Eq)]
#[logos(skip r"[ \t\r\n]")]
pub enum AssignmentToken {
    /// Positive literal in OPB format.
    #[regex("[a-zA-Z_][_a-zA-Z0-9\\-\\^\\[\\]\\{\\}]+")]
    PositiveVar,

    /// Negative literal in OPB format.
    #[regex("~[a-zA-Z_][_a-zA-Z0-9\\-\\^\\[\\]\\{\\}]+")]
    NegativeVar,
}

/// VeriPB substitution token.
#[derive(Debug, Logos, PartialEq, Eq)]
#[logos(skip r" |\t|\r|\n|->|→")]
pub enum SubstitutionToken {
    /// Positive literals in OPB format.
    #[regex("[a-zA-Z_][_a-zA-Z0-9\\-\\^\\[\\]\\{\\}]+")]
    PositiveLit,

    /// Negative literals in OPB format.
    #[regex("~[a-zA-Z_][_a-zA-Z0-9\\-\\^\\[\\]\\{\\}]+")]
    NegativeLit,

    /// Constant 0 (false) value in a substitution. I.e., the variable before the `0` is assigned to false.
    #[token("0")]
    Zero,

    /// Constant 1 (true) value in a substitution. I.e., the variable before the `1` is assigned to true.
    #[token("1")]
    One,

    /// Token to finalize the a substitution.
    #[token(";")]
    Semicolon,
}

/// Token for the rules.
#[derive(Debug, Clone, Copy, Logos, PartialEq, Eq)]
#[logos(skip r"[ \t\r\n]")]
pub enum RuleToken {
    // Header of the proof.
    #[token("pseudo-Boolean proof version")]
    Header,

    #[regex("\\*.*", allow_greedy = true)]
    Comment,

    #[token("pol")]
    #[token("p")]
    PolRule,

    #[token("rup")]
    #[token("u")]
    RUPRule,

    #[token("a")]
    AssertionRule,

    #[token("red")]
    RedRule,

    #[token("dom")]
    DomRule,

    #[token("core")]
    CoreRule,

    #[token("del")]
    DelRule,

    #[token("d")]
    SingleCharDelRule,

    #[token("delc")]
    DelFromCoreRule,

    #[token("deld")]
    DelFromDerivedRule,

    #[token("is_deleted")]
    IsDeletedCheck,

    #[token("f")]
    CheckFormula,

    #[token("obju")]
    ObjuRule,

    #[token("e")]
    EqualsRule,

    #[token("ea")]
    EqualsAddRule,

    #[token("i")]
    ImpliesRule,

    #[token("ia")]
    ImpliesAddRule,

    #[token("sol")]
    SolRule,

    #[token("soli")]
    #[token("o")]
    SoliRule,

    #[token("solx")]
    #[token("v")]
    SolxRule,

    #[token("conclusion")]
    ConclusionRule,

    #[token("output")]
    OutputRule,

    #[token("def_order")]
    #[token("pre_order")]
    DefineOrder,

    #[token("vars")]
    OrderVariables,

    #[token("left")]
    OrderLeftVariables,

    #[token("right")]
    OrderRightVariables,

    #[token("aux")]
    OrderAuxVariables,

    #[token("def")]
    OrderDef,

    #[token("transitivity")]
    OrderTransitivity,

    #[token("reflexivity")]
    OrderReflexivity,

    #[token("proof")]
    OrderBeginProof,

    #[token("fresh_right")]
    OrderFreshRightVars,

    #[token("fresh_aux_1")]
    OrderFreshAux1,

    #[token("fresh_aux_2")]
    OrderFreshAux2,

    #[token("spec")]
    OrderSpecification,

    #[token("load_order")]
    LoadOrder,

    #[token("end")]
    #[token("qed")]
    EndSubproof,

    #[token("proofgoal")]
    Proofgoal,

    #[token("end pseudo-Boolean proof")]
    EndProof,

    #[token("#")]
    SetLevel,

    #[token("w")]
    WipeLevel,

    #[token("eobj")]
    EqualsObjective,

    #[token("fail")]
    FailProof,

    #[token("strengthening_to_core")]
    StrengtheningToCore,

    #[token("end_time")]
    EndTimer,

    #[token("start_time")]
    StartTimer,
}

#[derive(Debug, Logos, PartialEq, Eq)]
#[logos(skip r"[ \t\r\n]")]
pub enum ConstraintDefRuleToken {
    #[regex("\\*.*", allow_greedy = true)]
    Comment,

    #[token("end")]
    End,
}

// Tokens for reverse Polish notation cutting planes proofs.
#[derive(Debug, Logos, PartialEq, Eq)]
#[logos(skip r"[ \t\r\n]")]
pub enum PolToken {
    // The integer is either used as constraint ID or for division/multiplication.
    #[regex("[+-]?[0-9]+")]
    Integer,

    // OPB variable name.
    #[regex("[a-zA-Z_][_a-zA-Z0-9\\-\\^\\[\\]\\{\\}]+")]
    Var,

    // Negation symbol for a literal.
    #[regex("~[a-zA-Z_][_a-zA-Z0-9\\-\\^\\[\\]\\{\\}]+")]
    NegatedVar,

    // Saturate constraint.
    #[token("s")]
    Saturate,

    // Divide constraint in normalized form by integer.
    #[token("d")]
    NormalizedFormDivide,

    // Weaken constraint by variable.
    #[token("w")]
    Weaken,

    // Multiply constraint by integer.
    #[token("*")]
    Multiply,

    // Add two constraints together.
    #[token("+")]
    Add,
}

// Conclusion subtokens.
#[derive(Debug, Logos)]
#[logos(skip r"[ \t\r\n]")]
pub enum V2ConclusionData {
    #[token(":")]
    Hint,

    #[regex("[+-]?[0-9]+", |lex| Bound::Bounded(BigInt::from_str(lex.slice()).unwrap()))]
    #[token("INF", |_lex| Bound::Unbounded)]
    Bound(Bound),
}

#[derive(Debug, Logos, PartialEq, Eq)]
#[logos(skip r"[ \t\r\n]")]
pub enum IntegerToken {
    // Integer used for coefficients or degree (right-hand side).
    #[regex(r"[+-]?\d+")]
    Integer,
}

impl IntegerToken {
    pub fn parse_optional(
        lex: &mut LogosLexer<IntegerToken>,
    ) -> Result<Option<isize>, ParserError> {
        match lex.next() {
            Some(Ok(_)) => Ok(Some(lex.slice().parse()?)),
            Some(Err(_)) => Err(ParserError::token_error(lex.span(), "constraint ID")),
            None => Ok(None),
        }
    }

    pub fn parse(lex: &mut LogosLexer<IntegerToken>) -> Result<isize, ParserError> {
        match lex.next() {
            Some(Ok(_)) => Ok(lex.slice().parse()?),
            _ => Err(ParserError::token_error(lex.span(), "integer")),
        }
    }
}

#[derive(Debug, Logos, PartialEq, Eq)]
#[logos(skip r"[ \t\r\n]")]
pub enum RUPHint {
    // Integer used for coefficients or degree (right-hand side).
    #[regex(r"[+-]?\d+")]
    Integer,

    // The tilde symbol represents the negated constraint of a RUP step.
    #[token("~")]
    Tilde,
}

impl RUPHint {
    pub fn parse_optional(lex: &mut LogosLexer<RUPHint>) -> Result<Option<isize>, ParserError> {
        match lex.next() {
            Some(Ok(RUPHint::Integer)) => Ok(Some(lex.slice().parse()?)),
            Some(Ok(RUPHint::Tilde)) => Ok(Some(0)),
            Some(Err(_)) => Err(ParserError::token_error(lex.span(), "constraint ID")),
            None => Ok(None),
        }
    }

    pub fn parse(lex: &mut LogosLexer<RUPHint>) -> Result<isize, ParserError> {
        match lex.next() {
            Some(Ok(RUPHint::Integer)) => Ok(lex.slice().parse()?),
            Some(Ok(RUPHint::Tilde)) => Ok(0),
            _ => Err(ParserError::token_error(lex.span(), "integer")),
        }
    }
}

#[derive(Debug, Logos, PartialEq, Eq)]
#[logos(skip r"[ \t\r\n]")]
pub enum IntegerOrSemicolonToken {
    // Integer used for coefficients or degree (right-hand side).
    #[regex(r"[+-]?\d+")]
    Integer,

    // Semicolons
    #[token(";")]
    Semicolon,
}

impl IntegerOrSemicolonToken {
    pub fn parse(lex: &mut LogosLexer<Self>) -> Result<Option<isize>, ParserError> {
        match lex.next() {
            Some(Ok(Self::Integer)) => Ok(Some(lex.slice().parse().unwrap())),
            Some(Ok(Self::Semicolon)) => Ok(None),
            Some(Err(_)) => Err(ParserError::token_error(lex.span(), "constraint ID")),
            None => Ok(None),
        }
    }
}

#[derive(Debug, Logos, PartialEq, Eq)]
#[logos(skip r"[ \t\r\n]")]
pub enum SubproofBeginToken {
    #[token("begin")]
    Begin,
}

impl SubproofBeginToken {
    pub fn parsed_begin(lex: &mut LogosLexer<Self>) -> Result<bool, ParserError> {
        match lex.next() {
            Some(Ok(Self::Begin)) => Ok(true),
            None => Ok(false),
            _ => Err(ParserError::token_error(
                lex.span(),
                "'begin' or end of line",
            )),
        }
    }
}

#[derive(Debug, Logos, PartialEq, Eq)]
#[logos(skip r"[ \t\r\n]")]
pub enum Name {
    #[regex(r"[_a-zA-Z][_a-zA-Z0-9\\-\\^\\[\\]\\{\\}]*")]
    Name,
}

impl Name {
    #[inline]
    pub fn parse(lex: &mut LogosLexer<Self>) -> Result<String, ParserError> {
        match lex.next() {
            Some(Ok(Self::Name)) => Ok(lex.slice().to_string()),
            _ => Err(ParserError::token_error(
                lex.span(),
                "a name for the order or timer",
            )),
        }
    }

    #[inline]
    pub fn parse_optional(lex: &mut LogosLexer<Self>) -> Result<Option<String>, ParserError> {
        match lex.next() {
            Some(Ok(Self::Name)) => Ok(Some(lex.slice().to_string())),
            None => Ok(None),
            _ => Err(ParserError::token_error(
                lex.span(),
                "a name for the order or timer or nothing",
            )),
        }
    }
}

#[derive(Debug, Logos, PartialEq, Eq)]
#[logos(skip r"[ \t\r\n]")]
pub enum VariableToken {
    #[regex(r"[_a-zA-Z][_a-zA-Z0-9\\-\\^\\[\\]\\{\\}]+")]
    Variable,
}

impl VariableToken {
    #[inline]
    pub fn parse_optional<V: VarNameRecorder>(
        lex: &mut LogosLexer<Self>,
        var_names: &mut V,
    ) -> Result<Option<VarIdx>, ParserError> {
        match lex.next() {
            Some(Ok(Self::Variable)) => Ok(Some(var_names.add_by_name(lex.slice()))),
            None => Ok(None),
            _ => Err(ParserError::token_error(lex.span(), "variable")),
        }
    }
}

#[derive(Debug, Logos, PartialEq, Eq)]
#[logos(skip r"[ \t\r\n]")]
pub enum LiteralToken {
    // OPB variable name.
    #[regex("[a-zA-Z_][_a-zA-Z0-9\\-\\^\\[\\]\\{\\}]+")]
    Variable,

    // Negation symbol for a literal.
    #[regex("~[a-zA-Z_][_a-zA-Z0-9\\-\\^\\[\\]\\{\\}]+")]
    NegatedVariable,
}

impl LiteralToken {
    #[inline]
    pub fn parse_optional<V: VarNameRecorder>(
        lex: &mut LogosLexer<Self>,
        var_names: &mut V,
    ) -> Result<Option<Lit>, ParserError> {
        match lex.next() {
            Some(Ok(Self::Variable)) => {
                let var = var_names.add_by_name(lex.slice());
                Ok(Some(Lit::from_var(var, false)))
            }
            Some(Ok(Self::NegatedVariable)) => {
                let var = var_names.add_by_name(&lex.slice()[1..]);
                Ok(Some(Lit::from_var(var, true)))
            }
            None => Ok(None),
            _ => Err(ParserError::token_error(lex.span(), "literal")),
        }
    }
}

#[derive(Debug, Logos, PartialEq, Eq)]
#[logos(skip r"[ \t\r\n]")]
pub enum OptionType {
    #[token("on")]
    On,

    #[token("off")]
    Off,
}
