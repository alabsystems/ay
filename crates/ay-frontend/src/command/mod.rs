// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB commands
//!
//! Represents and parses SMT-LIB 2.6 commands.

mod datatype;
mod fixedpoint;
mod sygus;
mod tactic;
mod term;

pub use datatype::{ConstructorDec, DatatypeDec, SelectorDec, SortDec};
pub use sygus::{SygusGrammar, SygusGrammarRule};
pub use tactic::{ApplyTactic, ParamValue, Probe, ProbeCmp, SUPPORTED_TACTIC_NAMES};
pub use term::{Constant, MatchPattern, ParsedConstant, Term};

use crate::sexp::{ParseError, SExpr, PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE};

/// An SMT-LIB parsed sort AST.
///
/// This is the parser-level, string-based representation used by
/// [`Command`]. It is intentionally separate from the native semantic
/// [`ay_core::Sort`] used by solver APIs.
///
/// Prefer the [`ParsedSort`] alias when importing both frontend and native
/// sort types in the same module.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Sort {
    /// A simple sort (Bool, Int, Real, etc.)
    Simple(String),
    /// A parameterized sort (Array Int Int, BitVec 32, etc.)
    Parameterized(String, Vec<Self>),
    /// An indexed sort (_ BitVec 32)
    Indexed(String, Vec<String>),
}

/// Compatibility alias for [`Sort`] that makes the parser/native distinction
/// explicit at import sites.
///
/// `ParsedSort` and [`Sort`] are the same type. The alias avoids local import
/// collisions with native solver sorts such as [`ay_core::Sort`] or
/// `ay::Sort` without breaking existing `ay_frontend::Sort` users.
pub type ParsedSort = Sort;

impl Sort {
    /// Parse a sort from an S-expression
    pub fn from_sexp(sexp: &SExpr) -> Result<Self, ParseError> {
        // Stack-safety guard for deeply nested parameterized sorts, e.g.
        // `(Array (Array (Array ... )))` — mirrors `Term::from_sexp` (#4602).
        stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || {
            Self::from_sexp_inner(sexp)
        })
    }

    fn from_sexp_inner(sexp: &SExpr) -> Result<Self, ParseError> {
        match sexp {
            SExpr::Symbol(name) => Ok(Self::Simple(name.clone())),
            SExpr::List(items) if !items.is_empty() => {
                // Check for indexed identifier (_ name index+)
                if items[0].is_symbol("_") && items.len() >= 2 {
                    let name = items[1]
                        .as_symbol()
                        .ok_or_else(|| ParseError::new("Expected symbol in indexed sort"))?;
                    let indices: Result<Vec<_>, _> = items[2..]
                        .iter()
                        .map(|s| match s {
                            SExpr::Numeral(n) => Ok(n.clone()),
                            SExpr::Symbol(s) => Ok(s.clone()),
                            _ => Err(ParseError::new(
                                "Expected numeral or symbol in indexed sort",
                            )),
                        })
                        .collect();
                    Ok(Self::Indexed(name.to_string(), indices?))
                } else {
                    // Parameterized sort
                    let name = items[0]
                        .as_symbol()
                        .ok_or_else(|| ParseError::new("Expected symbol as sort constructor"))?;
                    let params: Result<Vec<_>, _> =
                        items[1..].iter().map(Self::from_sexp).collect();
                    Ok(Self::Parameterized(name.to_string(), params?))
                }
            }
            _ => Err(ParseError::new(format!("Invalid sort: {sexp}"))),
        }
    }
}

/// A function declaration: (name, parameters, return sort)
/// Used in define-funs-rec for mutually recursive function definitions.
pub(crate) type FuncDeclaration = (String, Vec<(String, Sort)>, Sort);

/// An SMT-LIB command
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum Command {
    /// `(set-logic <symbol>)`
    SetLogic(String),
    /// `(set-option <keyword> <value>)`
    SetOption(String, SExpr),
    /// `(set-info <keyword> <value>)`
    SetInfo(String, SExpr),
    /// `(declare-sort <symbol> <numeral>)`
    DeclareSort(String, u32),
    /// `(define-sort <symbol> (<symbol>*) <sort>)`
    DefineSort(String, Vec<String>, Sort),
    /// `(declare-datatype <symbol> <datatype_dec>)`
    DeclareDatatype(String, DatatypeDec),
    /// `(declare-datatypes (<sort_dec>+) (<datatype_dec>+))`
    DeclareDatatypes(Vec<SortDec>, Vec<DatatypeDec>),
    /// `(declare-fun <symbol> (<sort>*) <sort>)`
    DeclareFun(String, Vec<Sort>, Sort),
    /// `(declare-const <symbol> <sort>)`
    DeclareConst(String, Sort),
    /// `(declare-var <symbol> <sort>)` - SyGuS input variable declaration.
    ///
    /// Also used by the Z3 fixedpoint (CHC) surface: a `declare-var` there is a
    /// universally-quantified rule variable, which has the same shape.
    DeclareVar(String, Sort),
    /// `(declare-rel <symbol> (<sort>*))` - Z3 fixedpoint relation declaration.
    ///
    /// Declares a Bool-valued relation (CHC predicate). The return sort is
    /// implicitly `Bool`.
    DeclareRel(String, Vec<Sort>),
    /// `(rule <term>)` - Z3 fixedpoint Horn rule.
    ///
    /// The term is a Horn implication `(=> body head)` or a bare relation
    /// application (an initiation fact) over declared relations and rule
    /// variables.
    Rule(Term),
    /// `(query <term>)` - Z3 fixedpoint reachability query.
    ///
    /// The term is a relation application (or bare nullary relation symbol).
    /// Reachability of the query relation is decided by the CHC engine; the
    /// fixedpoint sat/unsat polarity is the inverse of plain HORN.
    Query(Term),
    /// `(define-fun <symbol> (<sorted_var>*) <sort> <term>)`
    DefineFun(String, Vec<(String, Sort)>, Sort, Term),
    /// `(define-fun-rec <symbol> (<sorted_var>*) <sort> <term>)`
    DefineFunRec(String, Vec<(String, Sort)>, Sort, Term),
    /// `(define-funs-rec (<func_dec>+) (<term>+))`
    /// where `func_dec = (<symbol> (<sorted_var>*) <sort>)`
    DefineFunsRec(Vec<FuncDeclaration>, Vec<Term>),
    /// `(synth-fun <symbol> (<sorted_var>*) <sort> [<grammar>])`
    SynthFun(String, Vec<(String, Sort)>, Sort, Option<SygusGrammar>),
    /// `(synth-inv <symbol> (<sorted_var>*) [<grammar>])`
    SynthInv(String, Vec<(String, Sort)>, Option<SygusGrammar>),
    /// `(constraint <term>)`
    SygusConstraint(Term),
    /// `(inv-constraint <inv> <pre> <trans> <post>)`
    InvConstraint(String, String, String, String),
    /// `(check-synth)`
    CheckSynth,
    /// `(assert <term>)`
    Assert(Term),
    /// `(assert-soft <term> [:weight <numeral>] [:id <symbol>])` - Z3 MaxSMT extension.
    ///
    /// Registers a *soft* constraint: unlike [`Command::Assert`], the term need
    /// not hold in a satisfying model. At `check-sat` the solver minimizes the
    /// total `weight` of violated soft constraints subject to the hard
    /// assertions (Weighted Partial MaxSMT). `weight` defaults to `1` when the
    /// `:weight` attribute is absent; `:id` is an optional group label.
    AssertSoft {
        /// The Boolean term that should ideally be satisfied.
        term: Term,
        /// Penalty incurred when the term is violated (default 1).
        weight: u64,
        /// Optional group label (`:id`).
        id: Option<String>,
    },
    /// `(maximize <term>)` - Z3 optimization extension
    Maximize(Term),
    /// `(minimize <term>)` - Z3 optimization extension
    Minimize(Term),
    /// `(check-sat)`
    CheckSat,
    /// `(check-sat-assuming (<literal>*))`
    CheckSatAssuming(Vec<Term>),
    /// `(get-model)`
    GetModel,
    /// `(get-objectives)` - Z3 optimization extension
    GetObjectives,
    /// `(get-objective-certificates)` - AY extension (#lra-opt-cert): dual
    /// (Farkas) optimality certificates for the last optimizing check-sat.
    GetObjectiveCertificates,
    /// `(get-value (<term>+))`. Each entry is the term's ORIGINAL SMT-LIB text
    /// (echoed verbatim as the key, per the SMT-LIB spec) paired with its parsed
    /// `Term` (evaluated against the model). Keeping the original text avoids
    /// echoing an internally-rewritten form — e.g. a single-constructor datatype
    /// constant `w` is eagerly eliminated to `(wrap <field>)`, which must NOT
    /// leak into the `(get-value ...)` key.
    GetValue(Vec<(String, Term)>),
    /// `(eval <term>)` - Z3 extension.
    ///
    /// Shorthand for `(get-value (<term>))` of a single term: evaluates the
    /// term in the current model after a satisfiable `check-sat` and prints
    /// just the resulting value (no `(term value)` pairing). Z3 historically
    /// exposes this spelling for interactive use.
    Eval(Term),
    /// `(get-consequences (<assumption>*) (<literal>*))` - Z3 extension.
    ///
    /// Given background assumptions and a list of candidate literals, returns
    /// the subset of literals *implied* by the asserted formulas conjoined with
    /// the assumptions. A literal `L` is a consequence exactly when
    /// `assertions /\ assumptions /\ ~L` is unsatisfiable. Implemented as a
    /// sound under-approximation: a literal is reported only when that
    /// entailment check is genuinely UNSAT; literals whose check is SAT or
    /// `unknown` are omitted.
    GetConsequences(Vec<Term>, Vec<Term>),
    /// `(get-unsat-core)`
    GetUnsatCore,
    /// `(get-unsat-core :farkas)` -- AY extension (#8769).
    ///
    /// Returns the UNSAT core with per-entry Farkas coefficients for LRA/LIA
    /// theory contributions. Entries for theories without a Farkas-style
    /// certificate are emitted as plain names, keeping the command
    /// backwards-compatible for non-arithmetic cores.
    GetUnsatCoreWithFarkas,
    /// `(get-unsat-assumptions)`
    GetUnsatAssumptions,
    /// `(get-proof)`
    GetProof,
    /// `(get-assertions)`
    GetAssertions,
    /// `(get-assignment)`
    GetAssignment,
    /// `(get-info <keyword>)`
    GetInfo(String),
    /// `(get-option <keyword>)`
    GetOption(String),
    /// `(push <numeral>)`
    Push(u32),
    /// `(pop <numeral>)`
    Pop(u32),
    /// `(reset)`
    Reset,
    /// `(reset-assertions)`
    ResetAssertions,
    /// `(exit)`
    Exit,
    /// `(echo <string>)`
    Echo(String),
    /// `(simplify <term>)` - Z3 extension
    Simplify(Term),
    /// `(get-interpolant <term-A> <term-B>)` - Z3/SeaHorn/KLEE extension.
    ///
    /// Computes a Craig interpolant `I` for the pair `(A, B)` where the
    /// conjunction `A /\ B` is unsatisfiable: `A => I`, `I /\ B` is UNSAT, and
    /// `I` ranges only over symbols shared by `A` and `B`. The two terms are the
    /// formulas (or `(and ...)` groupings) to interpolate over.
    GetInterpolant(Term, Term),
    /// `(compute-interpolant <term-A> <term-B>)` - Z3 extension.
    ///
    /// Alias of [`Command::GetInterpolant`]: same Craig-interpolant semantics.
    /// Z3 historically exposes both spellings; both are accepted here.
    ComputeInterpolant(Term, Term),
    /// `(get-abduct <name> <goal>)` - SMT-LIB / cvc5 / Z3 extension (abduction).
    ///
    /// Given the current background assertions `A` and a Boolean goal `G`, find
    /// a formula `C` (the *abduct*) such that `A /\ C` is satisfiable and
    /// `A /\ C => G` (equivalently `A /\ C /\ not G` is unsatisfiable). The
    /// first field is the name to bind the abduct to in the response; the second
    /// is the goal term `G`. An optional grammar argument is accepted and
    /// ignored (AY synthesizes from a fixed internal candidate grammar).
    GetAbduct(String, Term),
    /// `(apply <tactic>)` - Z3 tactic surface.
    ///
    /// Applies a goal-to-goal [`ApplyTactic`] to the *current* goal (the set of
    /// assertions) and prints the resulting goal(s) in Z3's `(goals (goal ...))`
    /// shape. It never emits a sat/unsat verdict and — crucially — never mutates
    /// the real assertion stack: a subsequent `(check-sat)` still solves the
    /// original problem. Every supported tactic is equivalence-preserving, so
    /// the printed goal has exactly the same models as the input.
    Apply(ApplyTactic),
}

impl Command {
    /// Parse a command from an S-expression
    pub fn from_sexp(sexp: &SExpr) -> Result<Self, ParseError> {
        let items = sexp
            .as_list()
            .ok_or_else(|| ParseError::new("Command must be a list"))?;

        if items.is_empty() {
            return Err(ParseError::new("Empty command"));
        }

        let cmd = items[0]
            .as_symbol()
            .ok_or_else(|| ParseError::new("Command name must be a symbol"))?;

        match cmd {
            "set-logic" => {
                let logic = items
                    .get(1)
                    .and_then(|s| s.as_symbol())
                    .ok_or_else(|| ParseError::new("set-logic requires logic name"))?;
                Ok(Self::SetLogic(logic.to_string()))
            }
            "set-option" => {
                if items.len() < 3 {
                    return Err(ParseError::new("set-option requires keyword and value"));
                }
                let keyword = match &items[1] {
                    SExpr::Keyword(k) => k.clone(),
                    _ => return Err(ParseError::new("set-option requires keyword")),
                };
                Ok(Self::SetOption(keyword, items[2].clone()))
            }
            "set-info" => {
                if items.len() < 3 {
                    return Err(ParseError::new("set-info requires keyword and value"));
                }
                let keyword = match &items[1] {
                    SExpr::Keyword(k) => k.clone(),
                    _ => return Err(ParseError::new("set-info requires keyword")),
                };
                Ok(Self::SetInfo(keyword, items[2].clone()))
            }
            "declare-sort" => {
                let name = items
                    .get(1)
                    .and_then(|s| s.as_symbol())
                    .ok_or_else(|| ParseError::new("declare-sort requires name"))?;
                let arity = items
                    .get(2)
                    .and_then(|s| s.as_numeral())
                    .and_then(|n| n.parse::<u32>().ok())
                    .unwrap_or(0);
                Ok(Self::DeclareSort(name.to_string(), arity))
            }
            "define-sort" => {
                let name = items
                    .get(1)
                    .and_then(|s| s.as_symbol())
                    .ok_or_else(|| ParseError::new("define-sort requires name"))?;
                let params = items
                    .get(2)
                    .and_then(|s| s.as_list())
                    .ok_or_else(|| ParseError::new("define-sort requires parameter list"))?;
                let param_names: Result<Vec<_>, _> = params
                    .iter()
                    .map(|p| {
                        p.as_symbol()
                            .map(String::from)
                            .ok_or_else(|| ParseError::new("sort parameter must be symbol"))
                    })
                    .collect();
                let sort = items
                    .get(3)
                    .ok_or_else(|| ParseError::new("define-sort requires sort definition"))?;
                Ok(Self::DefineSort(
                    name.to_string(),
                    param_names?,
                    Sort::from_sexp(sort)?,
                ))
            }
            "declare-datatype" => {
                // (declare-datatype name datatype_dec)
                let name = items
                    .get(1)
                    .and_then(|s| s.as_symbol())
                    .ok_or_else(|| ParseError::new("declare-datatype requires name"))?;
                let datatype_dec = items.get(2).ok_or_else(|| {
                    ParseError::new("declare-datatype requires datatype declaration")
                })?;
                Ok(Self::DeclareDatatype(
                    name.to_string(),
                    DatatypeDec::from_sexp(datatype_dec)?,
                ))
            }
            "declare-datatypes" => {
                // (declare-datatypes ((name1 arity1) ...) (datatype_dec1 ...))
                let sort_decs = items.get(1).and_then(|s| s.as_list()).ok_or_else(|| {
                    ParseError::new("declare-datatypes requires sort declarations")
                })?;
                let datatype_decs = items.get(2).and_then(|s| s.as_list()).ok_or_else(|| {
                    ParseError::new("declare-datatypes requires datatype declarations")
                })?;

                // Legacy pre-2.6 non-parametric syntax:
                //   (declare-datatypes () ((Name <ctor>+) ...))
                // — an EMPTY parameter list, and each datatype entry carries its
                // own name as `(Name <ctor>+)`. Modern 2.6 requires exactly one
                // `(Name arity)` sort-dec per datatype, so an empty sort-dec list
                // paired with a non-empty datatype list is UNAMBIGUOUSLY legacy
                // (modern would be a length mismatch). z3 still accepts this form;
                // rewrite it to the modern arity-0 (SortDec, DatatypeDec) shape.
                if sort_decs.is_empty() && !datatype_decs.is_empty() {
                    let mut sorts = Vec::with_capacity(datatype_decs.len());
                    let mut datatypes = Vec::with_capacity(datatype_decs.len());
                    for dec in datatype_decs {
                        let parts = dec.as_list().ok_or_else(|| {
                            ParseError::new(
                                "legacy declare-datatypes entry must be (<name> <constructor>+)",
                            )
                        })?;
                        if parts.len() < 2 {
                            return Err(ParseError::new(
                                "legacy declare-datatypes entry must be (<name> <constructor>+)",
                            ));
                        }
                        let name = parts[0].as_symbol().ok_or_else(|| {
                            ParseError::new("legacy datatype name must be a symbol")
                        })?;
                        let constructors: Result<Vec<_>, _> =
                            parts[1..].iter().map(ConstructorDec::from_sexp).collect();
                        sorts.push(SortDec {
                            name: name.to_string(),
                            arity: 0,
                        });
                        datatypes.push(DatatypeDec {
                            constructors: constructors?,
                            type_params: Vec::new(),
                        });
                    }
                    return Ok(Self::DeclareDatatypes(sorts, datatypes));
                }

                if sort_decs.len() != datatype_decs.len() {
                    return Err(ParseError::new(
                        "declare-datatypes: number of sort declarations must match datatype declarations",
                    ));
                }

                let sorts: Result<Vec<_>, _> = sort_decs.iter().map(SortDec::from_sexp).collect();
                let datatypes: Result<Vec<_>, _> =
                    datatype_decs.iter().map(DatatypeDec::from_sexp).collect();

                Ok(Self::DeclareDatatypes(sorts?, datatypes?))
            }
            "declare-fun" => {
                let name = items
                    .get(1)
                    .and_then(|s| s.as_symbol())
                    .ok_or_else(|| ParseError::new("declare-fun requires name"))?;
                let args = items
                    .get(2)
                    .and_then(|s| s.as_list())
                    .ok_or_else(|| ParseError::new("declare-fun requires argument sorts"))?;
                let arg_sorts: Result<Vec<_>, _> = args.iter().map(Sort::from_sexp).collect();
                let ret = items
                    .get(3)
                    .ok_or_else(|| ParseError::new("declare-fun requires return sort"))?;
                Ok(Self::DeclareFun(
                    name.to_string(),
                    arg_sorts?,
                    Sort::from_sexp(ret)?,
                ))
            }
            "declare-const" => {
                let name = items
                    .get(1)
                    .and_then(|s| s.as_symbol())
                    .ok_or_else(|| ParseError::new("declare-const requires name"))?;
                let sort = items
                    .get(2)
                    .ok_or_else(|| ParseError::new("declare-const requires sort"))?;
                Ok(Self::DeclareConst(name.to_string(), Sort::from_sexp(sort)?))
            }
            "declare-var" => Self::parse_declare_var(items),
            "declare-rel" => Self::parse_declare_rel(items),
            "rule" => Self::parse_rule(items),
            "query" => Self::parse_query(items),
            "define-fun" => Self::parse_define_fun(items),
            "define-const" => Self::parse_define_const(items),
            "define-fun-rec" => Self::parse_define_fun_rec(items),
            "define-funs-rec" => Self::parse_define_funs_rec(items),
            "synth-fun" => Self::parse_synth_fun(items),
            "synth-inv" => Self::parse_synth_inv(items),
            "constraint" => Self::parse_sygus_constraint(items),
            "inv-constraint" => Self::parse_inv_constraint(items),
            "check-synth" => Self::parse_check_synth(items),
            "assert" => {
                let term = items
                    .get(1)
                    .ok_or_else(|| ParseError::new("assert requires term"))?;
                Ok(Self::Assert(Term::from_sexp(term)?))
            }
            "assert-soft" => Self::parse_assert_soft(items),
            "maximize" => {
                if items.len() != 2 {
                    return Err(ParseError::new("maximize requires exactly one term"));
                }
                let term = items
                    .get(1)
                    .ok_or_else(|| ParseError::new("maximize requires term"))?;
                Ok(Self::Maximize(Term::from_sexp(term)?))
            }
            "minimize" => {
                if items.len() != 2 {
                    return Err(ParseError::new("minimize requires exactly one term"));
                }
                let term = items
                    .get(1)
                    .ok_or_else(|| ParseError::new("minimize requires term"))?;
                Ok(Self::Minimize(Term::from_sexp(term)?))
            }
            "check-sat" => Ok(Self::CheckSat),
            // Z3 tactic surface (#tactics). `(check-sat-using <tactic>)` runs a
            // user-supplied tactic to discharge the current goal. AY VALIDATES
            // the tactic argument through the shared registry (so a garbage
            // name errors exactly like z3 — `invalid tactic, unknown tactic
            // <name>`, exit 1, script continues — and z3's arity errors are
            // reproduced byte-for-byte), then DISCHARGES the goal with the
            // default sound engine: the tactic is only a search hint, and
            // routing to the default solver is always sound. Documented sound
            // divergence: z3 answers `unknown` when the named tactic alone
            // cannot finish (e.g. `(check-sat-using simplify)` on an UNSAT
            // goal); AY's engine-computed verdict is always the correct one
            // for the formula — strictly-better completeness, zero
            // wrong-verdict surface (no new decide path is introduced).
            "check-sat-using" => {
                if items.len() < 2 {
                    // z3 byte text (measured, z3 4.15.4).
                    return Err(ParseError::new("check-sat-using needs a tactic argument"));
                }
                if items.len() > 2 {
                    // z3 rejects trailing arguments here — even keywords like
                    // `:random-seed` (parameters belong INSIDE the tactic
                    // expression, e.g. `(! smt :random-seed 7)`). Both message
                    // texts measured on z3 4.15.4.
                    return Err(match &items[2] {
                        SExpr::Keyword(_) => ParseError::new("invalid keyword argument"),
                        _ => ParseError::new("invalid command argument, keyword expected"),
                    });
                }
                // Validate (shared registry — same names/messages as `apply`
                // and `Z3_mk_tactic`), then discard the hint and solve with the
                // default engine.
                ApplyTactic::parse(&items[1])?;
                Ok(Self::CheckSat)
            }
            "check-sat-assuming" => {
                let lits = items
                    .get(1)
                    .and_then(|s| s.as_list())
                    .ok_or_else(|| ParseError::new("check-sat-assuming requires literal list"))?;
                let terms: Result<Vec<_>, _> = lits.iter().map(Term::from_sexp).collect();
                Ok(Self::CheckSatAssuming(terms?))
            }
            "get-model" => Ok(Self::GetModel),
            "get-objectives" => Ok(Self::GetObjectives),
            "get-objective-certificates" => Ok(Self::GetObjectiveCertificates),
            "get-value" => {
                let terms = items
                    .get(1)
                    .and_then(|s| s.as_list())
                    .ok_or_else(|| ParseError::new("get-value requires term list"))?;
                let parsed: Result<Vec<(String, Term)>, _> = terms
                    .iter()
                    .map(|s| Term::from_sexp(s).map(|t| (s.to_raw_string(), t)))
                    .collect();
                Ok(Self::GetValue(parsed?))
            }
            "eval" => {
                // (eval <term>) -- Z3 shorthand for get-value of one term.
                if items.len() != 2 {
                    return Err(ParseError::new("eval requires exactly one term"));
                }
                Ok(Self::Eval(Term::from_sexp(&items[1])?))
            }
            "get-consequences" => Self::parse_get_consequences(items),
            "get-unsat-core" => {
                // (get-unsat-core) -- standard SMT-LIB.
                // (get-unsat-core :farkas) -- AY extension for #8769.
                match items.get(1) {
                    None => Ok(Self::GetUnsatCore),
                    Some(SExpr::Keyword(k)) if k == "farkas" || k == ":farkas" => {
                        Ok(Self::GetUnsatCoreWithFarkas)
                    }
                    Some(other) => Err(ParseError::new(format!(
                        "get-unsat-core accepts no arguments or :farkas, got {other:?}"
                    ))),
                }
            }
            "get-unsat-assumptions" => Ok(Self::GetUnsatAssumptions),
            "get-proof" => Ok(Self::GetProof),
            "get-assertions" => Ok(Self::GetAssertions),
            "get-assignment" => Ok(Self::GetAssignment),
            "get-info" => {
                let keyword = match items.get(1) {
                    Some(SExpr::Keyword(k)) => k.clone(),
                    _ => return Err(ParseError::new("get-info requires keyword")),
                };
                Ok(Self::GetInfo(keyword))
            }
            "get-option" => {
                let keyword = match items.get(1) {
                    Some(SExpr::Keyword(k)) => k.clone(),
                    _ => return Err(ParseError::new("get-option requires keyword")),
                };
                Ok(Self::GetOption(keyword))
            }
            "push" => {
                let n = items
                    .get(1)
                    .and_then(|s| s.as_numeral())
                    .and_then(|n| n.parse::<u32>().ok())
                    .unwrap_or(1);
                Ok(Self::Push(n))
            }
            "pop" => {
                let n = items
                    .get(1)
                    .and_then(|s| s.as_numeral())
                    .and_then(|n| n.parse::<u32>().ok())
                    .unwrap_or(1);
                Ok(Self::Pop(n))
            }
            "reset" => Ok(Self::Reset),
            "reset-assertions" => Ok(Self::ResetAssertions),
            "exit" => Ok(Self::Exit),
            "echo" => {
                let msg = match items.get(1) {
                    Some(SExpr::String(s)) => s.clone(),
                    _ => return Err(ParseError::new("echo requires string")),
                };
                Ok(Self::Echo(msg))
            }
            "simplify" => {
                let term = items
                    .get(1)
                    .ok_or_else(|| ParseError::new("simplify requires term"))?;
                Ok(Self::Simplify(Term::from_sexp(term)?))
            }
            "get-interpolant" => Self::parse_interpolant(items, false),
            "compute-interpolant" => Self::parse_interpolant(items, true),
            // Z3 tactic surface (#tactics). `(apply <tactic>)` applies a real
            // goal-to-goal tactic to the current goal (the assertions) and later
            // prints the *resulting* goal(s); it never emits a verdict and never
            // mutates the assertion stack. The tactic argument is parsed into a
            // structured, validated [`ApplyTactic`] — an unknown tactic name is a
            // parse error (like z3), not a silently-accepted empty goal.
            "apply" => {
                let tactic_sexp = items
                    .get(1)
                    .ok_or_else(|| ParseError::new("apply needs a tactic argument"))?;
                Ok(Self::Apply(ApplyTactic::parse(tactic_sexp)?))
            }
            "get-abduct" => Self::parse_get_abduct(items),
            _ => Err(ParseError::new(format!("Unknown command: {cmd}"))),
        }
    }

    /// Parse `(assert-soft <term> [:weight <numeral>] [:id <symbol>])`.
    ///
    /// The term is mandatory and comes first. The `:weight` and `:id`
    /// attributes are optional and may appear in either order. A missing
    /// `:weight` defaults to `1`; a `:weight` whose value is not a numeral is a
    /// parse error (matching Z3's strict attribute parsing).
    fn parse_assert_soft(items: &[SExpr]) -> Result<Self, ParseError> {
        let term_sexp = items
            .get(1)
            .ok_or_else(|| ParseError::new("assert-soft requires a term"))?;
        let term = Term::from_sexp(term_sexp)?;

        let mut weight: u64 = 1;
        let mut id: Option<String> = None;

        // Walk the trailing attribute/value pairs (any order).
        let mut idx = 2;
        while idx < items.len() {
            let keyword = match &items[idx] {
                SExpr::Keyword(k) => k.as_str(),
                other => {
                    return Err(ParseError::new(format!(
                        "assert-soft expects :weight/:id keyword attributes, got {other}"
                    )));
                }
            };
            // Keywords carry their leading colon in the SExpr representation.
            let key = keyword.trim_start_matches(':');
            let value = items.get(idx + 1).ok_or_else(|| {
                ParseError::new(format!("assert-soft attribute {keyword} requires a value"))
            })?;
            match key {
                "weight" => {
                    let numeral = value.as_numeral().ok_or_else(|| {
                        ParseError::new("assert-soft :weight requires a numeral value")
                    })?;
                    weight = numeral.parse::<u64>().map_err(|_| {
                        ParseError::new(format!(
                            "assert-soft :weight must be a non-negative integer, got {numeral}"
                        ))
                    })?;
                }
                "id" => {
                    let symbol = value.as_symbol().ok_or_else(|| {
                        ParseError::new("assert-soft :id requires a symbol value")
                    })?;
                    id = Some(symbol.to_string());
                }
                other => {
                    return Err(ParseError::new(format!(
                        "assert-soft: unknown attribute :{other}"
                    )));
                }
            }
            idx += 2;
        }

        Ok(Self::AssertSoft { term, weight, id })
    }

    /// Parse `(get-interpolant A B)` / `(compute-interpolant A B)`.
    ///
    /// Both Z3 spellings take exactly two formula arguments whose conjunction is
    /// expected to be unsatisfiable. The `compute` flag selects which command
    /// variant to construct so the two surface spellings round-trip distinctly.
    fn parse_interpolant(items: &[SExpr], compute: bool) -> Result<Self, ParseError> {
        let name = if compute {
            "compute-interpolant"
        } else {
            "get-interpolant"
        };
        if items.len() != 3 {
            return Err(ParseError::new(format!(
                "{name} requires exactly two formula arguments (A and B)"
            )));
        }
        let a = Term::from_sexp(&items[1])?;
        let b = Term::from_sexp(&items[2])?;
        if compute {
            Ok(Self::ComputeInterpolant(a, b))
        } else {
            Ok(Self::GetInterpolant(a, b))
        }
    }

    /// Parse `(get-abduct <name> <goal> [<grammar>])`.
    ///
    /// The first argument is the symbol to name the synthesized abduct; the
    /// second is the goal formula `G`. SMT-LIB also permits an optional third
    /// grammar argument restricting the abduct's vocabulary; AY accepts it for
    /// surface compatibility but ignores it (it synthesizes from its own fixed
    /// candidate grammar and validates every candidate before emitting).
    fn parse_get_abduct(items: &[SExpr]) -> Result<Self, ParseError> {
        if items.len() < 3 {
            return Err(ParseError::new(
                "get-abduct requires a name and a goal formula",
            ));
        }
        let name = items[1]
            .as_symbol()
            .ok_or_else(|| ParseError::new("get-abduct requires a symbol name"))?;
        let goal = Term::from_sexp(&items[2])?;
        // items[3..] (optional grammar) is intentionally ignored.
        Ok(Self::GetAbduct(name.to_string(), goal))
    }

    /// Parse `(get-consequences (<assumption>*) (<literal>*))`.
    ///
    /// Both arguments are S-expression lists. The first is a list of background
    /// assumption literals; the second is the list of candidate literals to test
    /// for entailment. Each element is parsed as a [`Term`], so bare Boolean
    /// symbols (`p`), negations (`(not p)`), and arbitrary Boolean applications
    /// (`(> x 0)`) are all accepted.
    fn parse_get_consequences(items: &[SExpr]) -> Result<Self, ParseError> {
        if items.len() != 3 {
            return Err(ParseError::new(
                "get-consequences requires an assumption list and a variable list",
            ));
        }
        let assumptions = items[1]
            .as_list()
            .ok_or_else(|| ParseError::new("get-consequences requires an assumption list"))?;
        let variables = items[2]
            .as_list()
            .ok_or_else(|| ParseError::new("get-consequences requires a variable list"))?;
        let assumption_terms: Result<Vec<_>, _> = assumptions.iter().map(Term::from_sexp).collect();
        let variable_terms: Result<Vec<_>, _> = variables.iter().map(Term::from_sexp).collect();
        Ok(Self::GetConsequences(assumption_terms?, variable_terms?))
    }

    fn parse_declare_var(items: &[SExpr]) -> Result<Self, ParseError> {
        if items.len() != 3 {
            return Err(ParseError::new("declare-var requires name and sort"));
        }
        let name = items[1]
            .as_symbol()
            .ok_or_else(|| ParseError::new("declare-var requires name"))?;
        let sort = Sort::from_sexp(&items[2])?;
        Ok(Self::DeclareVar(name.to_string(), sort))
    }

    fn parse_define_fun(items: &[SExpr]) -> Result<Self, ParseError> {
        let name = items
            .get(1)
            .and_then(|s| s.as_symbol())
            .ok_or_else(|| ParseError::new("define-fun requires name"))?;
        let sorted_vars = Self::parse_sorted_var_list(items.get(2), "define-fun")?;
        let ret_sort = items
            .get(3)
            .ok_or_else(|| ParseError::new("define-fun requires return sort"))?;
        let body = items
            .get(4)
            .ok_or_else(|| ParseError::new("define-fun requires body"))?;
        Ok(Self::DefineFun(
            name.to_string(),
            sorted_vars,
            Sort::from_sexp(ret_sort)?,
            Term::from_sexp(body)?,
        ))
    }

    /// `(define-const name sort value)` — z3's convenience form for a nullary
    /// `define-fun`. Desugars to `(define-fun name () sort value)`; z3's own
    /// tutorial teaches it, so consumers pasting tutorial scripts hit it.
    fn parse_define_const(items: &[SExpr]) -> Result<Self, ParseError> {
        let name = items
            .get(1)
            .and_then(|s| s.as_symbol())
            .ok_or_else(|| ParseError::new("define-const requires name"))?;
        let sort = items
            .get(2)
            .ok_or_else(|| ParseError::new("define-const requires sort"))?;
        let body = items
            .get(3)
            .ok_or_else(|| ParseError::new("define-const requires value"))?;
        Ok(Self::DefineFun(
            name.to_string(),
            Vec::new(),
            Sort::from_sexp(sort)?,
            Term::from_sexp(body)?,
        ))
    }

    fn parse_define_fun_rec(items: &[SExpr]) -> Result<Self, ParseError> {
        let name = items
            .get(1)
            .and_then(|s| s.as_symbol())
            .ok_or_else(|| ParseError::new("define-fun-rec requires name"))?;
        let sorted_vars = Self::parse_sorted_var_list(items.get(2), "define-fun-rec")?;
        let ret_sort = items
            .get(3)
            .ok_or_else(|| ParseError::new("define-fun-rec requires return sort"))?;
        let body = items
            .get(4)
            .ok_or_else(|| ParseError::new("define-fun-rec requires body"))?;
        Ok(Self::DefineFunRec(
            name.to_string(),
            sorted_vars,
            Sort::from_sexp(ret_sort)?,
            Term::from_sexp(body)?,
        ))
    }

    fn parse_define_funs_rec(items: &[SExpr]) -> Result<Self, ParseError> {
        // (define-funs-rec ((f1 ((x T)) T) (f2 ((y T)) T)) (body1 body2))
        let func_decs = items
            .get(1)
            .and_then(|s| s.as_list())
            .ok_or_else(|| ParseError::new("define-funs-rec requires function declarations"))?;
        let bodies = items
            .get(2)
            .and_then(|s| s.as_list())
            .ok_or_else(|| ParseError::new("define-funs-rec requires function bodies"))?;

        if func_decs.len() != bodies.len() {
            return Err(ParseError::new(
                "define-funs-rec: number of declarations must match number of bodies",
            ));
        }

        let mut declarations = Vec::new();
        for func_dec in func_decs {
            let dec_list = func_dec
                .as_list()
                .ok_or_else(|| ParseError::new("function declaration must be a list"))?;
            if dec_list.len() != 3 {
                return Err(ParseError::new(
                    "function declaration must be (name ((param sort)*) sort)",
                ));
            }
            let name = dec_list[0]
                .as_symbol()
                .ok_or_else(|| ParseError::new("function name must be symbol"))?;
            let sorted_vars =
                Self::parse_sorted_var_list(Some(&dec_list[1]), "define-funs-rec parameter")?;
            let ret_sort = Sort::from_sexp(&dec_list[2])?;
            declarations.push((name.to_string(), sorted_vars, ret_sort));
        }

        let parsed_bodies: Result<Vec<_>, _> = bodies.iter().map(Term::from_sexp).collect();
        Ok(Self::DefineFunsRec(declarations, parsed_bodies?))
    }

    fn parse_synth_fun(items: &[SExpr]) -> Result<Self, ParseError> {
        if !(4..=5).contains(&items.len()) {
            return Err(ParseError::new(
                "synth-fun requires name, parameters, return sort, and optional grammar",
            ));
        }
        let name = items[1]
            .as_symbol()
            .ok_or_else(|| ParseError::new("synth-fun requires name"))?;
        let sorted_vars = Self::parse_sorted_var_list(items.get(2), "synth-fun")?;
        let ret_sort = Sort::from_sexp(&items[3])?;
        let grammar = items.get(4).map(SygusGrammar::from_sexp).transpose()?;
        Ok(Self::SynthFun(
            name.to_string(),
            sorted_vars,
            ret_sort,
            grammar,
        ))
    }

    fn parse_synth_inv(items: &[SExpr]) -> Result<Self, ParseError> {
        if !(3..=4).contains(&items.len()) {
            return Err(ParseError::new(
                "synth-inv requires name, parameters, and optional grammar",
            ));
        }
        let name = items[1]
            .as_symbol()
            .ok_or_else(|| ParseError::new("synth-inv requires name"))?;
        let sorted_vars = Self::parse_sorted_var_list(items.get(2), "synth-inv")?;
        let grammar = items.get(3).map(SygusGrammar::from_sexp).transpose()?;
        Ok(Self::SynthInv(name.to_string(), sorted_vars, grammar))
    }

    fn parse_sygus_constraint(items: &[SExpr]) -> Result<Self, ParseError> {
        if items.len() != 2 {
            return Err(ParseError::new("constraint requires exactly one term"));
        }
        Ok(Self::SygusConstraint(Term::from_sexp(&items[1])?))
    }

    fn parse_inv_constraint(items: &[SExpr]) -> Result<Self, ParseError> {
        if items.len() != 5 {
            return Err(ParseError::new(
                "inv-constraint requires inv, pre, trans, and post symbols",
            ));
        }
        let symbol = |idx: usize, role: &str| {
            items[idx]
                .as_symbol()
                .map(str::to_string)
                .ok_or_else(|| ParseError::new(format!("inv-constraint {role} must be a symbol")))
        };
        Ok(Self::InvConstraint(
            symbol(1, "inv")?,
            symbol(2, "pre")?,
            symbol(3, "trans")?,
            symbol(4, "post")?,
        ))
    }

    fn parse_check_synth(items: &[SExpr]) -> Result<Self, ParseError> {
        if items.len() != 1 {
            return Err(ParseError::new("check-synth takes no arguments"));
        }
        Ok(Self::CheckSynth)
    }

    /// Parse a list of sorted variables `((name sort) ...)` from an S-expression.
    fn parse_sorted_var_list(
        sexp: Option<&SExpr>,
        context: &str,
    ) -> Result<Vec<(String, Sort)>, ParseError> {
        let params = sexp
            .and_then(|s| s.as_list())
            .ok_or_else(|| ParseError::new(format!("{context} requires parameter list")))?;
        let mut sorted_vars = Vec::new();
        for param in params {
            let param_list = param
                .as_list()
                .ok_or_else(|| ParseError::new("parameter must be (name sort)"))?;
            if param_list.len() != 2 {
                return Err(ParseError::new("parameter must be (name sort)"));
            }
            let var_name = param_list[0]
                .as_symbol()
                .ok_or_else(|| ParseError::new("parameter name must be symbol"))?;
            let var_sort = Sort::from_sexp(&param_list[1])?;
            sorted_vars.push((var_name.to_string(), var_sort));
        }
        Ok(sorted_vars)
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "tests.rs"]
mod tests;
