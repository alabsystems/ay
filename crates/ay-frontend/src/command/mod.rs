// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB commands
//!
//! Represents and parses SMT-LIB 2.7 commands.

mod datatype;
mod fixedpoint;
mod sygus;
mod tactic;
mod term;

pub use datatype::{ConstructorDec, DatatypeDec, SelectorDec, SortDec};
pub use sygus::{SygusGrammar, SygusGrammarRule};
pub use tactic::{ApplyTactic, ParamValue, Probe, ProbeCmp, SUPPORTED_TACTIC_NAMES};
pub use term::{Constant, Index, MatchPattern, ParsedConstant, QualifiedIdentifier, Term};

use crate::sexp::{ParseError, SExpr, PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE};
use std::collections::{HashMap, HashSet};

/// Exact regular-stream payload produced by the pinned Z3 5.0.0 `(help)`
/// command, including its one terminal line feed.
const Z3_5_HELP_OUTPUT: &str = include_str!("z3_5_help.txt");

/// Exact regular-stream payload produced by the pinned Z3 5.0.0
/// `(help-simplifier)` command, including its one terminal line feed.
///
/// This command reports a build-time registry, not live solver state. Keeping
/// the oracle snapshot beside the parser makes the versioned compatibility
/// contract explicit and avoids reconstructing almost 180 lines of parameter
/// metadata from unrelated AY implementation details.
const Z3_5_HELP_SIMPLIFIER_OUTPUT: &str = include_str!("z3_5_help_simplifier.txt");

/// Exact regular-stream payload produced by the pinned Z3 5.0.0
/// `(help-tactic)` command, including its one terminal line feed. The snapshot
/// contains the complete 118-tactic parameter registry for this exact build.
const Z3_5_HELP_TACTIC_OUTPUT: &str = include_str!("z3_5_help_tactic.txt");

fn z3_5_help_simplifier_output() -> &'static str {
    Z3_5_HELP_SIMPLIFIER_OUTPUT
        .strip_suffix('\n')
        .unwrap_or(Z3_5_HELP_SIMPLIFIER_OUTPUT)
}

fn z3_5_help_output() -> &'static str {
    Z3_5_HELP_OUTPUT
        .strip_suffix('\n')
        .unwrap_or(Z3_5_HELP_OUTPUT)
}

fn z3_5_help_tactic_output() -> &'static str {
    Z3_5_HELP_TACTIC_OUTPUT
        .strip_suffix('\n')
        .unwrap_or(Z3_5_HELP_TACTIC_OUTPUT)
}

/// Select one command's complete help block from the pinned zero-argument
/// registry transcript. Every entry begins at a line whose exact prefix is
/// ` (`; descriptions and parameter rows are more deeply indented.
fn z3_5_help_entry(name: &str) -> Option<&'static str> {
    let body = z3_5_help_output().strip_prefix('\"')?.strip_suffix('\"')?;
    let mut starts = vec![0];
    starts.extend(body.match_indices("\n (").map(|(index, _)| index + 1));

    for (entry_index, start) in starts.iter().copied().enumerate() {
        let end = starts.get(entry_index + 1).copied().unwrap_or(body.len());
        let entry = &body[start..end];
        let header = entry.strip_prefix(" (")?;
        let name_end = header
            .find(|character: char| character.is_whitespace() || character == ')')
            .unwrap_or(header.len());
        if &header[..name_end] == name {
            return Some(entry);
        }
    }
    None
}

/// Render the public `sexpr::display` grammar used by Z3 5.0.0's
/// `dbg-sexpr` command. Unlike normal SMT-LIB serialization, that debug
/// printer emits symbol payloads verbatim (even when the input was quoted)
/// and escapes only embedded double quotes in string atoms.
fn z3_5_debug_sexpr_output(sexpr: &SExpr) -> String {
    match sexpr {
        SExpr::Symbol(symbol) => symbol.clone(),
        SExpr::Keyword(keyword) => keyword.clone(),
        SExpr::Numeral(numeral) => numeral.clone(),
        SExpr::Decimal(decimal) => decimal.clone(),
        SExpr::Hexadecimal(hexadecimal) => hexadecimal.clone(),
        SExpr::Binary(binary) => binary.clone(),
        SExpr::String(string) => format!("\"{}\"", string.replace('"', "\\\"")),
        SExpr::True => "true".to_string(),
        SExpr::False => "false".to_string(),
        SExpr::List(items) => {
            let body = items
                .iter()
                .map(z3_5_debug_sexpr_output)
                .collect::<Vec<_>>()
                .join(" ");
            format!("({body})")
        }
    }
}

/// Minimal expression DAG used by the pinned Z3 debug/introspection commands.
///
/// Z3's `dbg-size` and `dbg-used-vars` operate on its parsed AST, before the
/// solver rewriters run. AY's native `TermStore` deliberately performs eager
/// Boolean/arithmetic normalization, so counting or scanning that lowered DAG
/// would lose authored nodes (`(and true false)` is the smallest example).
/// This private representation retains exactly the pieces these commands
/// inspect: hash-consed expression shape and de Bruijn-bound variables. `let`
/// is expanded while building the DAG, matching Z3's SMT2 parser.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Z3DebugNode {
    Atom(String),
    Var(u32, String),
    App(String, Vec<Self>),
    Quantifier(String, Vec<(String, String)>, Box<Self>),
}

#[derive(Clone, Debug)]
enum Z3DebugBinding {
    Bound(String),
    Let(Z3DebugNode),
}

fn z3_debug_shift_free_vars(node: &Z3DebugNode, amount: u32, cutoff: u32) -> Z3DebugNode {
    match node {
        Z3DebugNode::Atom(_) => node.clone(),
        Z3DebugNode::Var(index, sort) if *index >= cutoff => {
            Z3DebugNode::Var(index.saturating_add(amount), sort.clone())
        }
        Z3DebugNode::Var(_, _) => node.clone(),
        Z3DebugNode::App(head, arguments) => Z3DebugNode::App(
            head.clone(),
            arguments
                .iter()
                .map(|argument| z3_debug_shift_free_vars(argument, amount, cutoff))
                .collect(),
        ),
        Z3DebugNode::Quantifier(kind, declarations, body) => Z3DebugNode::Quantifier(
            kind.clone(),
            declarations.clone(),
            Box::new(z3_debug_shift_free_vars(
                body,
                amount,
                cutoff.saturating_add(declarations.len() as u32),
            )),
        ),
    }
}

fn z3_debug_symbol_node(symbol: &str, bindings: &[(String, Z3DebugBinding)]) -> Z3DebugNode {
    let mut de_bruijn_index = 0u32;
    for (name, binding) in bindings.iter().rev() {
        if name == symbol {
            return match binding {
                Z3DebugBinding::Bound(sort) => Z3DebugNode::Var(de_bruijn_index, sort.clone()),
                Z3DebugBinding::Let(value) => z3_debug_shift_free_vars(value, de_bruijn_index, 0),
            };
        }
        if matches!(binding, Z3DebugBinding::Bound(_)) {
            de_bruijn_index = de_bruijn_index.saturating_add(1);
        }
    }
    Z3DebugNode::Atom(format!("symbol:{symbol}"))
}

fn z3_debug_node(sexpr: &SExpr, bindings: &mut Vec<(String, Z3DebugBinding)>) -> Z3DebugNode {
    match sexpr {
        SExpr::Symbol(symbol) => z3_debug_symbol_node(symbol, bindings),
        SExpr::Keyword(keyword) => Z3DebugNode::Atom(format!("keyword:{keyword}")),
        SExpr::Numeral(value) => Z3DebugNode::Atom(format!("numeral:{value}")),
        SExpr::Decimal(value) => Z3DebugNode::Atom(format!("decimal:{value}")),
        SExpr::Hexadecimal(value) => Z3DebugNode::Atom(format!("hex:{value}")),
        SExpr::Binary(value) => Z3DebugNode::Atom(format!("binary:{value}")),
        SExpr::String(value) => Z3DebugNode::Atom(format!("string:{value}")),
        SExpr::True => Z3DebugNode::Atom("bool:true".to_string()),
        SExpr::False => Z3DebugNode::Atom("bool:false".to_string()),
        SExpr::List(items) if items.is_empty() => Z3DebugNode::Atom("list:()".to_string()),
        SExpr::List(items) => {
            let head = items[0].as_symbol();
            if head == Some("let") && items.len() == 3 {
                let Some(let_bindings) = items[1].as_list() else {
                    return Z3DebugNode::App(
                        "let".to_string(),
                        items[1..]
                            .iter()
                            .map(|item| z3_debug_node(item, bindings))
                            .collect(),
                    );
                };
                // SMT-LIB let bindings are simultaneous: every value is built
                // in the incoming environment, then all names scope the body.
                let mut values = Vec::with_capacity(let_bindings.len());
                for binding in let_bindings {
                    let Some(pair) = binding.as_list() else {
                        continue;
                    };
                    let (Some(name), Some(value)) =
                        (pair.first().and_then(SExpr::as_symbol), pair.get(1))
                    else {
                        continue;
                    };
                    values.push((name.to_string(), z3_debug_node(value, bindings)));
                }
                let old_len = bindings.len();
                bindings.extend(
                    values
                        .into_iter()
                        .map(|(name, value)| (name, Z3DebugBinding::Let(value))),
                );
                let result = z3_debug_node(&items[2], bindings);
                bindings.truncate(old_len);
                return result;
            }

            if matches!(head, Some("forall" | "exists" | "lambda")) && items.len() == 3 {
                let Some(sorted_variables) = items[1].as_list() else {
                    return Z3DebugNode::App(
                        head.unwrap_or_default().to_string(),
                        items[1..]
                            .iter()
                            .map(|item| z3_debug_node(item, bindings))
                            .collect(),
                    );
                };
                let mut declarations = Vec::with_capacity(sorted_variables.len());
                for variable in sorted_variables {
                    let Some(pair) = variable.as_list() else {
                        continue;
                    };
                    let (Some(name), Some(sort)) =
                        (pair.first().and_then(SExpr::as_symbol), pair.get(1))
                    else {
                        continue;
                    };
                    declarations.push((name.to_string(), sort.to_raw_string()));
                }
                let old_len = bindings.len();
                bindings.extend(
                    declarations
                        .iter()
                        .cloned()
                        .map(|(name, sort)| (name, Z3DebugBinding::Bound(sort))),
                );
                let body = z3_debug_node(&items[2], bindings);
                bindings.truncate(old_len);
                return Z3DebugNode::Quantifier(
                    head.unwrap_or_default().to_string(),
                    declarations,
                    Box::new(body),
                );
            }

            // An SMT-LIB annotation does not introduce an expression node.
            // Quantifier patterns are metadata children in Z3, but the clean
            // owner witnesses intentionally avoid them; the logical body is
            // still the exact node inspected by the commands implemented here.
            if head == Some("!") && items.len() >= 2 {
                return z3_debug_node(&items[1], bindings);
            }

            // Indexed and qualified identifiers in term position are nullary
            // applications. Their indices/sort are declaration parameters,
            // not expression children.
            if matches!(head, Some("_" | "as")) {
                return Z3DebugNode::Atom(format!("identifier:{}", sexpr.to_raw_string()));
            }

            let application_head = items[0].to_raw_string();
            let arguments = items[1..]
                .iter()
                .map(|item| z3_debug_node(item, bindings))
                .collect();
            Z3DebugNode::App(application_head, arguments)
        }
    }
}

fn z3_debug_is_associative(head: &str) -> bool {
    matches!(
        head,
        "and" | "or" | "xor" | "+" | "*" | "bvand" | "bvor" | "bvxor" | "bvadd" | "bvmul"
    )
}

fn z3_debug_count_nodes(node: &Z3DebugNode, visited: &mut HashSet<Z3DebugNode>) -> usize {
    if !visited.insert(node.clone()) {
        return 0;
    }
    match node {
        Z3DebugNode::Atom(_) | Z3DebugNode::Var(_, _) => 1,
        Z3DebugNode::App(head, arguments) => {
            let associative_expansion = if z3_debug_is_associative(head) {
                arguments.len().saturating_sub(2)
            } else {
                0
            };
            1 + associative_expansion
                + arguments
                    .iter()
                    .map(|argument| z3_debug_count_nodes(argument, visited))
                    .sum::<usize>()
        }
        Z3DebugNode::Quantifier(_, _, body) => 1 + z3_debug_count_nodes(body, visited),
    }
}

fn z3_5_debug_size_output(sexpr: &SExpr) -> String {
    let node = z3_debug_node(sexpr, &mut Vec::new());
    z3_debug_count_nodes(&node, &mut HashSet::new()).to_string()
}

fn z3_debug_collect_used_vars(node: &Z3DebugNode, delta: u32, used: &mut HashMap<u32, String>) {
    match node {
        Z3DebugNode::Var(index, sort) if *index >= delta => {
            used.entry(index - delta).or_insert_with(|| sort.clone());
        }
        Z3DebugNode::App(_, arguments) => {
            for argument in arguments {
                z3_debug_collect_used_vars(argument, delta, used);
            }
        }
        Z3DebugNode::Quantifier(_, declarations, body) => {
            z3_debug_collect_used_vars(body, delta.saturating_add(declarations.len() as u32), used)
        }
        Z3DebugNode::Atom(_) | Z3DebugNode::Var(_, _) => {}
    }
}

fn z3_debug_used_var_map(sexpr: &SExpr) -> HashMap<u32, String> {
    let node = z3_debug_node(sexpr, &mut Vec::new());
    let inspected = match &node {
        Z3DebugNode::Quantifier(_, _, body) => body.as_ref(),
        _ => &node,
    };
    let mut used = HashMap::new();
    z3_debug_collect_used_vars(inspected, 0, &mut used);
    used
}

fn z3_5_debug_used_vars_output(sexpr: &SExpr) -> String {
    let used = z3_debug_used_var_map(sexpr);
    let Some(max_index) = used.keys().copied().max() else {
        return "(vars)".to_string();
    };
    let mut output = String::from("(vars");
    for index in 0..=max_index {
        let sort = used.get(&index).map(String::as_str).unwrap_or("<not-used>");
        output.push_str(&format!("\n  ({index:<6} {sort})"));
    }
    output.push(')');
    output
}

fn z3_debug_quantifier_parts(sexpr: &SExpr) -> Option<(&str, &[SExpr], &SExpr)> {
    let items = sexpr.as_list()?;
    if items.len() != 3 {
        return None;
    }
    let kind = items[0].as_symbol()?;
    if !matches!(kind, "forall" | "exists" | "lambda") {
        return None;
    }
    Some((kind, items[1].as_list()?, &items[2]))
}

fn z3_5_debug_elim_unused_vars_output(sexpr: &SExpr) -> String {
    let Some((kind, declarations, body)) = z3_debug_quantifier_parts(sexpr) else {
        return sexpr.to_raw_string();
    };
    let used = z3_debug_used_var_map(sexpr);
    let declaration_count = declarations.len();
    let retained = declarations
        .iter()
        .enumerate()
        .filter(|(position, _)| {
            let index = declaration_count - 1 - position;
            used.contains_key(&(index as u32))
        })
        .map(|(_, declaration)| declaration.clone())
        .collect::<Vec<_>>();
    if retained.is_empty() {
        return body.to_raw_string();
    }
    SExpr::List(vec![
        SExpr::Symbol(kind.to_string()),
        SExpr::List(retained),
        body.clone(),
    ])
    .to_raw_string()
}

fn z3_debug_substitute_symbols(sexpr: &SExpr, substitutions: &HashMap<String, SExpr>) -> SExpr {
    match sexpr {
        SExpr::Symbol(symbol) => substitutions
            .get(symbol)
            .cloned()
            .unwrap_or_else(|| sexpr.clone()),
        SExpr::List(items) if items.is_empty() => sexpr.clone(),
        SExpr::List(items) => {
            let head = items[0].as_symbol();
            if matches!(head, Some("forall" | "exists" | "lambda")) && items.len() == 3 {
                let mut nested = substitutions.clone();
                if let Some(declarations) = items[1].as_list() {
                    for declaration in declarations {
                        if let Some(name) = declaration
                            .as_list()
                            .and_then(|pair| pair.first())
                            .and_then(SExpr::as_symbol)
                        {
                            nested.remove(name);
                        }
                    }
                }
                return SExpr::List(vec![
                    items[0].clone(),
                    items[1].clone(),
                    z3_debug_substitute_symbols(&items[2], &nested),
                ]);
            }
            if head == Some("let") && items.len() == 3 {
                let rewritten_bindings = items[1].as_list().map(|bindings| {
                    bindings
                        .iter()
                        .map(|binding| {
                            let Some(pair) = binding.as_list() else {
                                return binding.clone();
                            };
                            if pair.len() != 2 {
                                return binding.clone();
                            }
                            SExpr::List(vec![
                                pair[0].clone(),
                                z3_debug_substitute_symbols(&pair[1], substitutions),
                            ])
                        })
                        .collect::<Vec<_>>()
                });
                let mut nested = substitutions.clone();
                if let Some(bindings) = items[1].as_list() {
                    for binding in bindings {
                        if let Some(name) = binding
                            .as_list()
                            .and_then(|pair| pair.first())
                            .and_then(SExpr::as_symbol)
                        {
                            nested.remove(name);
                        }
                    }
                }
                return SExpr::List(vec![
                    items[0].clone(),
                    SExpr::List(rewritten_bindings.unwrap_or_default()),
                    z3_debug_substitute_symbols(&items[2], &nested),
                ]);
            }

            let mut rewritten = Vec::with_capacity(items.len());
            rewritten.push(items[0].clone());
            rewritten.extend(
                items[1..]
                    .iter()
                    .map(|item| z3_debug_substitute_symbols(item, substitutions)),
            );
            SExpr::List(rewritten)
        }
        _ => sexpr.clone(),
    }
}

fn z3_5_debug_instantiate(items: &[SExpr]) -> Result<(Term, String), ParseError> {
    if items.len() != 3 {
        return Err(ParseError::new(
            "dbg-instantiate requires a quantifier and one expression list",
        ));
    }
    let Some((_kind, declarations, body)) = z3_debug_quantifier_parts(&items[1]) else {
        return Err(ParseError::new(
            "dbg-instantiate requires a quantified expression",
        ));
    };
    let arguments = items[2]
        .as_list()
        .ok_or_else(|| ParseError::new("dbg-instantiate requires an expression list"))?;
    if declarations.len() != arguments.len() {
        return Err(ParseError::new(
            "dbg-instantiate argument count must match the quantified variables",
        ));
    }
    let mut substitutions = HashMap::new();
    for (declaration, argument) in declarations.iter().zip(arguments) {
        let name = declaration
            .as_list()
            .and_then(|pair| pair.first())
            .and_then(SExpr::as_symbol)
            .ok_or_else(|| ParseError::new("quantified variable must be a sorted symbol"))?;
        substitutions.insert(name.to_string(), argument.clone());
    }
    let instantiated = z3_debug_substitute_symbols(body, &substitutions);
    let term = Term::from_sexp(&instantiated)?;
    Ok((term, instantiated.to_raw_string()))
}

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
    Indexed(String, Vec<Index>),
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
                if items[0].is_symbol("_") {
                    if items.len() < 3 {
                        return Err(ParseError::new(
                            "indexed sort requires a name and at least one index",
                        ));
                    }
                    let name = items[1]
                        .as_symbol()
                        .ok_or_else(|| ParseError::new("Expected symbol in indexed sort"))?;
                    let indices: Result<Vec<_>, _> = items[2..]
                        .iter()
                        .map(|sexp| {
                            Index::from_sexp(sexp).ok_or_else(|| {
                                ParseError::new("Expected an index token in indexed sort")
                            })
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
    /// `(set-option <keyword>)`, the valueless generic `attribute` alternative.
    SetOptionAttribute(String),
    /// `(set-info <keyword> <value>)`
    SetInfo(String, SExpr),
    /// `(set-info <keyword>)`, the valueless generic `attribute` alternative.
    SetInfoAttribute(String),
    /// `(declare-sort <symbol> <numeral>)`
    DeclareSort(String, u32),
    /// `(declare-sort-parameter <symbol>)` (SMT-LIB 2.7)
    DeclareSortParameter(String),
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
    /// `(labels)` - retrieve the labels attached to the last satisfiable or
    /// unknown result.
    Labels,
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
    /// `(display <term>)` - Z3 extension that prints an elaborated term.
    Display(Term, String),
    /// `(dbg-set <symbol> <term>)` - store a validated AST in Z3's debug-global map.
    DebugSet(String, Term, String),
    /// `(dbg-pp-var <symbol>)` - print an AST from Z3's debug-global map.
    DebugPpVar(String),
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

fn no_argument_command(
    items: &[SExpr],
    name: &str,
    command: Command,
) -> Result<Command, ParseError> {
    if items.len() != 1 {
        return Err(ParseError::new(format!("{name} takes no arguments")));
    }
    Ok(command)
}

fn parse_optional_u32(items: &[SExpr], name: &str, default: u32) -> Result<u32, ParseError> {
    if items.len() > 2 {
        return Err(ParseError::new(format!(
            "{name} accepts at most one numeral"
        )));
    }
    let Some(value) = items.get(1) else {
        return Ok(default);
    };
    let value = value
        .as_numeral()
        .ok_or_else(|| ParseError::new(format!("{name} requires a numeral")))?;
    value
        .parse::<u32>()
        .map_err(|_| ParseError::new(format!("{name} numeral is out of range")))
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
                if items.len() != 2 {
                    return Err(ParseError::new("set-logic requires exactly one logic name"));
                }
                let logic = items
                    .get(1)
                    .and_then(|s| s.as_symbol())
                    .ok_or_else(|| ParseError::new("set-logic requires logic name"))?;
                Ok(Self::SetLogic(logic.to_string()))
            }
            "set-option" => {
                if !(2..=3).contains(&items.len()) {
                    return Err(ParseError::new(
                        "set-option requires one keyword and at most one value",
                    ));
                }
                let keyword = match &items[1] {
                    SExpr::Keyword(k) => k.clone(),
                    _ => return Err(ParseError::new("set-option requires keyword")),
                };
                if let Some(value) = items.get(2) {
                    if matches!(value, SExpr::Keyword(_)) {
                        return Err(ParseError::new(
                            "set-option value must be an SMT-LIB attribute_value, not a keyword",
                        ));
                    }
                    Ok(Self::SetOption(keyword, value.clone()))
                } else {
                    Ok(Self::SetOptionAttribute(keyword))
                }
            }
            "set-info" => {
                if !(2..=3).contains(&items.len()) {
                    return Err(ParseError::new(
                        "set-info requires one keyword and at most one value",
                    ));
                }
                let keyword = match &items[1] {
                    SExpr::Keyword(k) => k.clone(),
                    _ => return Err(ParseError::new("set-info requires keyword")),
                };
                if let Some(value) = items.get(2) {
                    if matches!(value, SExpr::Keyword(_)) {
                        return Err(ParseError::new(
                            "set-info value must be an SMT-LIB attribute_value, not a keyword",
                        ));
                    }
                    Ok(Self::SetInfo(keyword, value.clone()))
                } else {
                    Ok(Self::SetInfoAttribute(keyword))
                }
            }
            "declare-sort" => {
                if !(2..=3).contains(&items.len()) {
                    return Err(ParseError::new(
                        "declare-sort requires a name and optional arity",
                    ));
                }
                let name = items
                    .get(1)
                    .and_then(|s| s.as_symbol())
                    .ok_or_else(|| ParseError::new("declare-sort requires name"))?;
                let arity = match items.get(2) {
                    Some(arity) => arity
                        .as_numeral()
                        .ok_or_else(|| ParseError::new("declare-sort arity must be a numeral"))?
                        .parse::<u32>()
                        .map_err(|_| ParseError::new("declare-sort arity is out of range"))?,
                    None => 0,
                };
                Ok(Self::DeclareSort(name.to_string(), arity))
            }
            "declare-sort-parameter" => {
                if items.len() != 2 {
                    return Err(ParseError::new(
                        "declare-sort-parameter requires exactly one symbol",
                    ));
                }
                let name = items[1]
                    .as_symbol()
                    .ok_or_else(|| ParseError::new("declare-sort-parameter requires a symbol"))?;
                Ok(Self::DeclareSortParameter(name.to_string()))
            }
            "define-sort" => {
                if items.len() != 4 {
                    return Err(ParseError::new(
                        "define-sort requires exactly a name, parameter list, and sort",
                    ));
                }
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
                if items.len() != 3 {
                    return Err(ParseError::new(
                        "declare-datatype requires exactly a name and datatype declaration",
                    ));
                }
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
                if items.len() != 3 {
                    return Err(ParseError::new(
                        "declare-datatypes requires exactly sort and datatype declaration lists",
                    ));
                }
                // (declare-datatypes ((name1 arity1) ...) (datatype_dec1 ...))
                let sort_decs = items.get(1).and_then(|s| s.as_list()).ok_or_else(|| {
                    ParseError::new("declare-datatypes requires sort declarations")
                })?;
                let datatype_decs = items.get(2).and_then(|s| s.as_list()).ok_or_else(|| {
                    ParseError::new("declare-datatypes requires datatype declarations")
                })?;

                if datatype_decs.is_empty() {
                    return Err(ParseError::new(
                        "declare-datatypes requires at least one sort and datatype declaration",
                    ));
                }

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
                if items.len() != 4 {
                    return Err(ParseError::new(
                        "declare-fun requires exactly a name, argument-sort list, and return sort",
                    ));
                }
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
                if items.len() != 3 {
                    return Err(ParseError::new(
                        "declare-const requires exactly a name and sort",
                    ));
                }
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
                if items.len() != 2 {
                    return Err(ParseError::new("assert requires exactly one term"));
                }
                let term = items
                    .get(1)
                    .ok_or_else(|| ParseError::new("assert requires term"))?;
                Ok(Self::Assert(Term::from_sexp(term)?))
            }
            // Z3 5.0.0's debug command constructs `(not term)` and passes it
            // directly to the ordinary assertion path. Desugar at the parser
            // boundary so every assertion invariant (Bool sort checking,
            // stack scoping, proof tracking, and query invalidation) stays in
            // the single established implementation.
            "assert-not" => {
                if items.len() != 2 {
                    return Err(ParseError::new("assert-not requires exactly one term"));
                }
                let term = items
                    .get(1)
                    .ok_or_else(|| ParseError::new("assert-not requires term"))?;
                Ok(Self::Assert(Term::App(
                    "not".to_string(),
                    vec![Term::from_sexp(term)?],
                )))
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
            "check-sat" => {
                if items.len() == 1 {
                    return Ok(Self::CheckSat);
                }
                // Exact Z3 5.0.0 overlay: trailing Boolean terms are temporary
                // assumptions, with the same semantics as the parenthesized
                // list accepted by `check-sat-assuming`.
                let terms = items[1..]
                    .iter()
                    .map(Term::from_sexp)
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Self::CheckSatAssuming(terms))
            }
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
                if items.len() != 2 {
                    return Err(ParseError::new(
                        "check-sat-assuming requires exactly one literal list",
                    ));
                }
                let lits = items
                    .get(1)
                    .and_then(|s| s.as_list())
                    .ok_or_else(|| ParseError::new("check-sat-assuming requires literal list"))?;
                let terms: Result<Vec<_>, _> = lits.iter().map(Term::from_sexp).collect();
                Ok(Self::CheckSatAssuming(terms?))
            }
            "get-model" => {
                // Z3 5.0.0 registers this command with variable arity. Every
                // argument must be a 32-bit unsigned model index; successive
                // arguments overwrite the preceding index. AY has no boxed
                // optimization-model selection here, so validate all indices
                // and otherwise retain the ordinary `GetModel` operation.
                for index in &items[1..] {
                    index
                        .as_numeral()
                        .ok_or_else(|| {
                            ParseError::new("get-model requires unsigned integer indices")
                        })?
                        .parse::<u32>()
                        .map_err(|_| ParseError::new("get-model index is out of range"))?;
                }
                Ok(Self::GetModel)
            }
            "get-objectives" => no_argument_command(items, "get-objectives", Self::GetObjectives),
            "get-objective-certificates" => Ok(Self::GetObjectiveCertificates),
            "get-value" => {
                if items.len() != 2 {
                    return Err(ParseError::new(
                        "get-value requires exactly one non-empty term list",
                    ));
                }
                let terms = items
                    .get(1)
                    .and_then(|s| s.as_list())
                    .ok_or_else(|| ParseError::new("get-value requires term list"))?;
                if terms.is_empty() {
                    return Err(ParseError::new("get-value requires a non-empty term list"));
                }
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
                if items.len() > 2 {
                    return Err(ParseError::new(
                        "get-unsat-core accepts no arguments or exactly :farkas",
                    ));
                }
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
            "get-unsat-assumptions" => {
                no_argument_command(items, "get-unsat-assumptions", Self::GetUnsatAssumptions)
            }
            "get-proof" => no_argument_command(items, "get-proof", Self::GetProof),
            "get-assertions" => no_argument_command(items, "get-assertions", Self::GetAssertions),
            "get-assignment" => no_argument_command(items, "get-assignment", Self::GetAssignment),
            "get-info" => {
                if items.len() != 2 {
                    return Err(ParseError::new("get-info requires exactly one info flag"));
                }
                let keyword = match items.get(1) {
                    Some(SExpr::Keyword(k)) => k.clone(),
                    _ => return Err(ParseError::new("get-info requires keyword")),
                };
                Ok(Self::GetInfo(keyword))
            }
            "get-option" => {
                if items.len() != 2 {
                    return Err(ParseError::new("get-option requires exactly one keyword"));
                }
                let keyword = match items.get(1) {
                    Some(SExpr::Keyword(k)) => k.clone(),
                    _ => return Err(ParseError::new("get-option requires keyword")),
                };
                Ok(Self::GetOption(keyword))
            }
            "labels" => no_argument_command(items, "labels", Self::Labels),
            "push" => {
                let n = parse_optional_u32(items, "push", 1)?;
                Ok(Self::Push(n))
            }
            "pop" => {
                let n = parse_optional_u32(items, "pop", 1)?;
                Ok(Self::Pop(n))
            }
            "reset" => no_argument_command(items, "reset", Self::Reset),
            "reset-assertions" => {
                no_argument_command(items, "reset-assertions", Self::ResetAssertions)
            }
            "exit" => no_argument_command(items, "exit", Self::Exit),
            "help" => Self::parse_help(items),
            // Z3 5.0.0 renders a deterministic build-time simplifier registry.
            // Model it as a fixed-output query through the existing `Echo`
            // result path: that path emits the payload without an additional
            // `:print-success` acknowledgement, exactly like Z3's command.
            "help-simplifier" => {
                if items.len() != 1 {
                    return Err(ParseError::new("invalid command, too many arguments"));
                }
                Ok(Self::Echo(z3_5_help_simplifier_output().to_string()))
            }
            "help-tactic" => {
                if items.len() != 1 {
                    return Err(ParseError::new("invalid command, too many arguments"));
                }
                Ok(Self::Echo(z3_5_help_tactic_output().to_string()))
            }
            "dbg-params" => {
                no_argument_command(items, "dbg-params", Self::Echo("worked".to_string()))
            }
            "dbg-sexpr" => {
                if items.len() != 2 {
                    return Err(ParseError::new(
                        "dbg-sexpr requires exactly one s-expression",
                    ));
                }
                Ok(Self::Echo(z3_5_debug_sexpr_output(&items[1])))
            }
            "dbg-translator" => {
                if items.len() != 2 {
                    return Err(ParseError::new("dbg-translator requires exactly one term"));
                }
                let source = items[1].to_string();
                Ok(Self::Display(
                    Term::from_sexp(&items[1])?,
                    format!("{source}\n--->\n{source}"),
                ))
            }
            "dbg-size" => {
                if items.len() != 2 {
                    return Err(ParseError::new("dbg-size requires exactly one term"));
                }
                let term = Term::from_sexp(&items[1])?;
                let output = stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || {
                    z3_5_debug_size_output(&items[1])
                });
                Ok(Self::Display(term, output))
            }
            "dbg-used-vars" => {
                if items.len() != 2 {
                    return Err(ParseError::new(
                        "dbg-used-vars requires exactly one expression",
                    ));
                }
                let term = Term::from_sexp(&items[1])?;
                let output = stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || {
                    z3_5_debug_used_vars_output(&items[1])
                });
                Ok(Self::Display(term, output))
            }
            "dbg-elim-unused-vars" => {
                if items.len() != 2 {
                    return Err(ParseError::new(
                        "dbg-elim-unused-vars requires exactly one expression",
                    ));
                }
                let term = Term::from_sexp(&items[1])?;
                let output = stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || {
                    z3_5_debug_elim_unused_vars_output(&items[1])
                });
                Ok(Self::Display(term, output))
            }
            "dbg-instantiate" => {
                let (term, output) =
                    stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || {
                        z3_5_debug_instantiate(items)
                    })?;
                Ok(Self::Display(term, output))
            }
            "dbg-set" => {
                if items.len() != 3 {
                    return Err(ParseError::new(
                        "dbg-set requires exactly one symbol and one term",
                    ));
                }
                let name = items[1]
                    .as_symbol()
                    .ok_or_else(|| ParseError::new("dbg-set requires a symbol"))?;
                Ok(Self::DebugSet(
                    name.to_string(),
                    Term::from_sexp(&items[2])?,
                    items[2].to_raw_string(),
                ))
            }
            "dbg-pp-var" => {
                if items.len() != 2 {
                    return Err(ParseError::new("dbg-pp-var requires exactly one symbol"));
                }
                let name = items[1]
                    .as_symbol()
                    .ok_or_else(|| ParseError::new("dbg-pp-var requires a symbol"))?;
                Ok(Self::DebugPpVar(name.to_string()))
            }
            "echo" => {
                if items.len() != 2 {
                    return Err(ParseError::new("echo requires exactly one string"));
                }
                let msg = match items.get(1) {
                    Some(SExpr::String(s)) => s.clone(),
                    _ => return Err(ParseError::new("echo requires string")),
                };
                Ok(Self::Echo(msg))
            }
            "display" => {
                if items.len() != 2 {
                    return Err(ParseError::new("display requires exactly one term"));
                }
                Ok(Self::Display(
                    Term::from_sexp(&items[1])?,
                    items[1].to_string(),
                ))
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

    /// Parse Z3 5.0.0's `(help <symbol>*)` registry query.
    ///
    /// With no names Z3 prints the complete sorted registry snapshot. With
    /// names it prints those complete blocks in request order, retaining
    /// duplicates. An unknown or non-symbol argument rejects the whole command
    /// before any output is emitted.
    fn parse_help(items: &[SExpr]) -> Result<Self, ParseError> {
        if items.len() == 1 {
            return Ok(Self::Echo(z3_5_help_output().to_string()));
        }

        let mut output = String::from("\"");
        for item in &items[1..] {
            // `true` and `false` have dedicated SExpr variants in AY's generic
            // parser, but Z3's command-argument parser accepts them in a
            // CPK_SYMBOL slot and then performs the ordinary registry lookup.
            let name = match item {
                SExpr::Symbol(name) => name.as_str(),
                SExpr::True => "true",
                SExpr::False => "false",
                _ => {
                    return Err(ParseError::new("invalid command argument, symbol expected"));
                }
            };
            let entry = z3_5_help_entry(name)
                .ok_or_else(|| ParseError::new(format!("unknown command '{name}'")))?;
            output.push_str(entry);
        }
        output.push('\"');
        Ok(Self::Echo(output))
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
        if items.len() != 5 {
            return Err(ParseError::new(
                "define-fun requires exactly a name, parameter list, return sort, and body",
            ));
        }
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
        if items.len() != 4 {
            return Err(ParseError::new(
                "define-const requires exactly a name, sort, and value",
            ));
        }
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
        if items.len() != 5 {
            return Err(ParseError::new(
                "define-fun-rec requires exactly a name, parameter list, return sort, and body",
            ));
        }
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
        if items.len() != 3 {
            return Err(ParseError::new(
                "define-funs-rec requires exactly declaration and body lists",
            ));
        }
        let func_decs = items
            .get(1)
            .and_then(|s| s.as_list())
            .ok_or_else(|| ParseError::new("define-funs-rec requires function declarations"))?;
        let bodies = items
            .get(2)
            .and_then(|s| s.as_list())
            .ok_or_else(|| ParseError::new("define-funs-rec requires function bodies"))?;

        if func_decs.is_empty() {
            return Err(ParseError::new(
                "define-funs-rec requires at least one function declaration and body",
            ));
        }

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
