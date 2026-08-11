// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `ay simplify` subcommand — SMT-LIB2 AST simplification.

use std::collections::{HashMap, HashSet};
use std::fs;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use ay_frontend::command::{Constant, Term};
use ay_frontend::{parse, Command};
use clap::{Args, ValueEnum};
use num_bigint::BigInt;

use crate::cmd_simplify_printer::command_to_smtlib;

/// Arguments for `ay simplify`.
///
/// Phase 1 (#8696) scope: `ay simplify FILE` parses SMT-LIB2, applies an
/// AST-level tactic, and emits the simplified script to stdout. The default
/// `simplify` tactic matches the task brief; additional tactics are accepted
/// as power-user options but remain AST-only rewrites (no solver integration
/// yet — that is a later `ctx-solver-simplify` phase).
///
/// Phase 2 (#8696) adds `--assumptions FILE`: an additional SMT-LIB2 file
/// whose assertions are treated as a read-only assumption context during
/// simplification. `propagate-values` substitutes symbol=numeral facts from
/// the assumptions into the main assertions, and `ctx-simplify` uses
/// assumption bounds to drop implied assertions. Assumptions themselves are
/// NEVER emitted — they are input-side context only.
#[derive(Args, Clone)]
pub(crate) struct SimplifyArgs {
    /// Input SMT-LIB2 file. Use `-` (default) for stdin.
    #[arg(value_name = "FILE", default_value = "-", allow_hyphen_values = true)]
    pub(crate) file: PathBuf,

    /// Simplification tactic.
    ///
    /// Phase 1 supports only AST-level rewrites. `ctx-solver-simplify` and
    /// quantifier elimination will land in later phases.
    #[arg(long, value_enum, default_value_t = SimplifyTactic::Simplify)]
    pub(crate) tactic: SimplifyTactic,

    /// Read input from stdin. Equivalent to passing `-` as the file.
    #[arg(long)]
    pub(crate) stdin: bool,

    /// Emit `(check-sat)` after the simplified assertions.
    ///
    /// Any `(check-sat)` commands in the input are stripped before rewriting;
    /// set this flag to append a single `(check-sat)` to the output so the
    /// result can be piped directly into another solver.
    #[arg(long)]
    pub(crate) check_sat: bool,

    /// Additional SMT-LIB2 file containing assertions to use as a read-only
    /// assumption context.
    ///
    /// Assumptions are parsed as a sequence of `(assert ...)` commands. Their
    /// assertions are used by `propagate-values` (symbol=numeral substitution)
    /// and `ctx-simplify` (bound-based implication detection) but are NEVER
    /// emitted to the simplified output. Non-assert commands in the
    /// assumptions file (declarations, logic settings, ...) are silently
    /// ignored — the main input file is the source of truth for declarations.
    #[arg(long, value_name = "FILE", help_heading = "Context")]
    pub(crate) assumptions: Option<PathBuf>,
}

/// Available AST-level simplification tactics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
#[clap(rename_all = "kebab-case")]
pub(crate) enum SimplifyTactic {
    Simplify,
    CtxSimplify,
    PropagateValues,
    ElimUnconstrained,
}

impl SimplifyTactic {
    fn as_str(self) -> &'static str {
        match self {
            Self::Simplify => "simplify",
            Self::CtxSimplify => "ctx-simplify",
            Self::PropagateValues => "propagate-values",
            Self::ElimUnconstrained => "elim-unconstrained",
        }
    }
}

#[derive(Default)]
struct TacticOutcome {
    assertions: Vec<Term>,
    removed_assertions: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BoundDirection {
    Lower,
    Upper,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Bound {
    symbol: String,
    value: BigInt,
    direction: BoundDirection,
    strict: bool,
}

/// Entry point for `ay simplify`.
pub(crate) fn run(args: &SimplifyArgs) -> Result<()> {
    run_simplify(args)
}

fn run_simplify(args: &SimplifyArgs) -> Result<()> {
    let input = read_input(args)?;
    let commands = parse(&input).map_err(|err| anyhow::anyhow!("{err}"))?;

    let mut declarations = Vec::new();
    let mut assertions = Vec::new();
    let mut others = Vec::new();

    for command in commands {
        match command {
            Command::Assert(term) => assertions.push(term),
            // `(check-sat)` is stripped unconditionally; the `--check-sat`
            // flag controls whether a single `(check-sat)` is re-emitted at
            // the end. Other trailing control commands (`(get-model)`,
            // `(exit)`, ...) are dropped as well — a `simplify` run is a
            // pure text transformation, not a solve.
            Command::CheckSat
            | Command::CheckSatAssuming(_)
            | Command::GetModel
            | Command::GetValue(_)
            | Command::GetUnsatCore
            | Command::GetUnsatAssumptions
            | Command::GetProof
            | Command::GetObjectives
            | Command::GetObjectiveCertificates
            | Command::GetAssertions
            | Command::GetAssignment
            | Command::Exit => {}
            other if is_declaration_command(&other) => declarations.push(other),
            other => others.push(other),
        }
    }

    let assumption_terms = read_assumptions(args.assumptions.as_deref())?;
    let outcome = apply_tactic(assertions, args.tactic, &assumption_terms);

    let stdout = io::stdout();
    let mut out = stdout.lock();
    writeln!(
        out,
        "; simplified by ay simplify (tactic: {})",
        args.tactic.as_str()
    )?;
    if !assumption_terms.is_empty() {
        writeln!(
            out,
            "; assumption context: {} assertion(s) from --assumptions",
            assumption_terms.len()
        )?;
    }
    if matches!(args.tactic, SimplifyTactic::CtxSimplify) {
        writeln!(
            out,
            "; ctx-simplify removed {} implied assertion(s)",
            outcome.removed_assertions
        )?;
    }

    for command in &declarations {
        writeln!(out, "{}", command_to_smtlib(command))?;
    }
    for assertion in &outcome.assertions {
        writeln!(
            out,
            "{}",
            command_to_smtlib(&Command::Assert(assertion.clone()))
        )?;
    }
    for command in &others {
        writeln!(out, "{}", command_to_smtlib(command))?;
    }

    if args.check_sat {
        writeln!(out, "{}", command_to_smtlib(&Command::CheckSat))?;
    }

    Ok(())
}

fn read_input(args: &SimplifyArgs) -> Result<String> {
    if args.stdin || args.file.as_path() == Path::new("-") {
        let mut input = String::new();
        io::stdin()
            .read_to_string(&mut input)
            .context("failed to read SMT-LIB2 input from stdin")?;
        return Ok(input);
    }

    fs::read_to_string(&args.file).with_context(|| {
        format!(
            "failed to read SMT-LIB2 input from '{}'",
            args.file.display()
        )
    })
}

/// Parse the assumptions file (if any) into a list of assertion terms.
///
/// Non-assert commands (declarations, set-logic, ...) are silently dropped —
/// callers are expected to keep declarations in the main input file. A
/// missing path (`args.assumptions == None`) returns the empty vector.
fn read_assumptions(path: Option<&Path>) -> Result<Vec<Term>> {
    let Some(path) = path else {
        return Ok(Vec::new());
    };

    let source = fs::read_to_string(path).with_context(|| {
        format!(
            "failed to read SMT-LIB2 assumptions from '{}'",
            path.display()
        )
    })?;
    let commands = parse(&source).map_err(|err| anyhow::anyhow!("{err}"))?;

    let mut assumptions = Vec::new();
    for command in commands {
        if let Command::Assert(term) = command {
            assumptions.push(term);
        }
    }
    Ok(assumptions)
}

fn apply_tactic(
    assertions: Vec<Term>,
    tactic: SimplifyTactic,
    assumptions: &[Term],
) -> TacticOutcome {
    match tactic {
        SimplifyTactic::Simplify => TacticOutcome {
            assertions: assertions.iter().map(simplify_term).collect(),
            removed_assertions: 0,
        },
        SimplifyTactic::CtxSimplify => apply_ctx_simplify(assertions, assumptions),
        SimplifyTactic::PropagateValues => TacticOutcome {
            assertions: apply_propagate_values(assertions, assumptions),
            removed_assertions: 0,
        },
        SimplifyTactic::ElimUnconstrained => apply_elim_unconstrained(assertions),
    }
}

/// `ctx-simplify` removes assertions that are implied by another assertion
/// or by an assumption from `--assumptions`. Implication is currently limited
/// to symbol-vs-numeral bound reasoning (`(> x 5)` implies `(> x 3)`, etc.);
/// correctness follows from the fact that we only ever DROP assertions whose
/// content is provably a consequence of a retained assertion or assumption.
fn apply_ctx_simplify(assertions: Vec<Term>, assumptions: &[Term]) -> TacticOutcome {
    let simplified: Vec<Term> = assertions.iter().map(simplify_term).collect();
    let bounds: Vec<Option<Bound>> = simplified.iter().map(extract_bound).collect();
    let assumption_bounds: Vec<Bound> = assumptions
        .iter()
        .map(simplify_term)
        .filter_map(|term| extract_bound(&term))
        .collect();

    let mut keep = vec![true; simplified.len()];
    let mut removed = 0usize;

    for (idx, bound) in bounds.iter().enumerate() {
        let Some(bound) = bound else {
            continue;
        };

        // Implied by a peer assertion (different index, still-kept, stronger).
        let implied_by_peer = bounds.iter().enumerate().any(|(other_idx, other_bound)| {
            idx != other_idx
                && other_bound
                    .as_ref()
                    .is_some_and(|other| bound_implies(other, bound))
        });
        // Implied by an assumption from --assumptions.
        let implied_by_assumption = assumption_bounds
            .iter()
            .any(|other| bound_implies(other, bound));

        if implied_by_peer || implied_by_assumption {
            keep[idx] = false;
            removed += 1;
        }
    }

    let assertions = simplified
        .into_iter()
        .zip(keep)
        .filter_map(|(term, keep_term)| keep_term.then_some(term))
        .collect();

    TacticOutcome {
        assertions,
        removed_assertions: removed,
    }
}

/// `propagate-values` substitutes symbol=numeral equalities in assertions.
///
/// Two substitution sources are combined:
///   1. Assumption-derived facts from `--assumptions`: these apply uniformly
///      to every output assertion without ever being excluded.
///   2. Self-derived facts from the main assertions: these apply to every
///      OTHER assertion. The defining equality itself is preserved verbatim
///      so the output is equisatisfiable with the input (Z3 matches this
///      behaviour).
fn apply_propagate_values(assertions: Vec<Term>, assumptions: &[Term]) -> Vec<Term> {
    let simplified: Vec<Term> = assertions.iter().map(simplify_term).collect();
    let assumption_substitutions =
        collect_numeric_equalities(&assumptions.iter().map(simplify_term).collect::<Vec<_>>());
    let self_substitutions = collect_numeric_equalities(&simplified);

    simplified
        .into_iter()
        .map(|term| {
            let mut local_substitutions = self_substitutions.clone();
            // Assumption facts always apply — they are external context that
            // doesn't conflict with the "don't rewrite your own definition"
            // rule for internal assertions.
            for (symbol, replacement) in &assumption_substitutions {
                local_substitutions
                    .entry(symbol.clone())
                    .or_insert_with(|| replacement.clone());
            }
            if let Some((symbol, _)) = extract_symbol_numeral_equality(&term) {
                local_substitutions.remove(&symbol);
            }
            simplify_term(&substitute_term(
                &term,
                &local_substitutions,
                &HashSet::new(),
            ))
        })
        .collect()
}

fn apply_elim_unconstrained(assertions: Vec<Term>) -> TacticOutcome {
    let simplified: Vec<Term> = assertions.iter().map(simplify_term).collect();
    let symbol_sets: Vec<HashSet<String>> = simplified
        .iter()
        .map(|term| {
            let mut symbols = HashSet::new();
            collect_free_symbols(term, &HashSet::new(), &mut symbols);
            symbols
        })
        .collect();

    let mut counts: HashMap<String, usize> = HashMap::new();
    for symbols in &symbol_sets {
        for symbol in symbols {
            *counts.entry(symbol.clone()).or_default() += 1;
        }
    }

    let mut removed = 0usize;
    let assertions = simplified
        .into_iter()
        .zip(symbol_sets)
        .filter_map(|(term, symbols)| {
            if !symbols.is_empty() && symbols.iter().all(|symbol| counts[symbol] == 1) {
                removed += 1;
                None
            } else {
                Some(term)
            }
        })
        .collect();

    TacticOutcome {
        assertions,
        removed_assertions: removed,
    }
}

fn simplify_term(term: &Term) -> Term {
    match term {
        Term::Const(_) | Term::Symbol(_) => term.clone(),
        Term::App(name, args) => simplify_app(name, args),
        Term::IndexedApp(name, indices, args) => Term::IndexedApp(
            name.clone(),
            indices.clone(),
            args.iter().map(simplify_term).collect(),
        ),
        Term::QualifiedApp(name, sort, args) => Term::QualifiedApp(
            name.clone(),
            sort.clone(),
            args.iter().map(simplify_term).collect(),
        ),
        Term::Let(bindings, body) => Term::Let(
            bindings
                .iter()
                .map(|(name, value)| (name.clone(), simplify_term(value)))
                .collect(),
            Box::new(simplify_term(body)),
        ),
        Term::Forall(bindings, body) => {
            Term::Forall(bindings.clone(), Box::new(simplify_term(body)))
        }
        Term::Exists(bindings, body) => {
            Term::Exists(bindings.clone(), Box::new(simplify_term(body)))
        }
        Term::Lambda(bindings, body) => {
            Term::Lambda(bindings.clone(), Box::new(simplify_term(body)))
        }
        Term::Annotated(inner, annotations) => {
            Term::Annotated(Box::new(simplify_term(inner)), annotations.clone())
        }
        _ => term.clone(),
    }
}

fn simplify_app(name: &str, args: &[Term]) -> Term {
    let simplified_args: Vec<Term> = args.iter().map(simplify_term).collect();

    match name {
        "+" => simplify_add(simplified_args),
        "*" => simplify_mul(simplified_args),
        "-" if simplified_args.len() == 2 && is_zero(&simplified_args[1]) => {
            simplified_args[0].clone()
        }
        "not" if simplified_args.len() == 1 => simplify_not(simplified_args.into_iter().next()),
        "and" => simplify_and(simplified_args),
        "or" => simplify_or(simplified_args),
        "ite" if simplified_args.len() == 3 => simplify_ite(simplified_args),
        "=" => simplify_equality(simplified_args),
        ">" | ">=" | "<" | "<=" => simplify_comparison(name, simplified_args),
        _ => Term::App(name.to_string(), simplified_args),
    }
}

fn simplify_add(args: Vec<Term>) -> Term {
    let mut others = Vec::new();
    let mut sum = BigInt::from(0u8);
    let mut saw_numeral = false;

    for arg in args {
        if let Some(value) = numeral_value(&arg) {
            sum += value;
            saw_numeral = true;
        } else {
            others.push(arg);
        }
    }

    if saw_numeral && (sum != BigInt::from(0u8) || others.is_empty()) {
        others.push(numeral_term(sum));
    }

    collapse_nary("+", others, Term::Const(Constant::Numeral("0".to_string())))
}

fn simplify_mul(args: Vec<Term>) -> Term {
    let mut others = Vec::new();
    let mut product = BigInt::from(1u8);
    let mut saw_numeral = false;

    for arg in args {
        if let Some(value) = numeral_value(&arg) {
            if value == BigInt::from(0u8) {
                return numeral_term(BigInt::from(0u8));
            }
            product *= value;
            saw_numeral = true;
        } else {
            others.push(arg);
        }
    }

    if saw_numeral && (product != BigInt::from(1u8) || others.is_empty()) {
        others.push(numeral_term(product));
    }

    collapse_nary("*", others, Term::Const(Constant::Numeral("1".to_string())))
}

fn simplify_not(arg: Option<Term>) -> Term {
    let arg = arg.expect("not arity checked by caller");

    if is_true(&arg) {
        return Term::Const(Constant::False);
    }
    if is_false(&arg) {
        return Term::Const(Constant::True);
    }
    if let Term::App(name, inner_args) = &arg {
        if name == "not" && inner_args.len() == 1 {
            return inner_args[0].clone();
        }
    }

    Term::App("not".to_string(), vec![arg])
}

fn simplify_and(args: Vec<Term>) -> Term {
    let mut filtered = Vec::new();
    for arg in args {
        if is_false(&arg) {
            return Term::Const(Constant::False);
        }
        if !is_true(&arg) {
            filtered.push(arg);
        }
    }

    collapse_nary("and", filtered, Term::Const(Constant::True))
}

fn simplify_or(args: Vec<Term>) -> Term {
    let mut filtered = Vec::new();
    for arg in args {
        if is_true(&arg) {
            return Term::Const(Constant::True);
        }
        if !is_false(&arg) {
            filtered.push(arg);
        }
    }

    collapse_nary("or", filtered, Term::Const(Constant::False))
}

fn simplify_ite(args: Vec<Term>) -> Term {
    match args.as_slice() {
        [cond, then_term, else_term] if is_true(cond) => then_term.clone(),
        [cond, _then_term, else_term] if is_false(cond) => else_term.clone(),
        _ => Term::App("ite".to_string(), args),
    }
}

fn simplify_equality(args: Vec<Term>) -> Term {
    if args.len() >= 2 && args.windows(2).all(|pair| pair[0] == pair[1]) {
        Term::Const(Constant::True)
    } else {
        Term::App("=".to_string(), args)
    }
}

fn simplify_comparison(name: &str, args: Vec<Term>) -> Term {
    if args.len() == 2 && args[0] == args[1] {
        return match name {
            ">" | "<" => Term::Const(Constant::False),
            ">=" | "<=" => Term::Const(Constant::True),
            _ => Term::App(name.to_string(), args),
        };
    }

    Term::App(name.to_string(), args)
}

fn collapse_nary(name: &str, mut args: Vec<Term>, empty_value: Term) -> Term {
    match args.len() {
        0 => empty_value,
        1 => args.pop().expect("length checked above"),
        _ => Term::App(name.to_string(), args),
    }
}

fn numeral_value(term: &Term) -> Option<BigInt> {
    match term {
        Term::Const(Constant::Numeral(value)) => value.parse::<BigInt>().ok(),
        _ => None,
    }
}

fn numeral_term(value: BigInt) -> Term {
    Term::Const(Constant::Numeral(value.to_string()))
}

fn is_zero(term: &Term) -> bool {
    numeral_value(term).is_some_and(|value| value == BigInt::from(0u8))
}

fn is_true(term: &Term) -> bool {
    matches!(term, Term::Const(Constant::True))
}

fn is_false(term: &Term) -> bool {
    matches!(term, Term::Const(Constant::False))
}

fn strip_annotations(term: &Term) -> &Term {
    match term {
        Term::Annotated(inner, _) => strip_annotations(inner),
        other => other,
    }
}

fn collect_numeric_equalities(assertions: &[Term]) -> HashMap<String, Term> {
    let mut substitutions = HashMap::new();
    for assertion in assertions {
        if let Some((symbol, numeral)) = extract_symbol_numeral_equality(assertion) {
            substitutions.insert(symbol, Term::Const(Constant::Numeral(numeral)));
        }
    }
    substitutions
}

fn extract_symbol_numeral_equality(term: &Term) -> Option<(String, String)> {
    let term = strip_annotations(term);
    let Term::App(name, args) = term else {
        return None;
    };
    if name != "=" || args.len() != 2 {
        return None;
    }

    match (&args[0], &args[1]) {
        (Term::Symbol(symbol), Term::Const(Constant::Numeral(numeral)))
        | (Term::Const(Constant::Numeral(numeral)), Term::Symbol(symbol)) => {
            Some((symbol.clone(), numeral.clone()))
        }
        _ => None,
    }
}

fn substitute_term(
    term: &Term,
    substitutions: &HashMap<String, Term>,
    bound: &HashSet<String>,
) -> Term {
    match term {
        Term::Const(_) => term.clone(),
        Term::Symbol(symbol) => substitutions
            .get(symbol)
            .filter(|_| !bound.contains(symbol))
            .cloned()
            .unwrap_or_else(|| term.clone()),
        Term::App(name, args) => Term::App(
            name.clone(),
            args.iter()
                .map(|arg| substitute_term(arg, substitutions, bound))
                .collect(),
        ),
        Term::IndexedApp(name, indices, args) => Term::IndexedApp(
            name.clone(),
            indices.clone(),
            args.iter()
                .map(|arg| substitute_term(arg, substitutions, bound))
                .collect(),
        ),
        Term::QualifiedApp(name, sort, args) => Term::QualifiedApp(
            name.clone(),
            sort.clone(),
            args.iter()
                .map(|arg| substitute_term(arg, substitutions, bound))
                .collect(),
        ),
        Term::Let(bindings, body) => {
            let rewritten_bindings = bindings
                .iter()
                .map(|(name, value)| (name.clone(), substitute_term(value, substitutions, bound)))
                .collect();

            let mut shadowed = bound.clone();
            for (name, _) in bindings {
                shadowed.insert(name.clone());
            }

            Term::Let(
                rewritten_bindings,
                Box::new(substitute_term(body, substitutions, &shadowed)),
            )
        }
        Term::Forall(bindings, body) => {
            let mut shadowed = bound.clone();
            for (name, _) in bindings {
                shadowed.insert(name.clone());
            }
            Term::Forall(
                bindings.clone(),
                Box::new(substitute_term(body, substitutions, &shadowed)),
            )
        }
        Term::Exists(bindings, body) => {
            let mut shadowed = bound.clone();
            for (name, _) in bindings {
                shadowed.insert(name.clone());
            }
            Term::Exists(
                bindings.clone(),
                Box::new(substitute_term(body, substitutions, &shadowed)),
            )
        }
        Term::Lambda(bindings, body) => {
            let mut shadowed = bound.clone();
            for (name, _) in bindings {
                shadowed.insert(name.clone());
            }
            Term::Lambda(
                bindings.clone(),
                Box::new(substitute_term(body, substitutions, &shadowed)),
            )
        }
        Term::Annotated(inner, annotations) => Term::Annotated(
            Box::new(substitute_term(inner, substitutions, bound)),
            annotations.clone(),
        ),
        _ => term.clone(),
    }
}

fn collect_free_symbols(term: &Term, bound: &HashSet<String>, symbols: &mut HashSet<String>) {
    match term {
        Term::Const(_) => {}
        Term::Symbol(symbol) if !bound.contains(symbol) => {
            symbols.insert(symbol.clone());
        }
        Term::App(_, args) | Term::IndexedApp(_, _, args) | Term::QualifiedApp(_, _, args) => {
            for arg in args {
                collect_free_symbols(arg, bound, symbols);
            }
        }
        Term::Let(bindings, body) => {
            for (_, value) in bindings {
                collect_free_symbols(value, bound, symbols);
            }

            let mut shadowed = bound.clone();
            for (name, _) in bindings {
                shadowed.insert(name.clone());
            }
            collect_free_symbols(body, &shadowed, symbols);
        }
        Term::Forall(bindings, body)
        | Term::Exists(bindings, body)
        | Term::Lambda(bindings, body) => {
            let mut shadowed = bound.clone();
            for (name, _) in bindings {
                shadowed.insert(name.clone());
            }
            collect_free_symbols(body, &shadowed, symbols);
        }
        Term::Annotated(inner, _) => collect_free_symbols(inner, bound, symbols),
        _ => {}
    }
}

fn extract_bound(term: &Term) -> Option<Bound> {
    let term = strip_annotations(term);
    let Term::App(name, args) = term else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }

    match (&args[0], &args[1]) {
        (Term::Symbol(symbol), rhs) => normalize_bound(name, symbol.clone(), numeral_value(rhs)?),
        (lhs, Term::Symbol(symbol)) => {
            let reversed = reverse_comparison(name)?;
            normalize_bound(reversed, symbol.clone(), numeral_value(lhs)?)
        }
        _ => None,
    }
}

fn normalize_bound(op: &str, symbol: String, value: BigInt) -> Option<Bound> {
    let (direction, strict) = match op {
        ">" => (BoundDirection::Lower, true),
        ">=" => (BoundDirection::Lower, false),
        "<" => (BoundDirection::Upper, true),
        "<=" => (BoundDirection::Upper, false),
        _ => return None,
    };

    Some(Bound {
        symbol,
        value,
        direction,
        strict,
    })
}

fn reverse_comparison(op: &str) -> Option<&'static str> {
    match op {
        ">" => Some("<"),
        ">=" => Some("<="),
        "<" => Some(">"),
        "<=" => Some(">="),
        _ => None,
    }
}

fn bound_implies(stronger: &Bound, weaker: &Bound) -> bool {
    if stronger.symbol != weaker.symbol || stronger.direction != weaker.direction {
        return false;
    }

    match stronger.direction {
        BoundDirection::Lower => {
            stronger.value > weaker.value
                || (stronger.value == weaker.value && (stronger.strict || !weaker.strict))
        }
        BoundDirection::Upper => {
            stronger.value < weaker.value
                || (stronger.value == weaker.value && (stronger.strict || !weaker.strict))
        }
    }
}

fn is_declaration_command(command: &Command) -> bool {
    matches!(
        command,
        Command::SetLogic(_)
            | Command::SetOption(_, _)
            | Command::SetOptionAttribute(_)
            | Command::SetInfo(_, _)
            | Command::SetInfoAttribute(_)
            | Command::DeclareSort(_, _)
            | Command::DeclareSortParameter(_)
            | Command::DefineSort(_, _, _)
            | Command::DeclareDatatype(_, _)
            | Command::DeclareDatatypes(_, _)
            | Command::DeclareFun(_, _, _)
            | Command::DeclareConst(_, _)
            | Command::DefineFun(_, _, _, _)
            | Command::DefineFunRec(_, _, _, _)
            | Command::DefineFunsRec(_, _)
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_frontend::sexp::parse_sexp;

    fn parse_term(input: &str) -> Term {
        Term::from_sexp(&parse_sexp(input).expect("valid term")).expect("valid AST term")
    }

    #[test]
    fn simplify_constant_folding_and_boolean_rules() {
        let term = parse_term("(and true (> (+ 2 3) (* 1 5)))");
        let simplified = simplify_term(&term);
        assert_eq!(
            command_to_smtlib(&Command::Assert(simplified)),
            "(assert false)"
        );
    }

    #[test]
    fn ctx_simplify_removes_weaker_lower_bound() {
        let assertions = vec![parse_term("(> x 5)"), parse_term("(> x 3)")];
        let outcome = apply_ctx_simplify(assertions, &[]);
        assert_eq!(outcome.removed_assertions, 1);
        assert_eq!(outcome.assertions, vec![parse_term("(> x 5)")]);
    }

    #[test]
    fn ctx_simplify_with_assumptions_drops_implied_assertion() {
        // Assumption `(> x 10)` strictly implies `(> x 3)` — ctx-simplify
        // should drop the assertion and leave nothing to output.
        let assertions = vec![parse_term("(> x 3)")];
        let assumptions = vec![parse_term("(> x 10)")];
        let outcome = apply_ctx_simplify(assertions, &assumptions);
        assert_eq!(outcome.removed_assertions, 1);
        assert!(outcome.assertions.is_empty());
    }

    #[test]
    fn propagate_values_substitutes_symbol_numeral_equalities() {
        let assertions = vec![parse_term("(= x 5)"), parse_term("(> x 3)")];
        let simplified = apply_propagate_values(assertions, &[]);
        assert_eq!(simplified[0], parse_term("(= x 5)"));
        assert_eq!(simplified[1], parse_term("(> 5 3)"));
    }

    #[test]
    fn propagate_values_substitutes_assumption_equalities() {
        // With `(= x 5)` in assumptions, every occurrence of `x` in the main
        // assertions is substituted. The assumption itself is NOT emitted.
        let assertions = vec![parse_term("(> x 3)"), parse_term("(< x 10)")];
        let assumptions = vec![parse_term("(= x 5)")];
        let simplified = apply_propagate_values(assertions, &assumptions);
        assert_eq!(simplified.len(), 2);
        assert_eq!(simplified[0], parse_term("(> 5 3)"));
        assert_eq!(simplified[1], parse_term("(< 5 10)"));
    }

    #[test]
    fn elim_unconstrained_drops_isolated_assertions() {
        let assertions = vec![
            parse_term("(> x 0)"),
            parse_term("(> y 1)"),
            parse_term("(> x 2)"),
        ];
        let outcome = apply_elim_unconstrained(assertions);
        assert_eq!(outcome.removed_assertions, 1);
        assert_eq!(
            outcome.assertions,
            vec![parse_term("(> x 0)"), parse_term("(> x 2)")]
        );
    }
}
