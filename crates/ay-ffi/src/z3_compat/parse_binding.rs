// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Binding the names an SMT-LIB text declares to the context's declarations.
//!
//! z3 identifies a function declaration by its name, domain and range, and an
//! uninterpreted sort by its name, so a text parsed by `Z3_solver_from_string`,
//! `Z3_parse_smtlib2_string` or `Z3_optimize_from_string` that declares
//! `(declare-fun p () Bool)` denotes the SAME constant as the API's
//! `Bool('p')`, before or after the parse. AY's engine keeps the API's
//! declarations under private identities, and the parser used to declare a
//! second, unrelated engine symbol for `p`: a parsed `(assert p)` never
//! constrained the API's `p` (measured: `sat` with the model `[p = false,
//! p = true]` where z3 answers `unsat`).
//!
//! A text is therefore parsed inside a scope that is popped afterwards, and
//! every symbol it declares is rebound, in the parsed formulas, to the
//! context's API declaration with the same name and signature (created on
//! first use, exactly as `Z3_mk_const` / `Z3_mk_func_decl` create it). Each
//! parse starts from a fresh symbol table, as z3's does; a solver's earlier
//! declarations, definitions and sorts stay visible to its later parses (z3
//! keeps one command context per solver), and `Z3_parse_smtlib2_string`'s
//! caller-named declarations and sorts are bound the way z3 binds them.
//!
//! The commands of a text are handled as follows:
//! - `declare-fun` / `declare-const`: rebound as above;
//! - `declare-sort U 0`: the sort NAME is bound to the context's sort `U`
//!   (`Z3_mk_uninterpreted_sort`), never a sort of the parse's own;
//! - `declare-datatype(s)`: declared in the context before the scoped parse
//!   (the same declaration again, or one identical to a caller's datatype, is
//!   that sort);
//! - `define-fun` / `define-sort`: macros and synonyms, expanded by the parse
//!   and remembered for the solver's later texts;
//! - `define-fun-rec` / `define-funs-rec`: the function is the context's
//!   declaration and its body is registered as `Z3_add_rec_def` registers one;
//! - `set-logic`, `set-option`, `set-info` and queries: no effect on the
//!   parsed formulas (z3 applies them to the text's own command context);
//! - `assert`, and for an Optimize `assert-soft` / `maximize` / `minimize`:
//!   the parsed formulas.
//!
//! Any other command makes the text ineligible; the caller then parses it
//! globally, refusing a text that would declare a name the context already
//! declared (see `solver::global_parse_collision`).

use std::collections::{HashMap, HashSet};

use ay_dpll::api::{FuncDecl, Sort, Term};

use super::{ObjectiveSense, Z3Context};

mod classify;
mod prelude;
mod rebind;
mod sexp_items;
use classify::{classify, split_commands, Classified, RecDefinition};
use prelude::{bind_sorts, build_prelude, declare_text_datatypes, finite_set_reachable};
use rebind::Rebinder;

/// Prefix of the parse's own helper names (sort aliases, recursive-definition
/// parameters). A text that mentions it is ineligible, so a helper never
/// captures a name of the text.
const HELPER_PREFIX: &str = "ay!parse-";

/// One symbol a parsed text declared, with its engine sorts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ParsedDeclaration {
    pub(crate) name: String,
    pub(crate) domain: Vec<Sort>,
    pub(crate) range: Sort,
}

/// What a solver's parses leave for its later parses (z3 keeps one command
/// context per solver).
#[derive(Clone, Debug, Default)]
pub(crate) struct ParsePrior {
    /// Declared constants and functions.
    pub(crate) declarations: Vec<ParsedDeclaration>,
    /// Declared sort names (`declare-sort U 0`), each the context's sort `U`.
    pub(crate) sorts: Vec<String>,
    /// `define-fun` and `define-sort` commands, verbatim, in order.
    pub(crate) definitions: Vec<String>,
}

impl ParsePrior {
    pub(crate) fn extend(&mut self, other: ParsePrior) {
        self.declarations.extend(other.declarations);
        self.sorts.extend(other.sorts);
        self.definitions.extend(other.definitions);
    }
}

/// The context declaration a caller of `Z3_parse_smtlib2_string` named for a
/// text symbol.
pub(crate) enum GivenDeclaration {
    /// A constant (`decls={'foo': x}`).
    Constant(Term),
    /// A function of positive arity.
    Function(FuncDecl),
}

/// What is in scope for one parse besides the text's own declarations.
#[derive(Default)]
pub(crate) struct ParseScope {
    /// What earlier parses of the same handle left in scope.
    pub(crate) prior: ParsePrior,
    /// Caller-named declarations: text name -> declaration.
    pub(crate) given: Vec<(String, GivenDeclaration)>,
    /// Caller-named sorts: text name -> sort.
    pub(crate) sorts: Vec<(String, Sort)>,
    /// Whether `assert-soft`, `maximize` and `minimize` are accepted (an
    /// Optimize parse).
    pub(crate) objectives: bool,
}

/// The formulas of a bound parse.
#[derive(Default)]
pub(crate) struct ParsedContent {
    pub(crate) assertions: Vec<Term>,
    /// Soft constraints: formula, weight, group id.
    pub(crate) softs: Vec<(Term, u64, Option<String>)>,
    pub(crate) objectives: Vec<(Term, ObjectiveSense)>,
    /// What this text adds to its handle's [`ParsePrior`].
    pub(crate) prior: ParsePrior,
}

/// The outcome of [`bound_parse`].
pub(crate) enum BoundParse {
    /// The text is outside the rebinding fragment (the reason); nothing was
    /// executed.
    Ineligible(String),
    /// Parsed and rebound.
    Parsed(ParsedContent),
    /// The text was rejected; the scope was rolled back.
    Failed(String),
    /// The parse scope could not be opened or closed: the engine state is
    /// unknown.
    ScopeLost(String),
}

/// z3 keeps one command context per solver: a text that declares a name
/// again with the same signature is an error there (a different signature is
/// an overload). The error for the first such declaration, if any.
fn redeclaration_error(
    text_declarations: &[ParsedDeclaration],
    prior: &[ParsedDeclaration],
) -> Option<String> {
    let again = text_declarations
        .iter()
        .find(|declaration| prior.contains(declaration))?;
    let kind = if again.domain.is_empty() {
        "constant"
    } else {
        "function"
    };
    Some(format!(
        "invalid declaration, {kind} '{}' (with the given signature) already declared",
        again.name
    ))
}

/// Parse `input` inside a popped scope and rebind its declarations to the
/// context's; see the module docs.
pub(crate) fn bound_parse(ctx: &mut Z3Context, input: &str, scope: &ParseScope) -> BoundParse {
    if input.contains(HELPER_PREFIX) {
        return BoundParse::Ineligible(format!("the text mentions {HELPER_PREFIX}"));
    }
    // A `FiniteSet` keeps a public sort apart from its engine lowering, which
    // only the global parse's retention restores.
    if input.contains("FiniteSet") || finite_set_reachable(ctx, scope) {
        return BoundParse::Ineligible("a FiniteSet".to_string());
    }
    let pieces = match split_commands(input) {
        Ok(pieces) => pieces,
        Err(e) => return BoundParse::Failed(e),
    };
    let classified = match classify(pieces, scope.objectives) {
        Ok(classified) => classified,
        Err(command) => return BoundParse::Ineligible(command),
    };
    let (prelude, speller, in_scope, given_by_name) = match build_prelude(ctx, scope, &classified) {
        Ok(built) => built,
        Err(outcome) => return outcome,
    };
    if !classified.datatypes.is_empty() {
        if let Some(outcome) = declare_text_datatypes(ctx, &classified) {
            return outcome;
        }
    }
    if let Err(e) = ctx.solver.try_push() {
        return BoundParse::ScopeLost(format!("cannot open the parse scope: {e}"));
    }
    let outcome = bind_sorts(ctx, &speller, scope, &classified.sorts).and_then(|()| {
        run_bound_parse(ctx, &prelude, &classified, &in_scope, given_by_name, scope)
    });
    let popped = ctx.solver.try_pop();
    let outcome = outcome.and_then(|(mut content, recs)| {
        register_text_rec_defs(ctx, recs, &classified.recs)?;
        content.prior.sorts = classified.sorts.clone();
        content.prior.definitions = classified.definitions.clone();
        Ok(content)
    });
    match (outcome, popped) {
        (Ok(content), Ok(())) => BoundParse::Parsed(content),
        (Err(reason), Ok(())) => BoundParse::Failed(reason),
        (Ok(_), Err(e)) | (Err(_), Err(e)) => {
            BoundParse::ScopeLost(format!("the parse scope could not be closed: {e}"))
        }
    }
}

/// Register a text's recursive definitions in the context (z3 registers a
/// `define-fun-rec` of a text in the context's recursive-function plugin);
/// the same definition from another text is the same function.
fn register_text_rec_defs(
    ctx: &mut Z3Context,
    recs: Vec<RecRegistration>,
    definitions: &[RecDefinition],
) -> Result<(), String> {
    for ((decl, display, args, body), rec) in recs.into_iter().zip(definitions) {
        let key = format!("define-fun-rec {display}");
        if ctx.rec_fun_defs.contains_key(decl.name())
            && ctx.text_datatypes.get(&key) == Some(&rec.source)
        {
            continue;
        }
        super::misc_ext::register_rec_def(ctx, &decl, &display, &args, body)
            .map_err(|(_, message)| message)?;
        ctx.text_datatypes.insert(key, rec.source.clone());
    }
    Ok(())
}

/// A recursive definition to register: the function, its display name, the
/// parameter constants and the body.
type RecRegistration = (FuncDecl, String, Vec<Term>, Term);

/// The parse and rebinding inside the open scope.
fn run_bound_parse(
    ctx: &mut Z3Context,
    prelude: &str,
    classified: &Classified,
    in_scope: &[ParsedDeclaration],
    given_by_name: HashMap<String, &GivenDeclaration>,
    scope: &ParseScope,
) -> Result<(ParsedContent, Vec<RecRegistration>), String> {
    let before: HashSet<String> = ctx
        .solver
        .symbol_signatures_core()
        .into_iter()
        .map(|(_, identity, ..)| identity)
        .collect();
    let batch = ctx
        .solver
        .parse_smtlib2_z3_5(&format!("{prelude}\n{}", classified.body))
        .map_err(|e| e.to_string())?;
    let (identities, text_declarations) = parse_identities(ctx, &before, classified, in_scope);
    if let Some(error) = redeclaration_error(&text_declarations, &scope.prior.declarations) {
        return Err(error);
    }
    let retained = super::retain_parsed_finite_set_batch(ctx, batch)
        .map_err(|e| format!("parsed public FiniteSet metadata could not be retained: {e}"))?;
    if retained.soft_constraints.len() != classified.softs.len()
        || retained.objectives.len() != classified.objectives.len()
    {
        return Err("the parsed objectives do not match the text".to_string());
    }
    let mut rebinder = Rebinder {
        identities,
        given: given_by_name,
        rec_params: classified.rec_params.clone(),
        constants: HashMap::new(),
        functions: HashMap::new(),
        memo: HashMap::new(),
    };
    let mut assertions = Vec::with_capacity(retained.assertions.len());
    for assertion in retained.assertions {
        assertions.push(rebinder.rebind(ctx, assertion, &mut Vec::new())?);
    }
    let mut recs = Vec::new();
    for (rec, &marker) in classified.recs.iter().zip(&classified.rec_markers) {
        recs.push(rec_registration(
            ctx,
            &rebinder,
            rec,
            assertions.get(marker).copied(),
        )?);
    }
    let markers: HashSet<usize> = classified.rec_markers.iter().copied().collect();
    let assertions = assertions
        .into_iter()
        .enumerate()
        .filter(|(index, _)| !markers.contains(index))
        .map(|(_, term)| term)
        .collect();
    let mut softs = Vec::new();
    for (term, (weight, group)) in retained.soft_constraints.into_iter().zip(&classified.softs) {
        softs.push((
            rebinder.rebind(ctx, term, &mut Vec::new())?,
            *weight,
            group.clone(),
        ));
    }
    let mut objectives = Vec::new();
    for (term, sense) in retained.objectives.into_iter().zip(&classified.objectives) {
        objectives.push((rebinder.rebind(ctx, term, &mut Vec::new())?, *sense));
    }
    Ok((
        ParsedContent {
            assertions,
            softs,
            objectives,
            prior: ParsePrior {
                declarations: text_declarations,
                ..ParsePrior::default()
            },
        },
        recs,
    ))
}

/// Every identity the parse declared for a name of the text or of the
/// prelude (`before` holds the identities that existed before it), and the
/// declarations of the text itself.
fn parse_identities(
    ctx: &Z3Context,
    before: &HashSet<String>,
    classified: &Classified,
    in_scope: &[ParsedDeclaration],
) -> (HashMap<String, ParsedDeclaration>, Vec<ParsedDeclaration>) {
    let in_scope_names: HashSet<&str> = in_scope.iter().map(|d| d.name.as_str()).collect();
    let mut identities: HashMap<String, ParsedDeclaration> = HashMap::new();
    let mut text_declarations = Vec::new();
    for (name, identity, domain, range, is_definition) in ctx.solver.symbol_signatures_core() {
        if is_definition || before.contains(&identity) {
            continue;
        }
        let from_text = classified.declared.contains(&name);
        if !from_text && !in_scope_names.contains(name.as_str()) {
            continue;
        }
        let declaration = ParsedDeclaration {
            name,
            domain,
            range,
        };
        if from_text && !classified.rec_params.contains_key(&declaration.name) {
            text_declarations.push(declaration.clone());
        }
        identities.insert(identity, declaration);
    }
    (identities, text_declarations)
}

/// The registration of one recursive definition from its rebound marker
/// `(marker (f a0 ...) body)`.
fn rec_registration(
    ctx: &mut Z3Context,
    rebinder: &Rebinder<'_>,
    rec: &RecDefinition,
    marker: Option<Term>,
) -> Result<RecRegistration, String> {
    let malformed = || format!("the recursive definition of {} did not parse", rec.name);
    let marker = marker.ok_or_else(malformed)?;
    let sides = ctx.solver.term_children(marker);
    let [lhs, body] = sides.as_slice() else {
        return Err(malformed());
    };
    let args = ctx.solver.term_children(*lhs);
    if args.len() != rec.arity || rec.params.len() != rec.arity {
        return Err(malformed());
    }
    let decl = rebinder
        .function_named(&rec.name, rec.arity)
        .ok_or_else(malformed)?;
    Ok((decl, rec.name.clone(), args, *body))
}
