// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! What is in scope for a bound parse besides its text (see the parent
//! module): the spelling of the caller's sorts and declarations, the sort
//! names the parse binds, and the datatypes a text declares.

use std::collections::{HashMap, HashSet};

use ay_dpll::api::{Sort, SortExt};
use ay_frontend::command::{Index, Sort as ParsedSort};

use super::super::Z3Context;
use super::{
    BoundParse, Classified, GivenDeclaration, ParseScope, ParsedDeclaration, HELPER_PREFIX,
};

/// Why prelude construction stopped before the solver was mutated.
pub(super) enum PreludeError {
    /// The prelude is invalid in the current declaration context.
    Failed(String),
    /// A declaration has no faithful SMT-LIB spelling.
    Ineligible(String),
}

/// The prelude of a parse: caller-named declarations, then the solver's
/// earlier declarations the text does not redeclare, then its earlier
/// definitions; with the sort spellings it uses, the declarations in scope and
/// the caller-named declarations by name.
pub(super) fn build_prelude<'a>(
    ctx: &Z3Context,
    scope: &'a ParseScope,
    classified: &Classified,
) -> Result<
    (
        String,
        SortSpeller,
        Vec<ParsedDeclaration>,
        HashMap<String, &'a GivenDeclaration>,
    ),
    PreludeError,
> {
    if let Some(reason) = recursive_definition_collision(ctx, classified) {
        return Err(PreludeError::Failed(reason));
    }
    let mut speller = SortSpeller::default();
    let mut prelude = String::new();
    let mut in_scope: Vec<ParsedDeclaration> = Vec::new();
    let mut given_by_name: HashMap<String, &GivenDeclaration> = HashMap::new();
    for (name, given) in &scope.given {
        if classified.declared.contains(name) {
            continue;
        }
        given_by_name.insert(name.clone(), given);
        in_scope.push(given_signature(ctx, name, given));
    }
    for declaration in &scope.prior.declarations {
        if !classified.declared.contains(&declaration.name)
            && !in_scope.iter().any(|d| d.name == declaration.name)
        {
            in_scope.push(declaration.clone());
        }
    }
    for declaration in &in_scope {
        let Some(text) = declaration_text(declaration, &mut speller) else {
            return Err(PreludeError::Ineligible(format!(
                "the name {:?} has no SMT-LIB spelling",
                declaration.name
            )));
        };
        prelude.push_str(&text);
    }
    for definition in &scope.prior.definitions {
        prelude.push_str(definition);
    }
    Ok((prelude, speller, in_scope, given_by_name))
}

/// Why the text's first `define-fun-rec` whose name the context already
/// declares as a function (other than by the same definition in an earlier
/// text) is refused. The parse binds a text function to the context's
/// declaration of its name and signature, so the definition would be attached
/// to that function (T5 P0.2 Q5; ypins.py `q5_text_recdef_vs_api`):
///
/// * beside an API recursive function of the name, libz3 5.1.0 refuses the
///   text the same way ("recursive function r already defined");
/// * beside an API uninterpreted function `f`, libz3 5.1.0 accepts the text
///   and keeps the two apart (`f(0) == 5` stays `sat`), which the parse
///   cannot; the definition used to be attached to the uninterpreted `f`
///   (measured: `f(0) == 5` answered `unsat`), so the text is refused.
fn recursive_definition_collision(ctx: &Z3Context, classified: &Classified) -> Option<String> {
    classified.recs.iter().find_map(|rec| {
        let same_definition = ctx
            .text_datatypes
            .get(&format!("define-fun-rec {}", rec.name))
            .is_some_and(|source| *source == rec.source);
        if same_definition {
            return None;
        }
        let named = |(symbol, _, _): &(super::super::SymbolKey, Vec<Sort>, Sort)| {
            symbol.display_name() == rec.name
        };
        if ctx.ffi_rec_func_decls.keys().any(named) {
            return Some(format!("recursive function {} already defined", rec.name));
        }
        ctx.ffi_func_decls.keys().any(named).then(|| {
            format!(
                "invalid recursive definition: the context declares an uninterpreted function \
                 {}, and AY cannot keep a text's recursive function of that name apart from it",
                rec.name
            )
        })
    })
}

/// Whether a caller-named sort or declaration of `scope` involves a
/// `FiniteSet`.
pub(super) fn finite_set_reachable(ctx: &Z3Context, scope: &ParseScope) -> bool {
    let mentions = |sort: &Sort| super::super::sort_mentions_finite_set(ctx, sort);
    let given = scope.given.iter().any(|(_, given)| match given {
        // The caller's sort of the constant (the engine's is lowered).
        GivenDeclaration::Constant(term) => ctx
            .ffi_const_cache
            .iter()
            .any(|((_, sort), api)| api == term && mentions(sort)),
        GivenDeclaration::Function(decl) => ctx
            .finite_set_decl_signatures
            .get(decl.name())
            .is_some_and(|(domain, range)| domain.iter().any(mentions) || mentions(range)),
    });
    given
        || scope
            .sorts
            .iter()
            .any(|(_, sort)| super::super::finite_set_basis(ctx, sort).is_some())
}

/// Whether `sort` is a built-in sort this module can spell.
fn is_builtin_sort(sort: &ParsedSort) -> bool {
    match sort {
        ParsedSort::Simple(name) => matches!(
            name.as_str(),
            "Bool"
                | "Int"
                | "Real"
                | "String"
                | "RoundingMode"
                | "Float16"
                | "Float32"
                | "Float64"
                | "Float128"
        ),
        ParsedSort::Indexed(name, indices) => {
            matches!(name.as_str(), "BitVec" | "FloatingPoint")
                && indices
                    .iter()
                    .all(|index| matches!(index, Index::Numeral(_)))
        }
        ParsedSort::Parameterized(name, params) => {
            matches!(name.as_str(), "Array" | "Seq") && params.iter().all(is_builtin_sort)
        }
        _ => false,
    }
}

/// SMT-LIB text of a built-in sort.
fn sort_text(sort: &ParsedSort) -> String {
    match sort {
        ParsedSort::Simple(name) => name.clone(),
        ParsedSort::Indexed(name, indices) => {
            let indices: Vec<String> = indices
                .iter()
                .map(|index| match index {
                    Index::Numeral(text)
                    | Index::Decimal(text)
                    | Index::Symbol(text)
                    | Index::Hexadecimal(text) => text.clone(),
                    other => format!("{other:?}"),
                })
                .collect();
            format!("(_ {name} {})", indices.join(" "))
        }
        ParsedSort::Parameterized(name, params) => {
            let params: Vec<String> = params.iter().map(sort_text).collect();
            format!("({name} {})", params.join(" "))
        }
        other => format!("{other:?}"),
    }
}

/// `name` as an SMT-LIB symbol: bare when it lexes back as itself, quoted
/// otherwise; `None` for a name no symbol can spell.
pub(crate) fn spell_symbol(name: &str) -> Option<String> {
    const EXTRA: &str = "~!@$%^&*_-+=<>.?/";
    let plain = name.chars().next().is_some_and(|first| {
        !first.is_ascii_digit() && (first.is_ascii_alphanumeric() || EXTRA.contains(first))
    }) && name
        .chars()
        .all(|ch| ch.is_ascii_alphanumeric() || EXTRA.contains(ch));
    if plain {
        Some(name.to_string())
    } else if !name.is_empty() && !name.contains('|') && !name.contains('\\') {
        Some(format!("|{name}|"))
    } else {
        None
    }
}

/// Spells sorts for the prelude: a built-in sort as itself, any other sort
/// through a helper sort name bound to it.
#[derive(Default)]
pub(super) struct SortSpeller {
    pub(super) aliases: Vec<(String, Sort)>,
}

impl SortSpeller {
    fn spell(&mut self, sort: &Sort) -> String {
        let parsed = sort.to_command_sort();
        if is_builtin_sort(&parsed) {
            return sort_text(&parsed);
        }
        if let Some((name, _)) = self.aliases.iter().find(|(_, s)| s == sort) {
            return format!("|{name}|");
        }
        let name = format!("{HELPER_PREFIX}sort!{}", self.aliases.len());
        self.aliases.push((name.clone(), sort.clone()));
        format!("|{name}|")
    }
}

/// The engine signature of a given declaration.
fn given_signature(ctx: &Z3Context, name: &str, given: &GivenDeclaration) -> ParsedDeclaration {
    let (domain, range) = match given {
        GivenDeclaration::Constant(term) => (Vec::new(), ctx.solver.term_sort(*term)),
        GivenDeclaration::Function(decl) => (decl.domain().to_vec(), decl.range().clone()),
    };
    ParsedDeclaration {
        name: name.to_string(),
        domain,
        range,
    }
}

fn declaration_text(declaration: &ParsedDeclaration, speller: &mut SortSpeller) -> Option<String> {
    let domain: Vec<String> = declaration
        .domain
        .iter()
        .map(|s| speller.spell(s))
        .collect();
    Some(format!(
        "(declare-fun {} ({}) {})",
        spell_symbol(&declaration.name)?,
        domain.join(" "),
        speller.spell(&declaration.range)
    ))
}

/// Bind the sort names of the parse: helper aliases, caller-named sorts, and
/// the declared sort names of the solver and the text.
pub(super) fn bind_sorts(
    ctx: &mut Z3Context,
    speller: &SortSpeller,
    scope: &ParseScope,
    text_sorts: &[String],
) -> Result<(), String> {
    for (name, sort) in &speller.aliases {
        ctx.solver
            .try_bind_sort_name(name, sort)
            .map_err(|e| e.to_string())?;
    }
    // A text's `declare-sort` of a datatype's name would share the datatype's
    // engine sort: refused (see `uninterpreted_sort_name_collision`).
    for name in text_sorts {
        if let Some(reason) = super::super::uninterpreted_sort_name_collision(ctx, name) {
            return Err(format!("invalid sort declaration, {reason}"));
        }
        ctx.uninterpreted_sort_names.insert(name.clone());
    }
    let mut named: Vec<(String, Sort)> = scope.sorts.clone();
    let mut seen: HashSet<String> = named.iter().map(|(n, _)| n.clone()).collect();
    for name in scope.prior.sorts.iter().chain(text_sorts) {
        if seen.insert(name.clone()) {
            named.push((name.clone(), Sort::Uninterpreted(name.clone())));
        } else if text_sorts.contains(name) && scope.prior.sorts.contains(name) {
            return Err(format!(
                "invalid sort declaration, sort '{name}' already declared"
            ));
        }
    }
    for (name, sort) in named {
        let wanted = ctx.solver.live_sort(&sort);
        match ctx.solver.resolve_sort_name(&name) {
            Some(existing) if existing == wanted => {}
            _ => ctx
                .solver
                .try_bind_sort_name(&name, &sort)
                .map_err(|e| e.to_string())?,
        }
    }
    Ok(())
}

/// Declare the text's datatypes in the context: first inside a popped scope
/// (a rejected declaration leaves the engine as it was), then for good.
/// `None` when they are declared; otherwise the outcome of the parse.
pub(super) fn declare_text_datatypes(
    ctx: &mut Z3Context,
    classified: &Classified,
) -> Option<BoundParse> {
    // The same declaration in another text is the same datatype; any other
    // declaration of a declared sort name is refused.
    let normalized = |text: &str| text.split_whitespace().collect::<Vec<_>>().join(" ");
    let declared = classified.datatypes.iter().all(|text| {
        let text = normalized(text);
        ctx.text_datatypes.values().any(|known| *known == text)
    }) && classified
        .datatype_sorts
        .iter()
        .all(|name| ctx.text_datatypes.contains_key(name));
    if declared {
        return None;
    }
    // A datatype named like an uninterpreted sort would share its engine
    // sort: refused (see `datatype_name_collision`).
    if let Some(reason) = classified
        .datatype_sorts
        .iter()
        .find_map(|name| super::super::datatype_name_collision(ctx, name))
    {
        return Some(BoundParse::Failed(format!("invalid declaration, {reason}")));
    }
    // A datatype the context already has (an API `Datatype` of the same name,
    // constructors and fields) is the same sort, as in z3.
    #[expect(
        clippy::suspicious_operation_groupings,
        reason = "context datatype fields are intentionally compared with parsed constructor selectors"
    )]
    let same_as_context =
        !classified.datatype_decs.is_empty()
            && classified.datatype_decs.iter().all(|(name, dec)| {
                ctx.ffi_sort_symbols
                    .iter()
                    .any(|(sort, symbol)| match sort {
                        Sort::Datatype(existing) => {
                            symbol.display_name() == *name
                                && dec.type_params.is_empty()
                                && existing.constructors.len() == dec.constructors.len()
                                && existing.constructors.iter().zip(&dec.constructors).all(
                                    |(a, b)| {
                                        a.name == b.name
                                            && a.fields.len() == b.selectors.len()
                                            && a.fields
                                                .iter()
                                                .zip(&b.selectors)
                                                .all(|(f, s)| f.name == s.name)
                                    },
                                )
                        }
                        _ => false,
                    })
            });
    if same_as_context {
        return None;
    }
    if let Some(name) = classified
        .datatype_sorts
        .iter()
        .find(|name| ctx.solver.resolve_sort_name(name).is_some())
    {
        return Some(BoundParse::Failed(format!(
            "invalid declaration, sort '{name}' already declared"
        )));
    }
    let text = classified.datatypes.concat();
    if let Err(e) = ctx.solver.try_push() {
        return Some(BoundParse::ScopeLost(format!(
            "cannot open the parse scope: {e}"
        )));
    }
    let trial = ctx.solver.parse_smtlib2_z3_5(&text).map(|_| ());
    if let Err(e) = ctx.solver.try_pop() {
        return Some(BoundParse::ScopeLost(format!(
            "the parse scope could not be closed: {e}"
        )));
    }
    if let Err(e) = trial {
        return Some(BoundParse::Failed(e.to_string()));
    }
    match ctx.solver.parse_smtlib2_z3_5(&text) {
        Ok(_) => {
            for declaration in &classified.datatypes {
                let declaration = normalized(declaration);
                for name in &classified.datatype_sorts {
                    ctx.text_datatypes
                        .entry(name.clone())
                        .or_insert_with(|| declaration.clone());
                }
            }
            None
        }
        Err(e) => Some(BoundParse::ScopeLost(format!(
            "a datatype declaration failed after it was checked: {e}"
        ))),
    }
}
