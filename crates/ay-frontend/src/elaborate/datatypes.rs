// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};

use crate::command;
use ay_core::Sort;

use super::{is_reserved_symbol, Context, ElaborateError, Result, SymbolInfo};

/// Mangle a parametric-datatype instantiation `(Name A1 .. An)` into a unique,
/// deterministic sort name used as `Sort::Uninterpreted(<mangled>)`.
///
/// Each argument is wrapped in `!{...}` so nested instances stay unambiguous:
/// `(Lst Int)` -> `Lst!{Int}`, `(Lst (Lst Int))` -> `Lst!{Lst!{Int}}`,
/// `(Pair Int Bool)` -> `Pair!{Int}!{Bool}`. The braces are balanced, so no two
/// distinct applied sorts can collide on the same name.
pub(crate) fn mangle_datatype_instance(name: &str, args: &[Sort]) -> String {
    let mut out = String::from(name);
    for arg in args {
        out.push_str("!{");
        mangle_sort_into(&mut out, arg);
        out.push('}');
    }
    out
}

/// Mangle a constructor/selector member `surface` into its instance-specific
/// INTERNAL name `surface@<instance>`, or `None` for a monomorphic datatype
/// (`instance == None`, surface name used directly). Deterministic and
/// injective (the `instance` sort name is itself unique per instantiation), so
/// distinct instances never collide; un-mangling uses the recorded reverse map.
// Nursery false positive: the Option-in/Option-out shape IS the contract
// (None = monomorphic, surface name used directly); moving the `.map` to the
// three call sites would scatter that rule instead of keeping it here.
#[allow(clippy::single_option_map)]
pub(crate) fn mangle_member(surface: &str, instance: Option<&str>) -> Option<String> {
    instance.map(|inst| format!("{surface}@{inst}"))
}

fn mangle_sort_into(out: &mut String, sort: &Sort) {
    use std::fmt::Write as _;
    match sort {
        Sort::Bool => out.push_str("Bool"),
        Sort::Int => out.push_str("Int"),
        Sort::Real => out.push_str("Real"),
        Sort::String => out.push_str("String"),
        Sort::RegLan => out.push_str("RegLan"),
        Sort::BitVec(bv) => {
            let _ = write!(out, "BitVec_{}", bv.width);
        }
        Sort::FloatingPoint(eb, sb) => {
            let _ = write!(out, "FloatingPoint_{eb}_{sb}");
        }
        // Already-mangled instance names, user sorts, and concrete datatypes are
        // injective in their names.
        Sort::Uninterpreted(n) => out.push_str(n),
        Sort::Datatype(dt) => out.push_str(&dt.name),
        Sort::Array(arr) => {
            out.push_str("Array!{");
            mangle_sort_into(out, &arr.index_sort);
            out.push_str("}!{");
            mangle_sort_into(out, &arr.element_sort);
            out.push('}');
        }
        Sort::Seq(elem) => {
            out.push_str("Seq!{");
            mangle_sort_into(out, elem);
            out.push('}');
        }
        // `Sort` is #[non_exhaustive]; any future variant falls back to its Debug
        // encoding, which stays injective for distinct sorts so the mangled
        // instance name remains unambiguous.
        other => {
            let _ = write!(out, "{other:?}");
        }
    }
}

impl Context {
    /// Register a datatype's constructors, selectors, and testers against the
    /// (already-registered) datatype sort `dt_sort`.
    ///
    /// `subst` substitutes a parametric datatype's bound type parameters into
    /// the selector field sorts; it is empty for monomorphic datatypes (so their
    /// elaboration is unchanged). Shared by [`Context::declare_datatype`],
    /// [`Context::declare_datatypes`], and the lazy monomorphizer
    /// [`Context::instantiate_parametric_datatype`].
    fn register_datatype_constructors(
        &mut self,
        dt_name: &str,
        dt_sort: &Sort,
        constructors: &[command::ConstructorDec],
        subst: &HashMap<String, Sort>,
        instance: Option<&str>,
    ) -> Result<()> {
        let selector_sorts = self.elaborate_datatype_selector_sorts(constructors, subst)?;
        self.register_elaborated_datatype_constructors(
            dt_name,
            dt_sort,
            constructors,
            &selector_sorts,
            instance,
        );
        Ok(())
    }

    /// Elaborate every selector sort before datatype metadata is committed.
    /// Keeping the fallible phase separate makes ordinary datatype declarations
    /// transactional without cloning the full term/assertion context.
    fn elaborate_datatype_selector_sorts(
        &mut self,
        constructors: &[command::ConstructorDec],
        subst: &HashMap<String, Sort>,
    ) -> Result<Vec<Vec<Sort>>> {
        constructors
            .iter()
            .map(|ctor| {
                ctor.selectors
                    .iter()
                    .map(|selector| self.elaborate_sort_inner(&selector.sort, subst))
                    .collect::<Result<Vec<_>>>()
            })
            .collect()
    }

    /// Commit constructors whose selector sorts have already been elaborated.
    /// This phase is intentionally infallible: all user-controlled validation
    /// happens before any datatype/symbol maps are changed.
    fn register_elaborated_datatype_constructors(
        &mut self,
        dt_name: &str,
        dt_sort: &Sort,
        constructors: &[command::ConstructorDec],
        selector_sorts: &[Vec<Sort>],
        instance: Option<&str>,
    ) {
        debug_assert_eq!(constructors.len(), selector_sorts.len());
        for (ctor, selector_sorts) in constructors.iter().zip(selector_sorts) {
            // For a monomorphized parametric INSTANCE, the constructor/selector/
            // tester get INTERNAL names that are name-disjoint per instance
            // (e.g. `osome@Opt!{Bool}`), so the DT theory treats each instance as
            // its own datatype. The user-facing surface names stay shared and are
            // resolved to these internal names by argument/result sort. Monomorphic
            // datatypes pass `instance = None` and use the surface names directly.
            let mctor = mangle_member(&ctor.name, instance);
            let ctor_internal = mctor.as_deref().unwrap_or(&ctor.name);
            let sel_internals: Vec<String> = ctor
                .selectors
                .iter()
                .map(|s| mangle_member(&s.name, instance).unwrap_or_else(|| s.name.clone()))
                .collect();

            // Track constructor -> selectors mapping (positional), keyed by the
            // internal constructor name.
            self.ctor_selectors
                .insert(ctor_internal.to_string(), sel_internals.clone());
            // Track constructor -> datatype mapping.
            self.constructors.insert(
                ctor_internal.to_string(),
                (dt_name.to_string(), ctor_internal.to_string()),
            );
            self.track_scoped_constructor(ctor_internal.to_string());
            self.ctor_selector_info.insert(
                ctor_internal.to_string(),
                sel_internals
                    .iter()
                    .zip(selector_sorts.iter())
                    .map(|(sel_internal, sel_sort)| (sel_internal.clone(), sel_sort.clone()))
                    .collect(),
            );

            // Record internal -> surface mappings for model un-mangling.
            if instance.is_some() {
                self.track_internal_surface(ctor_internal.to_string(), ctor.name.clone());
                for (sel, sel_internal) in ctor.selectors.iter().zip(sel_internals.iter()) {
                    self.track_internal_surface(sel_internal.clone(), sel.name.clone());
                }
                self.track_internal_surface(
                    format!("is-{ctor_internal}"),
                    format!("is-{}", ctor.name),
                );
            }

            // Constructor: (sel_sort1, ..., sel_sortN) -> DataType. The bound term
            // for a nullary constructor uses the INTERNAL name.
            let ctor_term = if selector_sorts.is_empty() {
                let t = self
                    .terms
                    .mk_fresh_named_var(ctor_internal, dt_sort.clone());
                // Record the exact term so constructor-shape folds recognize the
                // nullary constructor (it is a Var, not an App). (#rec-dt-expansion)
                self.nullary_ctor_terms.insert(ctor_internal.to_string(), t);
                Some(t)
            } else {
                None
            };
            self.register_overloadable_symbol(
                ctor.name.clone(),
                SymbolInfo {
                    term: ctor_term,
                    sort: dt_sort.clone(),
                    arg_sorts: selector_sorts.clone(),
                    internal_name: mctor.clone(),
                },
            );

            // Selectors: DataType -> field_sort
            for ((sel, sel_sort), sel_internal) in ctor
                .selectors
                .iter()
                .zip(selector_sorts.iter())
                .zip(sel_internals.iter())
            {
                self.register_overloadable_symbol(
                    sel.name.clone(),
                    SymbolInfo {
                        term: None,
                        sort: sel_sort.clone(),
                        arg_sorts: vec![dt_sort.clone()],
                        internal_name: instance.map(|_| sel_internal.clone()),
                    },
                );
            }

            // Tester: DataType -> Bool. Surface `is-<ctor>` resolves to the
            // instance-internal `is-<ctor_internal>`.
            self.register_overloadable_symbol(
                format!("is-{}", ctor.name),
                SymbolInfo {
                    term: None,
                    sort: Sort::Bool,
                    arg_sorts: vec![dt_sort.clone()],
                    internal_name: instance.map(|_| format!("is-{ctor_internal}")),
                },
            );
        }
    }

    /// Whether `name` is a registered datatype member name — a constructor,
    /// selector, or tester (`is-<ctor>`), by internal or user-facing surface
    /// name, including members of not-yet-instantiated parametric templates.
    ///
    /// The DT theory matches member operations structurally by name on
    /// `App(Named(name), ..)`, so a user `declare-fun`/`declare-const`/
    /// `define-fun` of a member name is silently conflated with the builtin
    /// operation (confirmed wrong-UNSAT class: post-hoc `declare-fun is-Cons`
    /// / `hd` / `Cons` forgeries). The declaration paths in `declarations.rs`
    /// reject such names with [`ElaborateError::DatatypeMemberCollision`]
    /// (`super::ElaborateError`). The programmatic ay-dpll API instead ADOPTS
    /// an identical-signature redeclaration as a handle to the member — the
    /// documented embedder contract — via this same check plus
    /// [`Context::has_symbol_with_signature`].
    pub fn is_datatype_member_name(&self, name: &str) -> bool {
        if self.constructors.contains_key(name) {
            return true;
        }
        if let Some(ctor) = name.strip_prefix("is-") {
            if self.constructors.contains_key(ctor) {
                return true;
            }
        }
        if self
            .ctor_selector_info
            .values()
            .any(|sels| sels.iter().any(|(sel, _)| sel == name))
        {
            return true;
        }
        // Parametric-INSTANCE members: ordinary declaration overloads also use
        // the internal->surface map, so require datatype metadata for the
        // mapped internal identity rather than classifying every alias as a
        // constructor/selector/tester.
        let mapped_datatype_member = self.dt_internal_surface.iter().any(|(internal, surface)| {
            if surface != name {
                return false;
            }
            self.constructors.contains_key(internal)
                || internal
                    .strip_prefix("is-")
                    .is_some_and(|ctor| self.constructors.contains_key(ctor))
                || self
                    .ctor_selector_info
                    .values()
                    .any(|selectors| selectors.iter().any(|(selector, _)| selector == internal))
        });
        if mapped_datatype_member {
            return true;
        }
        // Parametric TEMPLATE members (not yet instantiated): their surface
        // names become live operations at first instantiation, so declaring
        // them is gated too.
        self.parametric_datatypes.values().any(|dec| {
            dec.constructors.iter().any(|ctor| {
                ctor.name == name
                    || name.strip_prefix("is-").is_some_and(|n| n == ctor.name)
                    || ctor.selectors.iter().any(|sel| sel.name == name)
            })
        })
    }

    /// Reject a datatype declaration that re-uses an already-declared sort
    /// name ([`ElaborateError::SortRedeclaration`]). Re-declaring an existing
    /// sort as a datatype is malformed SMT-LIB, and it is the only way a
    /// pre-existing user symbol can mention the new datatype's carrier sort —
    /// after which the DT theory captures that symbol's applications as
    /// member operations (confirmed wrong-UNSAT class, e.g. `declare-sort
    /// Lst` + `declare-fun hd (Lst) Int` + use + `declare-datatype Lst ((Cons
    /// (hd Int)) …)` conflated the pre-declared `hd` with the new selector).
    /// Member-name overloading WITHOUT a sort redeclaration (e.g. a plain
    /// `declare-fun hd (Int) Int` before a datatype with selector `hd`, or two
    /// datatypes sharing a selector name) cannot mention the new carrier sort
    /// and stays supported — overload resolution disambiguates by sort.
    fn check_datatype_sort_redeclaration(&self, name: &str) -> Result<()> {
        if self.sort_defs.contains_key(name)
            || self.parametric_sort_defs.contains_key(name)
            || self.datatypes.contains_key(name)
            || self.parametric_datatypes.contains_key(name)
        {
            return Err(ElaborateError::SortRedeclaration(name.to_string()));
        }
        Ok(())
    }

    /// Validate that a datatype declaration uses no reserved symbols.
    fn validate_datatype_names(name: Option<&str>, dec: &command::DatatypeDec) -> Result<()> {
        if let Some(name) = name {
            if is_reserved_symbol(name) {
                return Err(ElaborateError::ReservedSymbol(name.to_string()));
            }
        }
        for ctor in &dec.constructors {
            if is_reserved_symbol(&ctor.name) {
                return Err(ElaborateError::ReservedSymbol(ctor.name.clone()));
            }
            for sel in &ctor.selectors {
                if is_reserved_symbol(&sel.name) {
                    return Err(ElaborateError::ReservedSymbol(sel.name.clone()));
                }
            }
        }
        Ok(())
    }

    /// Build the narrow context needed to preflight selector sorts. This copies
    /// only sort aliases/templates, not the term store, assertions, symbols, or
    /// scopes that dominate a live solver context.
    pub(super) fn datatype_sort_preflight_context(&self) -> Self {
        let mut context = Self::new();
        context.sort_defs = self.sort_defs.clone();
        context.parametric_sort_defs = self.parametric_sort_defs.clone();
        context.parametric_datatypes = self.parametric_datatypes.clone();
        // The scratch context must accept exactly what the LIVE one will, or it
        // rejects field sorts the live pass would have accepted. In particular a
        // PROGRAMMATIC declaration may name an uninterpreted field sort into
        // existence (see the `native_global_declaration` arm in
        // `elaborate_sort_dispatch`); without this the preflight would reject
        // every embedder datatype over such a sort.
        context.native_global_declaration = self.native_global_declaration;
        context
    }

    /// Declare a single datatype
    ///
    /// A datatype declaration creates:
    /// - A new uninterpreted sort
    /// - A constructor function for each constructor
    /// - A selector function for each selector
    /// - A tester function (is-Constructor) for each constructor
    ///
    /// A parametric `(par (T..) ..)` declaration is instead stored as a template
    /// and lazily monomorphized at each ground use (see
    /// [`Context::instantiate_parametric_datatype`]).
    pub(crate) fn declare_datatype(
        &mut self,
        name: &str,
        datatype_dec: &command::DatatypeDec,
    ) -> Result<()> {
        // Validate datatype name and all constructor/selector names
        Self::validate_datatype_names(Some(name), datatype_dec)?;
        // IDEMPOTENT re-declaration: adopt an EXACTLY-identical datatype
        // re-declaration as a no-op, mirroring `try_declare_fun`'s adopt-identical
        // embedder contract (an embedder that sets up its datatypes once and then
        // re-asserts a canonical declaration before each selector/match use should
        // not have to track what it already declared). SOUND — only an exact
        // `DatatypeDec` match is adopted; a plain-sort redeclaration (the
        // wrong-UNSAT class) or a DIFFERENT datatype of the same name still falls
        // through to `check_datatype_sort_redeclaration` below.
        if self.monomorphic_datatype_decs.get(name) == Some(datatype_dec) {
            return Ok(());
        }
        // Reject re-declaring an existing sort name (#reserved-ops reverse
        // gate; see `check_datatype_sort_redeclaration`).
        self.check_datatype_sort_redeclaration(name)?;

        // Parametric datatype: store the template and defer monomorphization.
        if !datatype_dec.type_params.is_empty() {
            self.parametric_datatypes
                .insert(name.to_string(), datatype_dec.clone());
            self.track_scoped_parametric(name.to_string());
            return Ok(());
        }

        let empty: HashMap<String, Sort> = HashMap::default();
        let mut preflight = self.datatype_sort_preflight_context();
        preflight
            .sort_defs
            .insert(name.to_string(), Sort::Uninterpreted(name.to_string()));
        preflight.elaborate_datatype_selector_sorts(&datatype_dec.constructors, &empty)?;

        // Register the carrier sort BEFORE elaborating the field sorts: a
        // datatype is in scope inside its own declaration (SMT-LIB 2.6 §4.2.3 —
        // that is what makes `(declare-datatype Lst ((nil) (cons (hd Int) (tl
        // Lst))))` recursive). This used to rely on unresolved sort names
        // silently becoming fresh uninterpreted sorts; now that an unknown sort
        // is an error, the name has to actually be in the signature. The
        // preflight above already validated the same field sorts against a
        // scratch context, so the live elaboration cannot fail on user input —
        // but roll the registration back if it ever does, rather than leaving a
        // half-declared sort behind.
        let sort = Sort::Uninterpreted(name.to_string());
        let sort_def_existed = self
            .sort_defs
            .insert(name.to_string(), sort.clone())
            .is_some();
        let selector_sorts =
            match self.elaborate_datatype_selector_sorts(&datatype_dec.constructors, &empty) {
                Ok(selector_sorts) => selector_sorts,
                Err(error) => {
                    if !sort_def_existed {
                        self.sort_defs.remove(name);
                    }
                    return Err(error);
                }
            };

        // Collect constructor names for datatype lookup
        let ctor_names: Vec<String> = datatype_dec
            .constructors
            .iter()
            .map(|c| c.name.clone())
            .collect();
        self.datatypes.insert(name.to_string(), ctor_names);
        // Retain the full declaration so an exactly-identical re-declaration is
        // adopted as a no-op above (removed on scope pop alongside `datatypes`).
        self.monomorphic_datatype_decs
            .insert(name.to_string(), datatype_dec.clone());

        // Track datatype and its sort in current scope for push/pop.
        self.track_scoped_datatype(name.to_string());
        self.track_scoped_sort_def(name.to_string());

        // Register constructors, selectors, and testers. The fallible sort
        // elaboration completed above, so the state-changing phase is atomic.
        self.register_elaborated_datatype_constructors(
            name,
            &sort,
            &datatype_dec.constructors,
            &selector_sorts,
            None,
        );
        Ok(())
    }

    /// Declare multiple (possibly mutually recursive) datatypes
    ///
    /// For mutually recursive datatypes, all sort names are registered first
    /// so that constructor/selector sorts can reference each other.
    ///
    /// Parametric `(par (T..) ..)` declarations (sort arity `> 0`) are stored as
    /// templates and lazily monomorphized at each ground use; the eager passes
    /// below only register the monomorphic (arity-0) members of the group.
    pub(crate) fn declare_datatypes(
        &mut self,
        sort_decs: &[command::SortDec],
        datatype_decs: &[command::DatatypeDec],
    ) -> Result<()> {
        if sort_decs.len() != datatype_decs.len() {
            return Err(ElaborateError::Unsupported(format!(
                "declare-datatypes has {} sort declaration(s) but {} datatype declaration(s)",
                sort_decs.len(),
                datatype_decs.len()
            )));
        }

        // Validate all names before making any changes
        let mut group_sort_names: HashSet<String> = HashSet::default();
        for sort_dec in sort_decs {
            if is_reserved_symbol(&sort_dec.name) {
                return Err(ElaborateError::ReservedSymbol(sort_dec.name.clone()));
            }
            if !group_sort_names.insert(sort_dec.name.clone()) {
                return Err(ElaborateError::SortRedeclaration(sort_dec.name.clone()));
            }
            // Reject re-declaring an existing sort name (#reserved-ops
            // reverse gate). Checked against the PRE-EXISTING state for every
            // group member before the group registers its own sorts below, so
            // mutually recursive groups do not self-collide.
            self.check_datatype_sort_redeclaration(&sort_dec.name)?;
        }
        for (sort_dec, datatype_dec) in sort_decs.iter().zip(datatype_decs) {
            Self::validate_datatype_names(None, datatype_dec)?;
            if sort_dec.arity == 0 && !datatype_dec.type_params.is_empty() {
                return Err(ElaborateError::Unsupported(format!(
                    "datatype '{}' declares type parameters but arity 0",
                    sort_dec.name
                )));
            }
            if sort_dec.arity != 0 && datatype_dec.type_params.len() != sort_dec.arity as usize {
                return Err(ElaborateError::Unsupported(format!(
                    "datatype '{}' has arity {} but {} type parameter(s)",
                    sort_dec.name,
                    sort_dec.arity,
                    datatype_dec.type_params.len()
                )));
            }
        }

        // Validate every monomorphic field sort against a narrow scratch
        // context containing the whole mutually-recursive group. This catches
        // all user errors before the live context changes, including references
        // to a parametric datatype declared by the same group.
        let empty: HashMap<String, Sort> = HashMap::default();
        let mut preflight = self.datatype_sort_preflight_context();
        for (sort_dec, datatype_dec) in sort_decs.iter().zip(datatype_decs) {
            if sort_dec.arity == 0 {
                preflight.sort_defs.insert(
                    sort_dec.name.clone(),
                    Sort::Uninterpreted(sort_dec.name.clone()),
                );
            } else {
                preflight
                    .parametric_datatypes
                    .insert(sort_dec.name.clone(), datatype_dec.clone());
            }
        }
        for (sort_dec, datatype_dec) in sort_decs.iter().zip(datatype_decs) {
            if sort_dec.arity == 0 {
                preflight.elaborate_datatype_selector_sorts(&datatype_dec.constructors, &empty)?;
            }
        }

        // Parametric templates must be visible while the live context
        // elaborates monomorphic members that reference them. Preflight above
        // guarantees this phase cannot fail for user-controlled input.
        let parametric_names: Vec<String> = sort_decs
            .iter()
            .filter(|sort_dec| sort_dec.arity != 0)
            .map(|sort_dec| sort_dec.name.clone())
            .collect();
        let scoped_parametric_count = self
            .scopes
            .last()
            .map_or(0, |frame| frame.parametric_datatypes.len());
        for (sort_dec, datatype_dec) in sort_decs.iter().zip(datatype_decs) {
            if sort_dec.arity != 0 {
                self.parametric_datatypes
                    .insert(sort_dec.name.clone(), datatype_dec.clone());
                self.track_scoped_parametric(sort_dec.name.clone());
            }
        }
        // Every MONOMORPHIC member's carrier sort must be in the signature
        // before any field sort is elaborated: the whole point of a
        // `declare-datatypes` GROUP is that its members may reference each
        // other (SMT-LIB 2.6 §4.2.3 mutual recursion). This used to work only
        // because an unresolved sort name silently became a fresh uninterpreted
        // sort. The names are tracked for `pop` in the same place as before;
        // the error path below removes them again, and the preflight above has
        // already validated these same field sorts.
        let mut registered_sorts: Vec<&str> = Vec::new();
        for sort_dec in sort_decs {
            if sort_dec.arity == 0 {
                let sort = Sort::Uninterpreted(sort_dec.name.clone());
                if self.sort_defs.insert(sort_dec.name.clone(), sort).is_none() {
                    registered_sorts.push(sort_dec.name.as_str());
                }
            }
        }
        let selector_sorts = sort_decs
            .iter()
            .zip(datatype_decs)
            .map(|(sort_dec, datatype_dec)| {
                if sort_dec.arity == 0 {
                    self.elaborate_datatype_selector_sorts(&datatype_dec.constructors, &empty)
                } else {
                    Ok(Vec::new())
                }
            })
            .collect::<Result<Vec<_>>>();
        let selector_sorts = match selector_sorts {
            Ok(selector_sorts) => selector_sorts,
            Err(error) => {
                // The scratch context above should make this branch reachable
                // only if live sort metadata changed unexpectedly. Still fail
                // closed and remove every group template rather than exposing a
                // partially declared group.
                for name in &parametric_names {
                    self.parametric_datatypes.remove(name);
                }
                for name in &registered_sorts {
                    self.sort_defs.remove(*name);
                }
                if let Some(frame) = self.scopes.last_mut() {
                    frame.parametric_datatypes.truncate(scoped_parametric_count);
                }
                return Err(error);
            }
        };

        // First pass: register all sort names. Parametric members (arity > 0)
        // are stored as templates; monomorphic members (arity 0) get a concrete
        // uninterpreted sort so the second pass can reference them.
        for sort_dec in sort_decs {
            if sort_dec.arity == 0 {
                let sort = Sort::Uninterpreted(sort_dec.name.clone());
                self.sort_defs.insert(sort_dec.name.clone(), sort);
                self.track_scoped_sort_def(sort_dec.name.clone());
            }
        }

        // Second pass: register constructors/selectors/testers for the
        // monomorphic members only.
        for ((sort_dec, datatype_dec), selector_sorts) in sort_decs
            .iter()
            .zip(datatype_decs)
            .zip(selector_sorts.iter())
        {
            if sort_dec.arity != 0 {
                continue;
            }
            let sort = Sort::Uninterpreted(sort_dec.name.clone());

            // Collect constructor names for datatype lookup
            let ctor_names: Vec<String> = datatype_dec
                .constructors
                .iter()
                .map(|c| c.name.clone())
                .collect();
            self.datatypes.insert(sort_dec.name.clone(), ctor_names);
            self.track_scoped_datatype(sort_dec.name.clone());

            self.register_elaborated_datatype_constructors(
                &sort_dec.name,
                &sort,
                &datatype_dec.constructors,
                selector_sorts,
                None,
            );
        }

        Ok(())
    }

    /// Whether `name` is a declared parametric datatype template.
    ///
    /// (Restored: this accessor from the original parametric-datatype work
    /// (c34b9d72ab) was dropped in the lazy-monomorphization rework merge
    /// while its test kept calling it, breaking the ay-frontend test-suite
    /// compile.)
    #[cfg(test)] // test-only accessor; cfg-gated so the lib build carries no dead code
    pub(crate) fn is_parametric_datatype(&self, name: &str) -> bool {
        self.parametric_datatypes.contains_key(name)
    }

    /// Lazily monomorphize a parametric datatype instance `(Name A1 .. An)`.
    ///
    /// Returns the instance sort `Sort::Uninterpreted(<mangled>)`. On first use
    /// the instance's constructors/selectors/testers are registered with the
    /// user-facing surface names (resolved by argument/result sort via the
    /// overload machinery) and the type-parameter-substituted field sorts. The
    /// instance sort name is registered BEFORE its fields are elaborated so a
    /// recursive self-reference like `(Lst T) -> Lst!{Int}` resolves to this
    /// in-progress instance instead of recursing forever (mirroring the
    /// register-sorts-first discipline of [`Context::declare_datatypes`]).
    pub(super) fn instantiate_parametric_datatype(
        &mut self,
        name: &str,
        args: &[Sort],
    ) -> Result<Sort> {
        let instance_name = mangle_datatype_instance(name, args);

        // Idempotent: a previously-registered instance just resolves to its sort.
        if self.datatypes.contains_key(&instance_name) {
            return Ok(Sort::Uninterpreted(instance_name));
        }

        let template = self
            .parametric_datatypes
            .get(name)
            .cloned()
            .ok_or_else(|| {
                ElaborateError::Unsupported(format!("'{name}' is not a parametric datatype"))
            })?;
        if template.type_params.len() != args.len() {
            return Err(ElaborateError::Unsupported(format!(
                "parametric datatype '{name}' expects {} type argument(s), got {}",
                template.type_params.len(),
                args.len()
            )));
        }

        let subst: HashMap<String, Sort> = template
            .type_params
            .iter()
            .cloned()
            .zip(args.iter().cloned())
            .collect();

        let instance_sort = Sort::Uninterpreted(instance_name.clone());

        // Register the instance sort + datatype metadata BEFORE elaborating its
        // own field sorts (recursive self-reference resolution).
        self.sort_defs
            .insert(instance_name.clone(), instance_sort.clone());
        // Store the INSTANCE-MANGLED constructor names so every consumer
        // (`datatype_iter`, the DT theory, finite-enum cardinality detection,
        // axiom generation) sees the same name-disjoint identity that the
        // constructor/selector metadata and the elaborated terms use. Storing
        // the surface names here would make those consumers look up
        // `constructor_selector_info("onone")` (mangled-keyed, hence missing) and
        // mis-classify a field-bearing instance as an all-nullary enum.
        let ctor_names: Vec<String> = template
            .constructors
            .iter()
            .map(|c| mangle_member(&c.name, Some(&instance_name)).unwrap_or_else(|| c.name.clone()))
            .collect();
        self.datatypes.insert(instance_name.clone(), ctor_names);
        self.parametric_instance_args
            .insert(instance_name.clone(), (name.to_string(), args.to_vec()));
        self.track_scoped_sort_def(instance_name.clone());
        self.track_scoped_datatype(instance_name.clone());

        self.register_datatype_constructors(
            &instance_name,
            &instance_sort,
            &template.constructors,
            &subst,
            Some(&instance_name),
        )?;

        Ok(instance_sort)
    }

    /// Ensure the parametric-datatype instance referenced by a BARE constructor
    /// application `name(arg_ids)` (no `(as ...)` ascription) is registered, by
    /// inferring its type arguments from the constructor's actual argument sorts.
    ///
    /// Lazy monomorphization is otherwise driven only by SORT references
    /// (`declare-const`, `as`, selector argument sorts, ...). A bare application
    /// like `(some true)` or `(mk 1 true)` never names the instance sort, so
    /// without this the instance would never be registered and the application
    /// would receive no injectivity/distinctness axioms — a soundness hole
    /// (false SAT for `(= (some true) (some false))`).
    ///
    /// For each parametric template that declares a constructor `name`, the
    /// template's field-sort patterns (which mention the type parameters) are
    /// unified against the actual argument sorts. If every type parameter is
    /// thereby determined, the instance is monomorphized (idempotently) so the
    /// existing overload resolver binds the application to it. Type parameters
    /// that NO argument determines (phantom parameters, e.g. nullary `none` of
    /// `(Opt T)`) cannot be inferred here; the application is left for an
    /// `(as ...)` ascription or a clean resolution error (never a guess).
    pub(crate) fn ensure_parametric_constructor_instance(
        &mut self,
        name: &str,
        arg_ids: &[ay_core::TermId],
    ) -> Result<()> {
        if self.parametric_datatypes.is_empty() {
            return Ok(());
        }
        let candidates: Vec<(String, command::DatatypeDec)> = self
            .parametric_datatypes
            .iter()
            .filter(|(_, dec)| dec.constructors.iter().any(|c| c.name == name))
            .map(|(dt, dec)| (dt.clone(), dec.clone()))
            .collect();
        if candidates.is_empty() {
            return Ok(());
        }

        let arg_sorts: Vec<Sort> = arg_ids
            .iter()
            .map(|&a| self.terms.sort(a).clone())
            .collect();

        for (dt_name, dec) in candidates {
            let Some(ctor) = dec.constructors.iter().find(|c| c.name == name) else {
                continue;
            };
            if ctor.selectors.len() != arg_sorts.len() {
                continue;
            }
            let mut bindings: HashMap<String, Sort> = HashMap::default();
            for (sel, arg_sort) in ctor.selectors.iter().zip(arg_sorts.iter()) {
                self.unify_template_sort(&sel.sort, arg_sort, &dec.type_params, &mut bindings);
            }
            // Instantiate only when EVERY type parameter is determined.
            let mut type_args = Vec::with_capacity(dec.type_params.len());
            let mut all_determined = true;
            for tp in &dec.type_params {
                match bindings.get(tp) {
                    Some(s) => type_args.push(s.clone()),
                    None => {
                        all_determined = false;
                        break;
                    }
                }
            }
            if all_determined {
                self.instantiate_parametric_datatype(&dt_name, &type_args)?;
            }
        }
        Ok(())
    }

    /// Unify a template field sort `template` (which may mention the type
    /// parameters in `type_params`) against the concrete argument sort `actual`,
    /// recording any type-parameter bindings into `bindings` (first binding
    /// wins; a later inconsistent argument is simply ignored, leaving the
    /// overload resolver to reject a genuinely ill-typed application).
    fn unify_template_sort(
        &self,
        template: &command::Sort,
        actual: &Sort,
        type_params: &[String],
        bindings: &mut HashMap<String, Sort>,
    ) {
        match template {
            command::Sort::Simple(p) => {
                if type_params.iter().any(|tp| tp == p) {
                    bindings.entry(p.clone()).or_insert_with(|| actual.clone());
                }
            }
            command::Sort::Parameterized(n, params) => match (n.as_str(), params.as_slice()) {
                ("Array", [i, e]) => {
                    if let Sort::Array(arr) = actual {
                        self.unify_template_sort(i, &arr.index_sort, type_params, bindings);
                        self.unify_template_sort(e, &arr.element_sort, type_params, bindings);
                    }
                }
                ("Seq", [el]) => {
                    if let Sort::Seq(inner) = actual {
                        self.unify_template_sort(el, inner, type_params, bindings);
                    }
                }
                _ => {
                    // A nested parametric-datatype instance: recover its type
                    // arguments from the mangled instance name and recurse.
                    if let Sort::Uninterpreted(mangled) = actual {
                        if let Some((inst_dt, inst_args)) =
                            self.parametric_instance_args.get(mangled).cloned()
                        {
                            if inst_dt == *n && inst_args.len() == params.len() {
                                for (p, a) in params.iter().zip(inst_args.iter()) {
                                    self.unify_template_sort(p, a, type_params, bindings);
                                }
                            }
                        }
                    }
                }
            },
            // Indexed sorts (BitVec/FloatingPoint) are concrete: no parameters.
            command::Sort::Indexed(_, _) => {}
        }
    }
}
