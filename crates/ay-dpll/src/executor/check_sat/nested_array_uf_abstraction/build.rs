// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Building `alpha(phi)`: sort classification, the renaming witness and the
//! raw-constructor rebuild of the original DAG.
//!
//! #nested-array-checked-rung: a DECLARED datatype carrier that reaches an
//! array (`Row` with an array field, `(Array I Row)` being the nested shape the
//! quarantine arms on) is renamed like an array sort, and its constructors and
//! selectors like `select`/`store`: each is a function of its argument values,
//! so the induced structure interprets the fresh symbol as that very function.

use super::*;
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Sort, Symbol};

/// Array operations the abstraction renames to fresh uninterpreted functions.
///
/// Each one denotes a function of its argument VALUES (`select`: array x index
/// -> element, `store`: array x index x element -> array, `const-array`:
/// element -> array), which is what lets the induced structure `M'` interpret
/// the fresh symbol as that very function. Anything else that touches an array
/// sort declines.
pub(super) const RENAMED_ARRAY_OPS: &[&str] = &["select", "store", "const-array"];

/// Equality predicates kept at CHANGED argument sorts. They mean the same thing
/// in every structure: identity (or pairwise non-identity) on the carrier, and
/// the fresh sort's carrier IS the array carrier. Keeping them is what gives
/// the abstraction its congruence power.
const KEPT_EQUALITY_PREDICATES: &[&str] = &["=", "distinct"];

/// Cap on distinct original nodes. The walk is linear in the DAG; past this
/// the rung declines before interning anything more.
pub(super) const MAX_ABSTRACTION_NODES: usize = 200_000;

/// Recursion cap for the fresh-sort mention walk. A datatype sort carries its
/// field sorts inline, so a deep one could otherwise recurse without bound;
/// hitting the cap declines.
const MAX_SORT_DEPTH: u32 = 64;

/// Fresh-name purposes. `mk_internal_symbol` spells `__ay_<purpose>!<counter>`
/// and the frontend rejects every `__ay_` source symbol.
const FRESH_SORT_PURPOSE: &str = "a2uf_sort";
const FRESH_FUNCTION_PURPOSE: &str = "a2uf_fn";
const FRESH_CONSTANT_PREFIX: &str = "__ay_a2uf_c";

/// Is `name` a function name this rung's mint spells (`__ay_a2uf_fn!<n>`)?
///
/// The renaming check needs every fresh FUNCTION to be uninterpreted, and
/// absence from the original DAG does not give that: `=`, `distinct`, a theory
/// operator or a datatype constructor the original never applies is absent
/// too, yet the solver interprets it. No source symbol can carry the `__ay_`
/// prefix (the frontend reserves it) and nothing else mints under this
/// purpose, so a minted name is uninterpreted everywhere. Sorts and constants
/// need no such test: an uninterpreted sort and a `Var` are uninterpreted by
/// construction.
pub(super) fn is_minted_function_name(name: &str) -> bool {
    name.strip_prefix("__ay_")
        .and_then(|rest| rest.strip_prefix(FRESH_FUNCTION_PURPOSE))
        .is_some_and(|counter| counter.starts_with('!'))
}

/// A typed symbol occurrence: the head plus its full original signature.
/// Keying on the signature makes the fresh-symbol map a function on TYPED
/// symbols; one head at two signatures gets two fresh symbols.
pub(super) type SymbolKey = (Symbol, Sort, Vec<Sort>);

/// How the abstraction treats one sort.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum SortClass {
    /// Reaches no array: mapped to itself.
    Plain,
    /// An array sort at the top: mapped to one fresh uninterpreted sort.
    Array,
    /// A DECLARED datatype carrier (registered field table) that reaches an
    /// array: mapped to one fresh uninterpreted sort, its constructors and
    /// selectors renamed (#nested-array-checked-rung).
    Carrier,
    /// Reaches an array below any other non-array constructor
    /// (`(Seq (Array ..))`, an inline datatype). There is no renaming for the
    /// container's operations, so it declines.
    Unsupported,
}

/// Classify `sort` for the abstraction.
///
/// "Reaches an array" is `StaticFeatures::sort_reaches_array`, the walk the
/// quarantine arms by, so the rung and the quarantine cannot disagree about
/// what a sort contains. It resolves `declare-datatype` carriers, which reach
/// the store as bare `Sort::Uninterpreted` identities, through the store's
/// registered field sorts: without that, a record with an array field would
/// read as plain and be KEPT, leaving an array inside the "array-free"
/// abstraction (#nested-array-quarantine-datatype-fields). Such a carrier is
/// renamed as a whole instead (#nested-array-checked-rung).
pub(super) fn classify_sort(terms: &TermStore, sort: &Sort) -> SortClass {
    match sort {
        Sort::Array(_) => SortClass::Array,
        _ if !StaticFeatures::sort_reaches_array(terms, sort) => SortClass::Plain,
        Sort::Uninterpreted(name) if terms.datatype_field_sorts(name).is_some() => {
            SortClass::Carrier
        }
        _ => SortClass::Unsupported,
    }
}

impl SortClass {
    /// Whether the abstraction maps the sort to a fresh uninterpreted sort.
    pub(super) fn is_renamed(self) -> bool {
        matches!(self, Self::Array | Self::Carrier)
    }
}

/// Does `sort` mention one of `names` as an uninterpreted sort anywhere?
/// `None` (too deep) is treated by callers as "yes".
pub(super) fn sort_mentions_uninterpreted(
    sort: &Sort,
    names: &HashSet<&str>,
    depth: u32,
) -> Option<bool> {
    if depth > MAX_SORT_DEPTH {
        return None;
    }
    Some(match sort {
        Sort::Uninterpreted(name) => names.contains(name.as_str()),
        Sort::Array(array) => {
            sort_mentions_uninterpreted(&array.index_sort, names, depth + 1)?
                || sort_mentions_uninterpreted(&array.element_sort, names, depth + 1)?
        }
        Sort::Seq(element) => sort_mentions_uninterpreted(element, names, depth + 1)?,
        Sort::Datatype(datatype) => {
            for constructor in &datatype.constructors {
                for field in &constructor.fields {
                    if sort_mentions_uninterpreted(&field.sort, names, depth + 1)? {
                        return Some(true);
                    }
                }
            }
            false
        }
        _ => false,
    })
}

/// The fresh identities one abstraction attempt minted.
///
/// Only the three maps are stored; every property the soundness argument
/// needs (injectivity, freshness, shape) is re-derived from them by
/// [`is_pure_renaming`], never cached.
#[derive(Debug, Default)]
pub(super) struct RenamingWitness {
    /// original array sort -> fresh uninterpreted sort
    pub(super) sorts: HashMap<Sort, Sort>,
    /// original typed array operation -> fresh uninterpreted function symbol
    pub(super) symbols: HashMap<SymbolKey, Symbol>,
    /// original array-sorted constant (`Var` node) -> fresh constant node
    pub(super) vars: HashMap<TermId, TermId>,
    /// Original binary `=` nodes whose image lists its two arguments in the
    /// other order: the TermId order `mk_eq` interns, which is the only
    /// orientation the solver's equality-atom lookups find
    /// (#nested-array-checked-rung). Equality is symmetric in every
    /// structure, so the swap changes no meaning; the checker admits it on
    /// binary `=` only and pairs the children crosswise.
    pub(super) swapped: HashSet<TermId>,
}

impl RenamingWitness {
    /// `sigma(sort)` without minting; `None` when the sort is unsupported or a
    /// renamed sort this witness never mapped.
    pub(super) fn mapped_sort(&self, terms: &TermStore, sort: &Sort) -> Option<Sort> {
        match classify_sort(terms, sort) {
            SortClass::Plain => Some(sort.clone()),
            SortClass::Array | SortClass::Carrier => self.sorts.get(sort).cloned(),
            SortClass::Unsupported => None,
        }
    }

    fn abstract_sort(&mut self, terms: &mut TermStore, sort: &Sort) -> Option<Sort> {
        match classify_sort(terms, sort) {
            SortClass::Plain => Some(sort.clone()),
            SortClass::Unsupported => None,
            SortClass::Array | SortClass::Carrier => {
                if let Some(fresh) = self.sorts.get(sort) {
                    return Some(fresh.clone());
                }
                let fresh = Sort::Uninterpreted(terms.mk_internal_symbol(FRESH_SORT_PURPOSE));
                self.sorts.insert(sort.clone(), fresh.clone());
                Some(fresh)
            }
        }
    }

    fn function(&mut self, terms: &mut TermStore, key: SymbolKey) -> Symbol {
        if let Some(fresh) = self.symbols.get(&key) {
            return fresh.clone();
        }
        let fresh = Symbol::named(terms.mk_internal_symbol(FRESH_FUNCTION_PURPOSE));
        self.symbols.insert(key, fresh.clone());
        fresh
    }
}

/// `alpha(roots)`, interned in the live term store, with its witness.
#[derive(Debug)]
pub(super) struct ArrayUfAbstraction {
    pub(super) roots: Box<[TermId]>,
    pub(super) witness: RenamingWitness,
}

impl ArrayUfAbstraction {
    /// Build `alpha(roots)` inside `terms`, or decline.
    ///
    /// Every node is rebuilt with a RAW constructor (`mk_app`, `mk_not_raw`,
    /// `mk_ite_raw`, ...): a folding constructor would change the SHAPE of the
    /// abstract DAG, which the lockstep check cannot tell apart from a rewrite
    /// bug and would therefore reject.
    pub(super) fn build(terms: &mut TermStore, roots: &[TermId]) -> Option<Self> {
        let mut witness = RenamingWitness::default();
        let mut memo: HashMap<TermId, TermId> = HashMap::default();
        let mut stack: Vec<(TermId, bool)> = Vec::new();
        for &root in roots {
            stack.push((root, false));
            while let Some((node, children_done)) = stack.pop() {
                if memo.contains_key(&node) {
                    continue;
                }
                if !children_done {
                    stack.push((node, true));
                    push_children(terms, node, &mut stack)?;
                    continue;
                }
                if memo.len() >= MAX_ABSTRACTION_NODES {
                    return None;
                }
                let image = abstract_node(terms, node, &memo, &mut witness)?;
                memo.insert(node, image);
            }
        }
        let abstract_roots = roots
            .iter()
            .map(|root| memo.get(root).copied())
            .collect::<Option<Vec<TermId>>>()?;
        Some(Self {
            roots: abstract_roots.into_boxed_slice(),
            witness,
        })
    }

    pub(super) fn roots(&self) -> &[TermId] {
        &self.roots
    }
}

fn push_children(terms: &TermStore, node: TermId, stack: &mut Vec<(TermId, bool)>) -> Option<()> {
    match terms.get(node) {
        TermData::Const(_) | TermData::Var(_, _) => {}
        TermData::App(_, args) => stack.extend(args.iter().map(|&arg| (arg, false))),
        TermData::Not(inner) => stack.push((*inner, false)),
        TermData::Ite(cond, then_term, else_term) => {
            stack.extend([(*cond, false), (*then_term, false), (*else_term, false)]);
        }
        TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
            stack.push((*body, false));
            stack.extend(triggers.iter().flatten().map(|&trigger| (trigger, false)));
        }
        // `Let` binds names through a mechanism the lockstep check does not
        // model, and `TermData` is non-exhaustive: decline both.
        _ => return None,
    }
    Some(())
}

/// Rebuild ONE node over its already-abstracted children, or decline.
fn abstract_node(
    terms: &mut TermStore,
    node: TermId,
    memo: &HashMap<TermId, TermId>,
    witness: &mut RenamingWitness,
) -> Option<TermId> {
    let original_sort = terms.sort(node).clone();
    let image_sort = witness.abstract_sort(terms, &original_sort)?;
    let child = |term: &TermId| memo.get(term).copied();
    match terms.get(node).clone() {
        TermData::Const(_) => (image_sort == original_sort).then_some(node),
        TermData::Var(_, _) => {
            if image_sort == original_sort {
                return Some(node);
            }
            let fresh = terms.mk_fresh_var(FRESH_CONSTANT_PREFIX, image_sort);
            witness.vars.insert(node, fresh);
            Some(fresh)
        }
        TermData::App(symbol, args) => {
            let image_args = args.iter().map(child).collect::<Option<Vec<TermId>>>()?;
            let arg_sorts = args
                .iter()
                .map(|&arg| terms.sort(arg).clone())
                .collect::<Vec<Sort>>();
            let head = match app_head_class(terms, &symbol, &original_sort, &arg_sorts)? {
                HeadClass::Kept => symbol,
                HeadClass::Renamed => witness.function(terms, (symbol, original_sort, arg_sorts)),
            };
            let mut image_args = image_args;
            if is_binary_equality(&head, &image_args, &image_sort) && image_args[0] > image_args[1]
            {
                image_args.swap(0, 1);
                witness.swapped.insert(node);
            }
            Some(terms.mk_app(head, &image_args, image_sort))
        }
        TermData::Not(inner) => Some(terms.mk_not_raw(child(&inner)?)),
        TermData::Ite(cond, then_term, else_term) => {
            let (cond, then_term, else_term) =
                (child(&cond)?, child(&then_term)?, child(&else_term)?);
            (terms.sort(then_term) == terms.sort(else_term))
                .then(|| terms.mk_ite_raw(cond, then_term, else_term))
        }
        TermData::Forall(vars, body, triggers) => {
            if !binders_are_array_free(terms, &vars) {
                return None;
            }
            let (body, triggers) = (child(&body)?, abstract_triggers(&triggers, memo)?);
            Some(terms.mk_forall_with_triggers(vars, body, triggers))
        }
        TermData::Exists(vars, body, triggers) => {
            if !binders_are_array_free(terms, &vars) {
                return None;
            }
            let (body, triggers) = (child(&body)?, abstract_triggers(&triggers, memo)?);
            Some(terms.mk_exists_with_triggers(vars, body, triggers))
        }
        _ => None,
    }
}

/// A binary `=` application: the one head whose image may list its arguments
/// in the other order (see [`RenamingWitness::swapped`]).
pub(super) fn is_binary_equality(head: &Symbol, args: &[TermId], sort: &Sort) -> bool {
    matches!(head, Symbol::Named(name) if name == "=") && args.len() == 2 && *sort == Sort::Bool
}

fn abstract_triggers(
    triggers: &[Vec<TermId>],
    memo: &HashMap<TermId, TermId>,
) -> Option<Vec<Vec<TermId>>> {
    triggers
        .iter()
        .map(|group| group.iter().map(|term| memo.get(term).copied()).collect())
        .collect()
}

pub(super) fn binders_are_array_free(terms: &TermStore, vars: &[(String, Sort)]) -> bool {
    vars.iter()
        .all(|(_, sort)| classify_sort(terms, sort) == SortClass::Plain)
}

/// What the abstraction does with an application head.
pub(super) enum HeadClass {
    /// Same symbol in the abstract problem.
    Kept,
    /// A fresh uninterpreted function for this typed occurrence.
    Renamed,
}

/// Classify one application head by its ORIGINAL signature, or decline.
///
/// Shared by the builder and the checker so the two cannot disagree about which
/// heads may be renamed; the checker still verifies the renaming itself.
pub(super) fn app_head_class(
    terms: &TermStore,
    symbol: &Symbol,
    result_sort: &Sort,
    arg_sorts: &[Sort],
) -> Option<HeadClass> {
    let classes = std::iter::once(result_sort)
        .chain(arg_sorts)
        .map(|sort| classify_sort(terms, sort))
        .collect::<Vec<SortClass>>();
    if classes.contains(&SortClass::Unsupported) {
        return None;
    }
    let touches_renamed = classes.iter().any(|class| class.is_renamed());
    let name = symbol.name();
    if KEPT_EQUALITY_PREDICATES.contains(&name) {
        return (*result_sort == Sort::Bool).then_some(HeadClass::Kept);
    }
    let named = matches!(symbol, Symbol::Named(_));
    let array_op = named && RENAMED_ARRAY_OPS.contains(&name);
    match (touches_renamed, array_op) {
        (true, true) => Some(HeadClass::Renamed),
        (true, false) if named && is_carrier_datatype_op(terms, name, &classes) => {
            Some(HeadClass::Renamed)
        }
        (false, false) => Some(HeadClass::Kept),
        // A head touching a renamed sort that is not a known value function (a
        // binder such as `lambda-array`, `default`, `(_ map f)`, set
        // operations, a tester, a user function over arrays or carriers), or
        // an array operation at array-free sorts: no renaming argument covers
        // it.
        _ => None,
    }
}

/// A constructor of a renamed carrier (`classes[0]`, the result, is
/// `Carrier` and the store registers `name` with one field per argument), or
/// a selector of one (its one argument is a `Carrier` and the store registers
/// `name` as a field). Both are functions of their argument values. The shape
/// test is what keeps a head that merely SHARES a field's name out.
fn is_carrier_datatype_op(terms: &TermStore, name: &str, classes: &[SortClass]) -> bool {
    let Some((result, args)) = classes.split_first() else {
        return false;
    };
    let constructor = *result == SortClass::Carrier
        && terms
            .constructor_field_names(name)
            .is_some_and(|fields| fields.len() == args.len());
    let selector = args == [SortClass::Carrier] && terms.name_is_registered_selector(name);
    constructor || selector
}
