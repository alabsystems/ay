// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Construction provenance: which terms are stored exactly as the caller built
//! them.
//!
//! z3 keeps the AST its caller builds; AY's constructors rewrite (`Not(Not p)`
//! is stored as `p`, `x > y` as `y < x`,
//! `Implies(p, q)` as `Or(Not p, q)`). Every rewrite is an equivalence, so a
//! solver verdict is unaffected, but the two STRUCTURAL operations of the API,
//! `Z3_substitute` (match subterms by identity) and `Z3_update_term` (keep the
//! operator, swap the children), read the structure itself: run on a rewritten
//! term they silently return a different formula from z3's.
//!
//! Until the FFI keeps the AST the caller built (critic plan rank 11), these
//! two entry points only act where AY's term provably IS the caller's term,
//! and fail closed elsewhere. The evidence is recorded at construction:
//!
//! * Every `Z3_mk_*` that returns an AST runs under [`super::ffi_guard_mk`],
//!   which logs the argument terms the entry decodes. A result whose children
//!   are exactly those arguments, in order, is a FAITHFUL construction and is
//!   recorded with its entry's name. Anything else (a fold to an argument or
//!   to a literal, reordered or flattened arguments, a different operator
//!   tree) marks the result AMBIGUOUS: from then on that handle may stand for
//!   a term z3 holds with a different structure.
//! * The same compound node (term and public sort) built faithfully by two
//!   different entries is ambiguous too (two z3 operators AY stores alike).
//! * Terms returned by rewriting producers (`Z3_simplify`, `Z3_substitute`,
//!   the SMT-LIB parsers, model evaluation) are marked ambiguous: z3's own
//!   answer has whatever structure ITS rewriter gives.
//!
//! The evidence is kept per public node (T5 P1: a `Z3_ast` names a node, and
//! one engine term may carry several, one per public sort). A rewriting
//! producer's term is ambiguous as a term: every node over it is.
//!
//! A node is CLEAN when it was built faithfully and is not ambiguous; an
//! engine term is clean when it has exactly one node and that node is clean.
//! Two substitution regimes are then exact:
//!
//! 1. Every pattern is a clean uninterpreted constant (`Z3_mk_const`,
//!    `Z3_mk_fresh_const`). Replacing a free constant commutes with every
//!    equivalence-preserving rewrite, so AY's result is equivalent to z3's
//!    whatever the target's structure.
//! 2. The target and every pattern are clean all the way down. Then AY's
//!    stored DAG is the DAG the caller built, and matching by identity finds
//!    exactly z3's occurrences.
//!
//! Both regimes match by engine term, so neither applies to a pattern whose
//! engine term stands for several public objects (T5 P1: the finite-domain
//! value 3 and the integer 3, a `Char` and its code point are two ASTs over
//! one term). Every occurrence of each would be replaced where z3 replaces
//! one (libz3 5.1.0: substituting `3 -> y` in `And(f(FD 3), g(3))` gives
//! `And(f(3), g(y))`).
//!
//! Everything else is refused with an error rather than answered.

use std::collections::{HashMap, HashSet};

use ay_dpll::api::{Term, TermKind};

use super::pub_ast::PubId;
use super::{PubTerm, Z3Context};

/// Entries whose result is a fresh uninterpreted constant (regime 1).
const CONSTANT_ENTRIES: &[&str] = &["Z3_mk_const", "Z3_mk_fresh_const"];

/// The argument log of the outermost `Z3_mk_*` call in progress.
struct MkScope {
    entry: &'static str,
    decoded: Vec<Term>,
}

/// How a [`Provenance::begin`] call nested.
pub(crate) enum MkToken {
    /// The outermost `Z3_mk_*` of this API call: its result is recorded.
    Outer,
    /// A `Z3_mk_*` called from inside another entry: not recorded (its result
    /// is not what the caller asked for), and the outer log is restored.
    Nested(Option<MkScopeBox>),
}

/// Opaque saved outer scope.
pub(crate) struct MkScopeBox(MkScope);

/// Per-context construction provenance (see the module docs).
#[derive(Default)]
pub(crate) struct Provenance {
    depth: u32,
    scope: Option<MkScope>,
    /// Clean candidates: nodes built faithfully, with the entry that built
    /// them.
    built: HashMap<PubId, &'static str>,
    /// Nodes that may stand for a differently structured z3 term.
    ambiguous: HashSet<PubId>,
    /// Engine terms every node over which (minted already or later) may stand
    /// for a differently structured z3 term: a rewriting producer's results.
    ambiguous_terms: HashSet<Term>,
    /// Evidence was lost (a panic while recording): refuse every structural
    /// operation in this context from now on.
    poisoned: bool,
}

impl Provenance {
    /// A length mismatch never walks child data. Otherwise the borrowed
    /// matcher visits each child once; include its constant header lookup.
    pub(crate) fn arithmetic_comparison_work(&self, children: usize) -> Option<usize> {
        match self.scope.as_ref() {
            Some(scope) if scope.decoded.len() == children => children.checked_add(1),
            _ => Some(1),
        }
    }
    /// Prepay the actual constructor metadata before argument decoding and
    /// before the existing end_mk borrowed comparison/table insertion. The caller keeps
    /// the SAME operation alive through that finish, including its callbacks.
    pub(crate) fn prepare_arithmetic_owned(
        &mut self,
        arguments: usize,
        owner: &dyn ay_core::term::TermConstructionAdmission,
    ) -> Result<(), &'static str> {
        if let Some(scope) = self.scope.as_mut() {
            ay_core::term::reserve_counted(&mut scope.decoded, arguments, owner)
                .map_err(|_| "constructor provenance stopped")?;
        }
        owner
            .admit(arguments, 0)
            .map_err(|_| "constructor child admission stopped")?;
        // Reuse mark_ambiguous_owned's conservative native-table replacement
        // envelope: old/new buckets, controls and rehash copies. These are
        // charged scratch bytes, not a new allowance or live-memory claim.
        for (length, capacity, entry) in [
            (
                self.built.len(),
                self.built.capacity(),
                std::mem::size_of::<(PubId, &'static str)>(),
            ),
            (
                self.ambiguous.len(),
                self.ambiguous.capacity(),
                std::mem::size_of::<PubId>(),
            ),
        ] {
            if length == capacity {
                let bytes = capacity
                    .checked_mul(entry)
                    .and_then(|n| n.checked_mul(4))
                    .and_then(|n| n.checked_add(4096))
                    .ok_or("constructor table size overflow")?;
                owner
                    .admit(
                        length
                            .checked_add(1)
                            .ok_or("constructor table work overflow")?,
                        bytes,
                    )
                    .map_err(|_| "constructor table admission stopped")?;
            }
        }
        self.built
            .try_reserve(1)
            .map_err(|_| "constructor table allocation failed")?;
        self.ambiguous
            .try_reserve(1)
            .map_err(|_| "constructor table allocation failed")?;
        owner.check().map_err(|_| "constructor provenance stopped")
    }
    /// Enter a `Z3_mk_*` entry.
    pub(crate) fn begin(&mut self, entry: &'static str) -> MkToken {
        self.depth += 1;
        if self.depth == 1 {
            self.scope = Some(MkScope {
                entry,
                decoded: Vec::new(),
            });
            MkToken::Outer
        } else {
            MkToken::Nested(self.scope.take().map(MkScopeBox))
        }
    }

    /// Log one argument term decoded by the entry in progress.
    pub(crate) fn note_decoded(&mut self, term: Term) {
        if let Some(scope) = self.scope.as_mut() {
            scope.decoded.push(term);
        }
    }

    /// Mark a term as possibly standing for a differently structured z3
    /// term: every node over it, including nodes minted later.
    pub(crate) fn mark_ambiguous(&mut self, term: Term) {
        self.ambiguous_terms.insert(term);
    }

    pub(crate) fn mark_ambiguous_owned(
        &mut self,
        term: Term,
        owner: &dyn ay_core::term::TermConstructionAdmission,
    ) -> Result<(), &'static str> {
        loop {
            owner.admit(1, 0).map_err(|_| "provenance owner stopped")?;
            if self.ambiguous_terms.contains(&term) {
                return Ok(());
            }
            let snapshot = (self.ambiguous_terms.len(), self.ambiguous_terms.capacity());
            // Same native table replacement envelope used by PubStore's
            // owned publication: retained buckets/controls and rehash copies.
            let bytes = if snapshot.0 == snapshot.1 {
                snapshot
                    .1
                    .checked_mul(std::mem::size_of::<Term>())
                    .and_then(|n| n.checked_mul(4))
                    .and_then(|n| n.checked_add(4096))
                    .ok_or("provenance storage overflow")?
            } else {
                0
            };
            let work = if bytes == 0 {
                1
            } else {
                snapshot
                    .0
                    .checked_add(1)
                    .ok_or("provenance work overflow")?
            };
            owner
                .admit(work, bytes)
                .map_err(|_| "provenance admission refused")?;
            if snapshot != (self.ambiguous_terms.len(), self.ambiguous_terms.capacity()) {
                continue;
            }
            self.ambiguous_terms
                .try_reserve(1)
                .map_err(|_| "provenance allocation refused")?;
            self.ambiguous_terms.insert(term);
            owner.check().map_err(|_| "provenance owner stopped")?;
            return Ok(());
        }
    }

    /// Recording the result of a `Z3_mk_*` failed: drop the log and treat the
    /// result as ambiguous.
    pub(crate) fn abandon(&mut self, result: Option<Term>) {
        self.scope = None;
        if let Some(term) = result {
            self.mark_ambiguous(term);
        }
    }

    /// Recording failed in a way that may have lost an ambiguous term.
    pub(crate) fn taint_all(&mut self) {
        self.poisoned = true;
    }

    fn is_clean(&self, node: PubTerm) -> bool {
        !self.poisoned
            && self.built.contains_key(&node.id)
            && !self.ambiguous.contains(&node.id)
            && !self.ambiguous_terms.contains(&node.term)
    }

    /// The entry that built `node`, when it is clean.
    fn clean_entry(&self, node: PubTerm) -> Option<&'static str> {
        if self.is_clean(node) {
            self.built.get(&node.id).copied()
        } else {
            None
        }
    }

    /// Record `result`, rebuilt by `Z3_update_term` from the clean `source`
    /// with `args` as its children: clean under `source`'s entry when AY
    /// stored exactly that application, ambiguous otherwise.
    pub(crate) fn record_update(
        &mut self,
        source: PubTerm,
        args: &[Term],
        result: PubTerm,
        children: &[Term],
    ) {
        match self.built.get(&source.id).copied() {
            Some(entry) if children == args => self.record_faithful(entry, result.id, true),
            _ => {
                self.ambiguous.insert(result.id);
            }
        }
    }

    fn record_faithful(&mut self, entry: &'static str, node: PubId, compound: bool) {
        match self.built.get(&node) {
            None => {
                self.built.insert(node, entry);
            }
            // Two z3 operators AY stores as one node: no single structure.
            Some(&previous) if compound && previous != entry => {
                self.ambiguous.insert(node);
            }
            Some(_) => {}
        }
    }
}

/// Leave a `Z3_mk_*` entry entered with `token`, recording its result `ast`.
pub(crate) fn end_mk(ctx: &mut Z3Context, token: MkToken, ast: super::Z3_ast) {
    ctx.provenance.depth = ctx.provenance.depth.saturating_sub(1);
    match token {
        MkToken::Nested(saved) => ctx.provenance.scope = saved.map(|MkScopeBox(s)| s),
        MkToken::Outer => {
            let Some(scope) = ctx.provenance.scope.take() else {
                return;
            };
            if ast == 0 || ctx.last_error != super::Z3_OK {
                return;
            }
            let Some(result) = super::checked_ast_to_pub(ctx, ast) else {
                return;
            };
            let inspected = ctx
                .solver
                .try_term_children_match(result.term, &scope.decoded);
            if let Ok((children, true)) = inspected {
                ctx.provenance
                    .record_faithful(scope.entry, result.id, children != 0);
            } else {
                ctx.provenance.ambiguous.insert(result.id);
            }
        }
    }
}

/// A rewriting producer (`Z3_simplify`, a parser, a model, a goal, ...)
/// returned `term`: z3's counterpart has whatever structure z3's own producer
/// gives, so unless `term` is a literal (whose structure is its value in both
/// systems) it is ambiguous from now on.
pub(crate) fn mark_produced_term(ctx: &mut Z3Context, term: Term) {
    if !matches!(ctx.solver.term_kind(term), TermKind::Const) {
        ctx.provenance.mark_ambiguous(term);
    }
}

/// [`mark_produced_term`] for an AST handle (ignores null and non-terms).
pub(crate) fn mark_produced(ctx: &mut Z3Context, ast: super::Z3_ast) {
    if let Some(term) = super::checked_ast_to_pub(ctx, ast).map(|produced| produced.term) {
        mark_produced_term(ctx, term);
    }
}

/// Why a structural operation on a term is refused.
pub(crate) enum StructuralRefusal {
    /// The input term may not be the term the caller built.
    Input,
    /// `from[i]` may not be the term the caller built.
    Pattern(usize),
}

/// Whether `Z3_substitute(target, from -> _)` is exact (module docs, regimes 1
/// and 2).
pub(crate) fn check_substitution(
    ctx: &Z3Context,
    target: Term,
    from: &[Term],
) -> Result<(), StructuralRefusal> {
    if ctx.provenance.poisoned {
        return Err(StructuralRefusal::Input);
    }
    if let Some(index) = from
        .iter()
        .position(|&pattern| ctx.pub_ast.is_shared(pattern))
    {
        return Err(StructuralRefusal::Pattern(index));
    }
    let constant_pattern = |t: &Term| {
        sole_node(ctx, *t)
            .and_then(|node| ctx.provenance.clean_entry(node))
            .is_some_and(|entry| CONSTANT_ENTRIES.contains(&entry))
    };
    if from.iter().all(constant_pattern) {
        return Ok(());
    }
    for (index, &pattern) in from.iter().enumerate() {
        if !clean_dag(ctx, pattern) {
            return Err(StructuralRefusal::Pattern(index));
        }
    }
    if clean_dag(ctx, target) {
        Ok(())
    } else {
        Err(StructuralRefusal::Input)
    }
}

/// Whether `Z3_update_term(source, ..)` keeps z3's operator: the caller's
/// node `source` itself was built faithfully (its children need not be clean:
/// they are replaced).
pub(crate) fn check_update(ctx: &Z3Context, source: PubTerm) -> Result<(), StructuralRefusal> {
    if ctx.provenance.is_clean(source) {
        Ok(())
    } else {
        Err(StructuralRefusal::Input)
    }
}

/// Why substituting `from -> to` inside `target` cannot be done by name.
pub(crate) enum BinderRefusal {
    /// A `from` or `to` term mentions this variable, which `target` binds (a
    /// quantifier's bound variable or a lambda's slot).
    Bound(String),
    /// `target` contains a `let`, whose bound names the C API cannot read.
    Let,
}

/// The variable names `roots` bind (a quantifier's bound variables, a
/// lambda's slot), and whether they contain a `let`.
pub(crate) fn binder_names(ctx: &Z3Context, roots: &[Term]) -> (HashSet<String>, bool) {
    let mut names = HashSet::new();
    let mut has_let = false;
    let mut seen = HashSet::new();
    let mut stack = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        let children = ctx.solver.term_children(term);
        match ctx.solver.term_kind(term) {
            TermKind::Forall | TermKind::Exists => {
                if let Some(bound) = ctx.solver.quantifier_bound_vars(term) {
                    names.extend(bound.into_iter().map(|(name, _)| name));
                }
            }
            TermKind::App { name, .. } if name == LAMBDA_ARRAY => {
                if let Some(&slot) = children.first() {
                    if let TermKind::Var { name } = ctx.solver.term_kind(slot) {
                        names.insert(name);
                    }
                }
            }
            TermKind::Let => has_let = true,
            _ => {}
        }
        stack.extend(children);
    }
    (names, has_let)
}

/// Every variable name occurring in `roots`.
fn variable_names(ctx: &Z3Context, roots: &[Term]) -> HashSet<String> {
    let mut names = HashSet::new();
    let mut seen = HashSet::new();
    let mut stack = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermKind::Var { name } = ctx.solver.term_kind(term) {
            names.insert(name);
        }
        stack.extend(ctx.solver.term_children(term));
    }
    names
}

/// Whether `Z3_substitute(target, from -> to)` can be done by name (T5 design
/// §4 P0.2 Q3). AY binds variables by NAME, and its substitution walks
/// through binders without renaming, so a `from` that is (or mentions) a
/// binder of `target` would rewrite bound occurrences z3 leaves alone
/// (`substitute(And(ForAll x. x > 0, x > 3), x -> 5)` gave `ForAll x. True`;
/// z3: `And(ForAll x. x > 0, 5 > 3)`), and a `to` that mentions one would be
/// captured (`substitute(Exists x. x != z, z -> x)` gave an UNSAT formula;
/// z3: `Exists x'. x' != x`, sat). Both measured on libz3 5.1.0. A lambda's
/// slot is a binder too (`substitute(Lambda x. x + 1, x -> 3)` built
/// `lambda-array(3, 4)`). A `let` hides its bound names from the C API, so a
/// target with one is refused outright.
pub(crate) fn check_binders(
    ctx: &Z3Context,
    target: Term,
    from: &[Term],
    to: &[Term],
) -> Result<(), BinderRefusal> {
    let (bound, has_let) = binder_names(ctx, &[target]);
    if has_let {
        return Err(BinderRefusal::Let);
    }
    if bound.is_empty() {
        return Ok(());
    }
    let roots: Vec<Term> = from.iter().chain(to).copied().collect();
    let mut clash: Vec<String> = variable_names(ctx, &roots)
        .intersection(&bound)
        .cloned()
        .collect();
    clash.sort();
    match clash.into_iter().next() {
        Some(name) => Err(BinderRefusal::Bound(name)),
        None => Ok(()),
    }
}

/// The error text for a substitution `entry` refuses (`check_binders`).
pub(crate) fn binder_refusal_message(
    ctx: &Z3Context,
    entry: &str,
    refusal: BinderRefusal,
) -> String {
    let reason = match refusal {
        BinderRefusal::Bound(name) => format!(
            "a from/to term mentions {}, which the input binds (a quantified variable or a \
             lambda's parameter). AY binds variables by name, so substituting there would \
             rewrite bound occurrences or capture free ones",
            super::ffi_surface_text(ctx, &ay_core::quote_symbol(&name))
        ),
        BinderRefusal::Let => {
            "the input contains a let binding, whose bound names AY cannot check for capture"
                .to_string()
        }
    };
    format!("{entry}: {reason}; refusing rather than returning a formula z3 would not")
}

/// The core spelling of a lambda array (`TermStore::mk_lambda_array`): its
/// first child is the bound variable.
pub(crate) const LAMBDA_ARRAY: &str = "lambda-array";

/// The one public node over `term`; `None` when it has none or several (a
/// walk over engine terms cannot tell which of several a subterm is).
fn sole_node(ctx: &Z3Context, term: Term) -> Option<PubTerm> {
    if ctx.pub_ast.is_shared(term) {
        return None;
    }
    let id = ctx.pub_ast.latest(term)?;
    Some(PubTerm { id, term })
}

/// Every term of `root`'s DAG is clean: it has one public node, and that node
/// is clean.
fn clean_dag(ctx: &Z3Context, root: Term) -> bool {
    let mut seen = HashSet::new();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if !sole_node(ctx, term).is_some_and(|node| ctx.provenance.is_clean(node)) {
            return false;
        }
        stack.extend(ctx.solver.term_children(term));
    }
    true
}
