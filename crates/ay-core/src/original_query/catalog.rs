// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::syntax::*;

/// Function-like catalog role; constructors/selectors retain nominal owners.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TermRole {
    /// Ordinary uninterpreted/defined function or constant.
    Function,
    /// Globally declared schematic rule variable.
    RuleVariable,
    /// Fixedpoint relation.
    Relation,
    /// Nominal datatype constructor.
    Constructor(DeclId),
    /// Nominal datatype selector with owning constructor and field position.
    Selector {
        /// Owning nominal constructor declaration.
        constructor: DeclId,
        /// Zero-based field position in that constructor.
        field: u32,
    },
}

/// Definition recursion mode, not inferred from the body.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DefinitionKind {
    /// Ordinary non-recursive definition.
    NonRecursive,
    /// Recursive definition admitted by a recursive declaration group.
    Recursive,
}

/// Definition body and its definition-time parameter environment.
#[derive(Clone, Debug)]
pub struct Definition {
    /// Explicit recursion kind.
    pub kind: DefinitionKind,
    /// Ordered term parameters, introducing body-local binders.
    pub parameters: Vec<Binder>,
    /// Original body, including unused definitions.
    pub body: NodeId,
}

/// Complete nominal declaration, not a digest or an authority-bearing handle.
#[derive(Clone, Debug)]
pub struct Declaration {
    /// Original nominal name; NEVER eligible for alpha-renaming.
    pub name: SymbolToken,
    /// Original declaration shape, parameters, and body.
    pub kind: DeclarationKind,
}

/// Catalog entries retain sort aliases and datatype templates without expansion.
#[derive(Clone, Debug)]
pub enum DeclarationKind {
    /// Uninterpreted sort constructor.
    Sort {
        /// Number of sort arguments required by this constructor.
        arity: u32,
    },
    /// Globally declared sort parameter, distinct from a lexical type parameter.
    SortParameter,
    /// Parameterized sort alias with original body.
    SortAlias {
        /// Lexical type parameters in declaration order.
        parameters: Vec<TypeParameter>,
        /// Original alias body, without expansion.
        body: SortId,
    },
    /// Function/constant/relation/constructor/selector declaration or definition.
    Term {
        /// Nominal role, never inferred from spelling.
        role: TermRole,
        /// Lexical polymorphic parameters in declaration order.
        type_parameters: Vec<TypeParameter>,
        /// Original argument sorts in order.
        arguments: Vec<SortId>,
        /// Original result sort.
        result: SortId,
        /// Body and term parameters, including unused definitions.
        definition: Option<Definition>,
    },
    /// Parameterized datatype template with nominal constructor catalog links.
    Datatype {
        /// Type parameters local to the complete datatype template.
        parameters: Vec<TypeParameter>,
        /// Constructors in authored order, including all selector signatures.
        constructors: Vec<DeclId>,
    },
}

/// Explicit declaration-group visibility rule.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeclarationGroupKind {
    /// Sequential non-recursive declarations: no self or forward body references.
    Sequential,
    /// A single/mutual recursive function definition group.
    RecursiveFunctions,
    /// A single/mutual recursive datatype template group with constructors/selectors.
    MutualDatatypes,
}

/// Authored root role; assertions/assumptions are not collapsed or reordered.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RootKind {
    /// Hard assertion.
    Assert,
    /// Soft assertion, retaining weight/id as attributes.
    SoftAssert,
    /// Horn rule.
    Rule,
    /// Fixedpoint reachability query.
    Query,
    /// Synthesis constraint.
    Constraint,
    /// Minimize objective.
    Minimize,
    /// Maximize objective.
    Maximize,
}

/// Check operation; assumptions are an ordered occurrence list, not a set.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CheckKind {
    /// Ordinary satisfiability query.
    Sat,
    /// Satisfiability query with an authored assumption list.
    Assuming,
    /// Synthesis query.
    Synth,
}

/// Scope operation with separately retained authored numeral/default syntax.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScopeKind {
    /// Open assertion/declaration scopes.
    Push,
    /// Close scopes and remove their declaration visibility.
    Pop,
}

/// Declaration lifetime captured from the host and source option history.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum DeclarationLifetime {
    /// Declarations belong to their current scope.
    #[default]
    Scoped,
    /// New declarations survive subsequent pops.
    Global,
}

/// Explicit host policy for reset-assertions, part of structural identity.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ResetAssertionsPolicy {
    /// Strict SMT-LIB: retire every scope above the initial scope.
    #[default]
    PopScopes,
    /// Compatibility policy: keep public depth and all currently visible declarations.
    RetainDepthAndDeclarations,
    /// Bare non-strict frontend: clear materialized depth but retain declarations.
    /// Unlike the CLI compatibility host, this host does not reopen empty levels.
    ClearDepthRetainDeclarations,
}

/// Host lifetime behavior across full reset; not inferred from another reset policy.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ResetLifetimePolicy {
    /// Ordinary fresh SMT-LIB context restores the scoped declaration default.
    #[default]
    RestoreScopedDefault,
    /// Compatibility host restores the current declaration option after reset.
    PreserveCurrent,
}

/// Independently captured effective option behavior, separate from lexical payload.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LifetimeEffect {
    /// The host ignored/rejected this option or it does not affect lifetime.
    Unchanged,
    /// Subsequent declarations become scoped.
    Scoped,
    /// Subsequent declarations become global.
    Global,
}

/// Original declaration command head, not reconstructed from its signature.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeclarationSyntax {
    /// `declare-sort`.
    DeclareSort,
    /// `declare-sort-parameter`.
    DeclareSortParameter,
    /// `define-sort`.
    DefineSort,
    /// `declare-datatype`.
    DeclareDatatype,
    /// `declare-datatypes`.
    DeclareDatatypes,
    /// `declare-fun`.
    DeclareFun,
    /// `declare-const`.
    DeclareConst,
    /// `declare-var`.
    DeclareVar,
    /// `declare-rel`.
    DeclareRel,
    /// `define-fun`.
    DefineFun,
    /// `define-fun-rec`.
    DefineFunRec,
    /// `define-funs-rec`.
    DefineFunsRec,
    /// `synth-fun`, retaining synthesis payload separately.
    SynthFun,
    /// `synth-inv`, retaining synthesis payload separately.
    SynthInv,
}

/// Synthesis formal environment, retained even when no grammar was authored.
#[derive(Clone, Debug)]
pub struct SynthesisSyntax {
    /// Original sorted formal binders, local to grammar productions.
    pub parameters: Vec<Binder>,
    /// Complete structured grammar syntax, if present.
    pub grammar: Option<DataId>,
}

/// Every source command affecting the query plus structured response requests.
#[derive(Clone, Debug)]
pub enum QueryCommand {
    /// Catalog entries in order; all catalog entries must occur exactly once.
    Declarations {
        /// Captured original command head.
        syntax: DeclarationSyntax,
        /// Explicit visibility/recursion classification.
        kind: DeclarationGroupKind,
        /// Ordered catalog entries, including implicit datatype members.
        entries: Vec<DeclId>,
        /// Synthesis formal binders and optional grammar, never discarded as unused.
        synthesis: Option<SynthesisSyntax>,
    },
    /// Ordered assertion/rule/objective occurrences and original attributes.
    Roots {
        /// Original assertion, rule or objective role.
        kind: RootKind,
        /// Authored term occurrences in order.
        roots: Vec<NodeId>,
        /// Original annotations in order.
        attributes: Vec<Attribute>,
    },
    /// Check operation with duplicate assumptions preserved.
    Check {
        /// Original check command classification.
        kind: CheckKind,
        /// Original assumptions in order, including duplicates.
        assumptions: Vec<NodeId>,
    },
    /// Logic selection, retaining nominal token spelling.
    SetLogic(SymbolToken),
    /// Ordered option change; this is part of identity, not an env override.
    SetOption {
        /// Exact authored option, retaining quoted/Boolean/ignored payload forms.
        attribute: Attribute,
        /// Captured effect, independently checked against source and host semantics.
        lifetime: LifetimeEffect,
    },
    /// Ordered metadata change.
    SetInfo(Attribute),
    /// Push/pop syntax; `None` is the omitted/default numeral alternative.
    Scope {
        /// Whether this command pushes or pops assertion scopes.
        kind: ScopeKind,
        /// Effective number of scopes affected.
        levels: u32,
        /// Authored numeral, or omission of that optional syntax.
        numeral: Option<String>,
    },
    /// Reset all declarations and assertion state; catalog history remains.
    Reset,
    /// Reset assertions while retaining declared symbols.
    ResetAssertions,
    /// Non-mutating response request with structured payload and typed term roots.
    ///
    /// The caller's independent command mapper must establish this classification;
    /// this variant is not permission to treat unknown mutations as non-mutating.
    Request {
        /// Original response-request command token.
        head: SymbolToken,
        /// Structured non-term payload in authored order.
        payload: Vec<DataId>,
        /// Explicit term roots referenced by the request.
        terms: Vec<NodeId>,
    },
}
