// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

macro_rules! locator {
    ($name:ident, $doc:literal) => {
        #[doc = $doc]
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name(pub u32);
    };
}
locator!(
    NodeId,
    "Descriptor-local term locator, never a semantic TermId."
);
locator!(
    SortId,
    "Descriptor-local sort-syntax locator, never semantic sort identity."
);
locator!(DataId, "Descriptor-local structured payload locator.");
locator!(
    DeclId,
    "Ordered nominal catalog locator, never declaration authority."
);
locator!(
    BinderId,
    "Lexical term-binder locator, meaningful only under its occurrence environment."
);
locator!(
    TypeParameterId,
    "Lexical type-parameter locator, meaningful only under its owning environment."
);

/// Lexical symbol distinction retained before any parser normalization.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SymbolKind {
    /// Unquoted symbol token.
    Simple,
    /// Quoted symbol token, including reserved-looking spellings.
    Quoted,
}

/// Symbol spelling and its original token kind.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SymbolToken {
    /// Lexical kind, not inferred from the spelling.
    pub kind: SymbolKind,
    /// Decoded symbol contents, without vertical-bar delimiters.
    pub text: String,
}

/// Non-interchangeable literal token kinds; no numeric normalization.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LiteralKind {
    /// Boolean constant token, distinct from a quoted/free nominal symbol.
    Boolean,
    /// Decimal integer digit token.
    Numeral,
    /// Decimal fraction digit token.
    Decimal,
    /// Hexadecimal digit token, without `#x`.
    Hexadecimal,
    /// Binary digit token, without `#b`.
    Binary,
    /// Decoded SMT-LIB string contents; original bytes are bound separately.
    String,
}

/// Unfolded literal contents, not a bignum computation or Display string.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Literal {
    /// Original lexical literal kind.
    pub kind: LiteralKind,
    /// Digit spelling or decoded string contents.
    pub text: String,
}

/// Explicit builtin namespace, distinct even from an identically named declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BuiltinFamily {
    /// Core Boolean and equality syntax.
    Core,
    /// Arithmetic and numeric conversion syntax.
    Arithmetic,
    /// Bit-vector syntax.
    BitVector,
    /// Floating-point syntax.
    FloatingPoint,
    /// Array syntax.
    Array,
    /// String syntax.
    String,
    /// Sequence syntax.
    Sequence,
    /// Regular-expression syntax.
    Regex,
    /// Set/bag/relation syntax.
    Collection,
    /// Datatype tester syntax.
    Datatype,
    /// Captured host-language extension; not a semantic escape hatch.
    Extension,
}

/// Structured builtin head; this tag does not establish builtin semantics.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Builtin {
    /// Captured builtin family.
    pub family: BuiltinFamily,
    /// Exact symbol token, never parsed from a rendered term.
    pub symbol: SymbolToken,
}

/// An indexed identifier's token, preserving numeral versus symbol indices.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IndexToken {
    /// Numeral index, retaining digit spelling.
    Numeral(String),
    /// Decimal index, including indexed-plugin extension syntax.
    Decimal(String),
    /// Hexadecimal index without `#x`.
    Hexadecimal(String),
    /// Binary index without `#b`.
    Binary(String),
    /// Symbol index, retaining quotation kind.
    Symbol(SymbolToken),
    /// Original symbol index with an independently resolved semantic namespace.
    ///
    /// The native mapper must establish that this occurrence denotes `reference`;
    /// the token/locator pair is structural evidence, never resolution authority.
    /// Raw metadata symbols remain the separate `Symbol` alternative.
    Reference {
        /// Original index spelling and lexical quotation kind.
        symbol: SymbolToken,
        /// Resolved builtin, visible nominal declaration, or lexical binder.
        reference: OperatorHead,
    },
}

/// Resolved operator namespace; nominal declarations cannot masquerade as builtins.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OperatorHead {
    /// Explicitly classified builtin operator.
    Builtin(Builtin),
    /// A visible nominal function/constructor/selector/relation.
    Declaration(DeclId),
    /// A lexically bound higher-order function.
    Bound(BinderId),
}

/// Full indexed/qualified head of an authored application.
#[derive(Clone, Debug)]
pub struct Operator {
    /// Builtin, nominal, or bound head.
    pub head: OperatorHead,
    /// Authored indices in order.
    pub indices: Vec<IndexToken>,
    /// Authored `as` qualification, distinct from an inferred result sort.
    pub qualification: Option<SortId>,
}

/// Unfolded sort syntax; aliases are retained as nominal applications.
#[derive(Clone, Debug)]
pub enum SortNode {
    /// Builtin sort application, including array/function/indexed sorts.
    Builtin {
        /// Closed builtin sort constructor.
        head: Builtin,
        /// Authored sort indices in order.
        indices: Vec<IndexToken>,
        /// Original sort arguments in order.
        arguments: Vec<SortId>,
    },
    /// A nominal sort/alias/datatype application.
    Nominal {
        /// Original nominal declaration identity.
        declaration: DeclId,
        /// Original sort arguments in order.
        arguments: Vec<SortId>,
    },
    /// A lexically scoped type parameter.
    Parameter(TypeParameterId),
}

/// Structured option/annotation syntax, without string-rendering authority.
#[derive(Clone, Debug)]
pub enum DataNode {
    /// Symbol token, retaining quotation kind.
    Symbol(SymbolToken),
    /// Resolved annotation/grammar reference, checked under its occurrence scope.
    /// Raw metadata symbols remain the distinct `Symbol` alternative.
    Reference(OperatorHead),
    /// Keyword contents without `:`.
    Keyword(String),
    /// Literal token, retaining lexical kind.
    Literal(Literal),
    /// Ordered S-expression children.
    List(Vec<DataId>),
}

/// An authored attribute; valueless attributes remain distinct.
#[derive(Clone, Debug)]
pub struct Attribute {
    /// Keyword contents without `:`.
    pub keyword: String,
    /// Structured payload, or the valueless attribute alternative.
    pub value: Option<DataId>,
}

/// Term binder with captured name and sort.
#[derive(Clone, Debug)]
pub struct Binder {
    /// Lexical binder locator, not a global symbol.
    pub id: BinderId,
    /// Captured spelling; only this bound name may be alpha-renamed.
    pub name: SymbolToken,
    /// Authored binder sort.
    pub sort: SortId,
}

/// Type binder with captured name.
#[derive(Clone, Debug)]
pub struct TypeParameter {
    /// Lexical type-parameter locator.
    pub id: TypeParameterId,
    /// Captured name, eligible for consistent alpha-renaming only.
    pub name: SymbolToken,
}

/// Distinct binding constructs; no lowering to one another.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Quantifier {
    /// Universal quantification.
    Forall,
    /// Existential quantification.
    Exists,
    /// Lambda abstraction.
    Lambda,
}

/// Simultaneous let binding; its value sees only the incoming environment.
#[derive(Clone, Debug)]
pub struct LetBinding {
    /// Binder introduced only for the let body.
    pub binder: Binder,
    /// Right-hand-side root in the incoming environment.
    pub value: NodeId,
}

/// Match pattern preserves constructor versus wildcard-variable distinction.
#[derive(Clone, Debug)]
pub enum MatchPattern {
    /// A constructor pattern with local field binders.
    Constructor {
        /// Nominal constructor selected by the pattern.
        declaration: DeclId,
        /// Ordered binder or wildcard fields.
        fields: Vec<PatternField>,
    },
    /// A variable/default case that binds the entire scrutinee.
    Variable(Binder),
    /// Unbound default wildcard, introducing no variable.
    Wildcard,
}

/// Constructor pattern field, distinguishing binders from unbound `_`.
#[derive(Clone, Debug)]
pub enum PatternField {
    /// Named field binder scoped only to its case body.
    Binder(Binder),
    /// Unbound field wildcard with its captured sort.
    Wildcard(SortId),
}

/// Match case with case-local bindings.
#[derive(Clone, Debug)]
pub struct MatchCase {
    /// Authored pattern, not an inferred constructor spelling.
    pub pattern: MatchPattern,
    /// Body root under this case's bindings only.
    pub body: NodeId,
}

/// Complete typed term syntax before canonicalization or folding.
#[derive(Clone, Debug)]
pub struct TypedNode {
    /// Captured type, checked structurally but not theory-semantically here.
    pub sort: SortId,
    /// Authored term structure.
    pub kind: NodeKind,
}

/// Authored term forms, retaining lexical binders and syntax rather than solver ids.
#[derive(Clone, Debug)]
pub enum NodeKind {
    /// Literal token.
    Literal(Literal),
    /// Visible free nominal reference, including nullary functions.
    Free(DeclId),
    /// Lexically bound variable reference.
    Bound(BinderId),
    /// Explicit operator application, preserving indices and qualification.
    Apply {
        /// Original operator, indices and qualification.
        operator: Operator,
        /// Original argument occurrences in order.
        arguments: Vec<NodeId>,
    },
    /// Simultaneous let; values do not see newly introduced binders.
    Let {
        /// Simultaneous bindings, preserving their authored order.
        bindings: Vec<LetBinding>,
        /// Body in the scope introduced by those bindings.
        body: NodeId,
    },
    /// Universal/existential/lambda binder block.
    Quantified {
        /// Universal, existential or lambda binder kind.
        quantifier: Quantifier,
        /// Lexical binders in authored order.
        binders: Vec<Binder>,
        /// Original body within that binder scope.
        body: NodeId,
    },
    /// Match with constructor/variable case distinction.
    Match {
        /// Original term being matched.
        scrutinee: NodeId,
        /// Constructor or wildcard cases in authored order.
        cases: Vec<MatchCase>,
    },
    /// Original annotation wrapper and ordered attributes.
    Annotated {
        /// Original annotated term.
        body: NodeId,
        /// Original annotations in order, including duplicates.
        attributes: Vec<Attribute>,
    },
}
