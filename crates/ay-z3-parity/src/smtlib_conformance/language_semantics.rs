// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Source-authenticated SMT-LIB typing/scope and command-state validators.
//!
//! These dimensions are deliberately separate from command grammar.  The
//! source inventory is a closed list of normative rules, each authenticated by
//! a unique exact byte span and containing source-line hash in the pinned
//! SMT-LIB 2.7 language snapshot.  The
//! semantic receipts then bind every rule to live, guarded AY transcripts.

use super::*;
use reference_inventory::{LanguageSourceFile, LoadedLanguageSource};

pub(super) const TYPE_SCOPE_VALIDATOR_ID: &str = "builtin.type-scope.v1";
pub(super) const STATE_MACHINE_VALIDATOR_ID: &str = "builtin.command-state-machine.v1";

const TYPE_SCOPE_DIMENSION: &str = "semantics.typing-and-scope";
const STATE_MACHINE_DIMENSION: &str = "semantics.command-state-machine";
const TYPE_MARKER: &str = "__ay_type_scope_recovered__";
const STATE_MARKER: &str = "__ay_command_state_completed__";
const STATE_PROBE_MARKER: &str = "__ay_command_under_test__";

#[derive(Clone, Copy)]
struct SourceRule {
    id: &'static str,
    path: &'static str,
    anchor: &'static str,
    claim: &'static str,
    typing: Option<&'static str>,
    state: Option<&'static str>,
    semantic: &'static str,
}

impl SourceRule {
    fn requirement(self, dimension: &str) -> Requirement {
        requirement(
            format!("{dimension}.{}", self.id),
            SourceCohort::SmtlibLanguage,
            format!("{}:anchor-sha256={}", self.path, sha256_bytes(self.anchor.as_bytes())),
            Classification::Standard,
            self.claim,
            expectation(
                None,
                self.typing,
                self.state,
                None,
                self.semantic,
            ),
            "no exhaustive source-authenticated positive/negative/stateful transcript receipt is attached",
        )
    }
}

const TYPE_RULES: &[SourceRule] = &[
    SourceRule {
        id: "sort-symbol-resolution",
        path: "Reference/concrete-syntax.tex",
        anchor: "The set of sorts consists itself of \\define{sort terms}.",
        claim: "Resolve every sort term only from the current signature",
        typing: Some("accept declared and theory sorts and reject unknown sorts"),
        state: None,
        semantic: "sort lookup is exact and never invents an undeclared sort",
    },
    SourceRule {
        id: "sort-constructor-arity",
        path: "Reference/concrete-syntax.tex",
        anchor: "a sort symbol applied to a sequence of sort terms",
        claim: "Apply each sort constructor at exactly its declared arity",
        typing: Some("reject every under- and over-applied sort constructor"),
        state: None,
        semantic: "sort-constructor arity is checked before a term enters the context",
    },
    SourceRule {
        id: "variable-judgment",
        path: "Reference/syntax-macros.tex",
        anchor: "{\\Sigma \\vdash x:\\tau}",
        claim: "Give a variable the unique sort associated with it in the active signature",
        typing: Some("accept bound or declared variables and reject free variables"),
        state: None,
        semantic: "the variable sorting judgment is implemented exactly",
    },
    SourceRule {
        id: "function-application-arity",
        path: "Reference/syntax-macros.tex",
        anchor: "{\\Sigma \\vdash (f\\; t_1\\; \\cdots\\; t_k): \\tau}",
        claim: "Apply function symbols with exactly the arity of a matching rank",
        typing: Some("reject missing and trailing operands"),
        state: None,
        semantic: "application arity participates in rank resolution",
    },
    SourceRule {
        id: "function-application-operands",
        path: "Reference/syntax-macros.tex",
        anchor: "f{:}\\tau_1 \\cdots \\tau_k\\tau \\in \\Sigma, \\\\",
        claim: "Match every application operand against the corresponding rank sort",
        typing: Some("reject applications whose operand sorts have no matching rank"),
        state: None,
        semantic: "no ill-sorted function application reaches solving",
    },
    SourceRule {
        id: "ambiguous-qualified-identifier",
        path: "Reference/concrete-syntax.tex",
        anchor: "every occurrence of an ambiguous function symbol",
        claim: "Require and validate result-sort qualification for ambiguous function symbols",
        typing: Some("accept a matching `(as f sort)` and reject a mismatching or missing qualification"),
        state: None,
        semantic: "qualification selects exactly one result rank",
    },
    SourceRule {
        id: "formula-bool-sort",
        path: "Reference/logical-semantics.tex",
        anchor: "\\define{Formulas} are well-sorted terms of sort $\\bool$.",
        claim: "Admit only Bool-sorted terms where a formula is required",
        typing: Some("reject non-Bool assert and quantifier bodies"),
        state: None,
        semantic: "formula contexts cannot coerce arbitrary terms to Bool",
    },
    SourceRule {
        id: "equality-common-sort",
        path: "Reference/logical-semantics.tex",
        anchor: "does not allow one to equate terms of different sorts",
        claim: "Instantiate polymorphic equality at one common operand sort",
        typing: Some("accept same-sort operands and reject incompatible sorts"),
        state: None,
        semantic: "equality never compares values from unrelated sorts",
    },
    SourceRule {
        id: "ite-condition-and-branches",
        path: "Reference/concrete-syntax.tex",
        anchor: "In this theory, \\ter{ite} has two ranks:",
        claim: "Require a Bool `ite` condition and a single common branch sort",
        typing: Some("reject non-Bool conditions and incompatible branches"),
        state: None,
        semantic: "the result sort of ite is the common branch sort",
    },
    SourceRule {
        id: "explicit-numeric-coercion",
        path: "Reference/logical-semantics.tex",
        anchor: "the sort structure is flat (no subsorts)",
        claim: "Use declared conversion functions instead of implicit cross-sort subtyping",
        typing: Some("type `to_real` and `to_int` at their declared ranks and reject wrong-domain calls"),
        state: None,
        semantic: "Int and Real remain distinct sorts despite overloaded numerals",
    },
    SourceRule {
        id: "quantifier-binder",
        path: "Reference/syntax-macros.tex",
        anchor: "if $Q\\, \\in \\{\\exists, \\forall\\}$",
        claim: "Extend the local signature for quantifier variables and require a Bool body",
        typing: Some("bound occurrences receive the declared sort only inside the body"),
        state: None,
        semantic: "quantifier binding follows the formal sorting judgment",
    },
    SourceRule {
        id: "binder-lexical-shadowing",
        path: "Reference/concrete-syntax.tex",
        anchor: "a bound variable will shadow any variable or user-defined",
        claim: "Apply lexical shadowing of enclosing variables and user function symbols",
        typing: Some("the innermost binder determines the local occurrence sort"),
        state: None,
        semantic: "binder shadowing is lexical and ends with its body",
    },
    SourceRule {
        id: "theory-symbol-no-shadowing",
        path: "Reference/concrete-syntax.tex",
        anchor: "binders cannot shadow \\define{theory function or sort symbols}",
        claim: "Reject binders and sort parameters that shadow current theory symbols",
        typing: Some("theory function and sort names remain reserved in local binders"),
        state: None,
        semantic: "the historical no-theory-shadowing exception is enforced",
    },
    SourceRule {
        id: "let-simultaneous-scope",
        path: "Reference/concrete-syntax.tex",
        anchor: "the scope of each variable in $\\{x_1, \\ldots, x_n\\}$ is the term $t$.",
        claim: "Elaborate let bindings simultaneously and scope them only over the body",
        typing: Some("a binding right-hand side cannot see sibling bindings"),
        state: None,
        semantic: "let is simultaneous rather than sequential",
    },
    SourceRule {
        id: "let-distinct-binders",
        path: "Reference/syntax-macros.tex",
        anchor: "if $x_1, \\ldots, x_{k+1}$ are all distinct",
        claim: "Require distinct variables in one let binder",
        typing: Some("reject repeated variables in a single let binding list"),
        state: None,
        semantic: "a let body has one unambiguous association per binder name",
    },
    SourceRule {
        id: "match-exhaustiveness",
        path: "Reference/logical-semantics.tex",
        anchor: "require that the match cases be \\define{exhaustive}",
        claim: "Require every match expression to cover its datatype",
        typing: Some("accept complete constructor or wildcard coverage and reject incomplete matches"),
        state: None,
        semantic: "match expressions are semantically total",
    },
    SourceRule {
        id: "match-pattern-scope",
        path: "Reference/concrete-syntax.tex",
        anchor: "the scope of each variable occurring in pattern $p_i$ is the corresponding term $t_i$",
        claim: "Scope each match-pattern variable over only its corresponding branch",
        typing: Some("reject pattern variables referenced by sibling branches or outside match"),
        state: None,
        semantic: "pattern bindings do not leak across cases",
    },
    SourceRule {
        id: "match-branch-common-sort",
        path: "Reference/syntax-macros.tex",
        anchor: "\\Sigma[\\bar x_i{:}\\bar\\tau_i]\\: \\vdash t_i:\\tau \\text{ for } i=1,\\ldots,k+1",
        claim: "Require all match branches to have one common result sort",
        typing: Some("reject a match with incompatible branch sorts"),
        state: None,
        semantic: "a match expression has a unique result sort",
    },
    SourceRule {
        id: "annotation-sort-preservation",
        path: "Reference/concrete-syntax.tex",
        anchor: "Term attributes have no logical meaning",
        claim: "Preserve the wrapped term sort through annotations",
        typing: Some("annotations neither repair nor change an ill-sorted term"),
        state: None,
        semantic: "annotation erasure preserves typing and semantics",
    },
    SourceRule {
        id: "namespace-separation",
        path: "Reference/concrete-syntax.tex",
        anchor: "There are several namespaces for identifiers:",
        claim: "Keep sort, term, command, and attribute namespaces distinct",
        typing: Some("the same spelling may coexist in distinct namespaces"),
        state: None,
        semantic: "only collisions within the relevant namespace are errors",
    },
    SourceRule {
        id: "sort-declaration-collision",
        path: "Reference/operational-semantics.tex",
        anchor: "It is an error if $s$ is a sort symbol or parameter already present",
        claim: "Reject sort declarations colliding with an active sort symbol or parameter",
        typing: Some("a rejected declaration leaves the original sort binding unchanged"),
        state: None,
        semantic: "sort declarations are unique within the active signature",
    },
    SourceRule {
        id: "function-declaration-collision",
        path: "Reference/operational-semantics.tex",
        anchor: "The command reports an error if a function symbol with name $f$ \nis already present in the current signature.",
        claim: "Reject declaration of an active user function name",
        typing: Some("user function symbols are not overloaded by scripts"),
        state: None,
        semantic: "a collision is atomic and preserves the earlier binding",
    },
    SourceRule {
        id: "definition-body-result",
        path: "Reference/operational-semantics.tex",
        anchor: "of sort $\\tau$ with respect to the current signature extended",
        claim: "Check a function definition body against its declared result sort",
        typing: Some("parameters are in scope in the body and the body must match the result"),
        state: None,
        semantic: "an ill-sorted definition never enters the signature",
    },
    SourceRule {
        id: "nonrecursive-definition",
        path: "Reference/operational-semantics.tex",
        anchor: "the restriction on $t$ prohibits recursive or mutually recursive",
        claim: "Reject self-reference in non-recursive definitions",
        typing: Some("define-fun checks its body before adding its own name"),
        state: None,
        semantic: "recursion is admitted only by recursive definition commands",
    },
    SourceRule {
        id: "mutual-recursive-definition",
        path: "Reference/operational-semantics.tex",
        anchor: "Mutual recursion is possible since each term $t_i$ can contain any applications",
        claim: "Type mutually recursive bodies in the signature of the complete declaration group",
        typing: Some("all recursive names are visible and every body matches its declared result"),
        state: None,
        semantic: "recursive groups are installed atomically",
    },
    SourceRule {
        id: "sort-alias-parameter-scope",
        path: "Reference/operational-semantics.tex",
        anchor: "where the $u_i$'s are (local) sort parameters",
        claim: "Scope define-sort parameters over the alias body and reject circular aliases",
        typing: Some("the alias body may use exactly its local parameters and active sorts"),
        state: None,
        semantic: "sort aliases expand by simultaneous parameter substitution",
    },
    SourceRule {
        id: "global-sort-parameter",
        path: "Reference/operational-semantics.tex",
        anchor: "adds \\emph{global} sort parameter $s$ to the current signature",
        claim: "Keep declared sort parameters global and usable in polymorphic ranks and assertions",
        typing: Some("reject collisions and uses forbidden by define-sort or datatype local-parameter rules"),
        state: None,
        semantic: "check-sat instantiates global parameters over the current monomorphic signature",
    },
    SourceRule {
        id: "datatype-parameter-scope",
        path: "Reference/operational-semantics.tex",
        anchor: "the terms $\\tau_i$ can contain only the sort parameters in the list",
        claim: "Restrict parametric datatype fields to their declared local parameters",
        typing: Some("datatype arity, parameter list, and field sorts agree"),
        state: None,
        semantic: "datatype parameter order determines constructor and selector ranks",
    },
    SourceRule {
        id: "datatype-symbol-collisions",
        path: "Reference/operational-semantics.tex",
        anchor: "of the same constructor in different datatypes or the use",
        claim: "Reject datatype, constructor, and selector name collisions",
        typing: Some("all symbols introduced by a datatype group are pairwise valid before commit"),
        state: None,
        semantic: "a rejected datatype group leaves no partial declarations",
    },
    SourceRule {
        id: "scoped-declaration-lifetime",
        path: "Reference/operational-semantics.tex",
        anchor: "Popping that assertion level removes them.",
        claim: "Remove non-global declarations and definitions with their assertion level",
        typing: Some("a popped symbol becomes unknown and its name can be declared again"),
        state: Some("push and pop delimit the active signature"),
        semantic: "scope lifetime affects both lookup and collision checking",
    },
    SourceRule {
        id: "global-declaration-lifetime",
        path: "Reference/operational-semantics.tex",
        anchor: "all declarations and definitions become permanent.",
        claim: "Preserve global declarations across pop and reset-assertions and remove them on reset",
        typing: Some("surviving symbols retain their exact ranks"),
        state: Some("the global-declarations option selects declaration lifetime"),
        semantic: "global declarations are outside the assertion stack",
    },
    SourceRule {
        id: "reserved-user-symbol-prefixes",
        path: "Reference/concrete-syntax.tex",
        anchor: "cannot have a name that begins with a dot",
        claim: "Reject user-declared and user-defined symbols reserved for solver use or abstract values",
        typing: Some("names beginning with dot or at-sign are not user signature entries"),
        state: None,
        semantic: "reserved namespaces cannot be captured by user declarations",
    },
];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Mode {
    Start,
    Assert,
    Sat,
    Unsat,
}

impl Mode {
    const ALL: [Self; 4] = [Self::Start, Self::Assert, Self::Sat, Self::Unsat];

    fn id(self) -> &'static str {
        match self {
            Self::Start => "start",
            Self::Assert => "assert",
            Self::Sat => "sat",
            Self::Unsat => "unsat",
        }
    }
}

#[derive(Clone, Copy)]
struct CommandRule {
    name: &'static str,
    command: &'static str,
    anchor: &'static str,
    allowed: &'static [Mode],
    result_class: ResultClass,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ResultClass {
    None,
    Check,
    Echo,
    Exit,
}

const START_ONLY: &[Mode] = &[Mode::Start];
const ASSERT_QUERY: &[Mode] = &[Mode::Assert, Mode::Sat, Mode::Unsat];
const ALL_MODES: &[Mode] = &[Mode::Start, Mode::Assert, Mode::Sat, Mode::Unsat];
const SAT_ONLY: &[Mode] = &[Mode::Sat];
const UNSAT_ONLY: &[Mode] = &[Mode::Unsat];

const COMMAND_RULES: &[CommandRule] = &[
    CommandRule {
        name: "assert",
        command: "(assert true)",
        anchor: "%%% assert %%%",
        allowed: ASSERT_QUERY,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "check-sat",
        command: "(check-sat)",
        anchor: "%%% check-sat %%%",
        allowed: ASSERT_QUERY,
        result_class: ResultClass::Check,
    },
    CommandRule {
        name: "check-sat-assuming",
        command: "(check-sat-assuming ())",
        anchor: "%%% check-sat-assuming %%%",
        allowed: ASSERT_QUERY,
        result_class: ResultClass::Check,
    },
    CommandRule {
        name: "declare-const",
        command: "(declare-const state_c Bool)",
        anchor: "%%% declare-const %%%",
        allowed: ASSERT_QUERY,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "declare-datatype",
        command: "(declare-datatype StateD ((state_a) (state_b)))",
        anchor: "%%% declare-datatype %%%",
        allowed: ASSERT_QUERY,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "declare-datatypes",
        command: "(declare-datatypes ((StateE 0)) (((state_e))))",
        anchor: "%%% declare-datatypes %%%",
        allowed: ASSERT_QUERY,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "declare-fun",
        command: "(declare-fun state_f (Bool) Bool)",
        anchor: "%%% declare-fun %%%",
        allowed: ASSERT_QUERY,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "declare-sort",
        command: "(declare-sort StateS 0)",
        anchor: "%%% declare-sort %%%",
        allowed: ASSERT_QUERY,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "declare-sort-parameter",
        command: "(declare-sort-parameter StateP)",
        anchor: "%%% declare-sort-parameter %%%",
        allowed: ASSERT_QUERY,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "define-const",
        command: "(define-const state_dc Bool true)",
        anchor: "%%% define-const %%%",
        allowed: ASSERT_QUERY,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "define-fun",
        command: "(define-fun state_df ((x Bool)) Bool x)",
        anchor: "%%% define-fun %%%",
        allowed: ASSERT_QUERY,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "define-fun-rec",
        command: "(define-fun-rec state_dr ((x Bool)) Bool x)",
        anchor: "%%% define-fun-rec %%%",
        allowed: ASSERT_QUERY,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "define-funs-rec",
        command: "(define-funs-rec ((state_dm ((x Bool)) Bool)) (x))",
        anchor: "%%% define-funs-rec %%%",
        allowed: ASSERT_QUERY,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "define-sort",
        command: "(define-sort StateAlias () Bool)",
        anchor: "%%% define-sort %%%",
        allowed: ASSERT_QUERY,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "echo",
        command: "(echo \"__ay_command_under_test__\")",
        anchor: "%%% echo %%%",
        allowed: ALL_MODES,
        result_class: ResultClass::Echo,
    },
    CommandRule {
        name: "exit",
        command: "(exit)",
        anchor: "%%% exit %%%",
        allowed: ALL_MODES,
        result_class: ResultClass::Exit,
    },
    CommandRule {
        name: "get-assertions",
        command: "(get-assertions)",
        anchor: "%%% get-assertions %%%",
        allowed: ASSERT_QUERY,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "get-assignment",
        command: "(get-assignment)",
        anchor: "%%% get-assignment %%%",
        allowed: SAT_ONLY,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "get-info",
        command: "(get-info :name)",
        anchor: "%%% get-info %%%",
        allowed: ALL_MODES,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "get-model",
        command: "(get-model)",
        anchor: "%%% get-model %%%",
        allowed: SAT_ONLY,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "get-option",
        command: "(get-option :print-success)",
        anchor: "%%% get-option %%%",
        allowed: ALL_MODES,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "get-proof",
        command: "(get-proof)",
        anchor: "%%% get-proof %%%",
        allowed: UNSAT_ONLY,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "get-unsat-assumptions",
        command: "(get-unsat-assumptions)",
        anchor: "%%% get-unsat-assumptions %%%",
        allowed: UNSAT_ONLY,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "get-unsat-core",
        command: "(get-unsat-core)",
        anchor: "%%% get-unsat-core %%%",
        allowed: UNSAT_ONLY,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "get-value",
        command: "(get-value (true))",
        anchor: "%%% get-value %%%",
        allowed: SAT_ONLY,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "pop",
        command: "(pop 1)",
        anchor: "%%% pop %%%",
        allowed: ASSERT_QUERY,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "push",
        command: "(push 1)",
        anchor: "%%% push %%%",
        allowed: ASSERT_QUERY,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "reset",
        command: "(reset)",
        anchor: "%%% reset %%%",
        allowed: ALL_MODES,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "reset-assertions",
        command: "(reset-assertions)",
        anchor: "%%% reset-assertions %%%",
        allowed: ALL_MODES,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "set-info",
        command: "(set-info :source |state-validator|)",
        anchor: "%%% set-info %%%",
        allowed: ALL_MODES,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "set-logic",
        command: "(set-logic ALL)",
        anchor: "%%% set-logic %%%",
        allowed: START_ONLY,
        result_class: ResultClass::None,
    },
    CommandRule {
        name: "set-option",
        command: "(set-option :verbosity 0)",
        anchor: "%%% set-option %%%",
        allowed: ALL_MODES,
        result_class: ResultClass::None,
    },
];

const STATE_EFFECT_RULES: &[SourceRule] = &[
    SourceRule {
        id: "initial-mode-and-set-logic",
        path: "Reference/operational-semantics.tex",
        anchor: "The solver starts in \\mode{start} mode, moves to \\mode{assert mode}",
        claim: "Start with one empty level and enter assert mode only after set-logic",
        typing: None,
        state: Some("set-logic is accepted in start mode and rejected after the transition"),
        semantic: "the initial mode and first transition are observable and deterministic",
    },
    SourceRule {
        id: "error-atomicity-and-recovery",
        path: "Reference/operational-semantics.tex",
        anchor: "the solver's state remains unmodified by the error-generating command",
        claim: "On continued execution, report an error, roll back the command, and accept later commands",
        typing: None,
        state: Some("the assertion stack and signature are unchanged by a rejected command"),
        semantic: "an error cannot partially commit state or suppress recovery",
    },
    SourceRule {
        id: "push-pop-stack-effects",
        path: "Reference/operational-semantics.tex",
        anchor: "pops the $n$ most-recent assertion levels from the stack",
        claim: "Push empty levels, pop exactly the requested levels, and reject underflow atomically",
        typing: None,
        state: Some("assertions and local declarations follow their owning level"),
        semantic: "the first assertion level is never popped",
    },
    SourceRule {
        id: "reset-assertions-effects",
        path: "Reference/operational-semantics.tex",
        anchor: "all assertion levels beyond the first one.",
        claim: "Reset assertions, local declarations, and definitions while preserving logic and options",
        typing: None,
        state: Some("reset-assertions returns to assert mode with one empty level"),
        semantic: "global declarations and set-option information survive",
    },
    SourceRule {
        id: "reset-complete-effects",
        path: "Reference/operational-semantics.tex",
        anchor: "resets the solver completely to the state it had after it was started",
        claim: "Reset the complete solver state, including logic, options, declarations, and result artifacts",
        typing: None,
        state: Some("reset returns every mode to start mode"),
        semantic: "the post-reset state is observationally equivalent to a new process",
    },
    SourceRule {
        id: "global-declarations-effects",
        path: "Reference/operational-semantics.tex",
        anchor: "they survive any pop operations on the assertion stack",
        claim: "Keep global declarations through pop and reset-assertions but not reset",
        typing: None,
        state: Some("global declarations remain outside all assertion levels"),
        semantic: "declaration lifetime follows the option value at introduction time",
    },
    SourceRule {
        id: "temporary-assumptions",
        path: "Reference/operational-semantics.tex",
        anchor: "should preserve the current context",
        claim: "Apply check-sat-assuming literals to exactly one query without modifying the context",
        typing: Some("each assumption is Bool-sorted"),
        state: Some("a later check without assumptions sees the original context"),
        semantic: "assumptions are query-epoch inputs, not stack assertions",
    },
    SourceRule {
        id: "sat-artifact-epoch",
        path: "Reference/operational-semantics.tex",
        anchor: "it receives the next check command or it exits the \\mode{sat} mode,",
        claim: "Expose model artifacts only for the current sat query epoch",
        typing: None,
        state: Some("mutation or a later query invalidates the previous model authority"),
        semantic: "get-model, get-value, and get-assignment cannot observe stale results",
    },
    SourceRule {
        id: "unsat-artifact-epoch",
        path: "Reference/operational-semantics.tex",
        anchor: "The next three commands can be issued only when the solver is \nin \\mode{unsat} mode",
        claim: "Expose proof and unsat artifacts only for the current unsat query epoch",
        typing: None,
        state: Some("mutation or a later query invalidates proof, core, and assumption authority"),
        semantic: "unsat inspection commands cannot observe stale results",
    },
    SourceRule {
        id: "success-response-timing",
        path: "Reference/operational-semantics.tex",
        anchor: "the effect applies already to the output of the very command",
        claim: "Apply print-success and output-affecting options to their own responses immediately",
        typing: None,
        state: Some("success is emitted exactly when enabled and never substitutes for a specific response"),
        semantic: "response behavior changes at the option command boundary",
    },
    SourceRule {
        id: "regular-output-channel",
        path: "Reference/operational-semantics.tex",
        anchor: "Regular output, including responses \\emph{and errors}",
        claim: "Route responses and errors through the selected regular output channel",
        typing: None,
        state: Some("channel changes apply to the setting command itself"),
        semantic: "regular responses never leak to the diagnostic channel",
    },
    SourceRule {
        id: "diagnostic-output-channel",
        path: "Reference/operational-semantics.tex",
        anchor: "Diagnostic output, including warnings, debugging, tracing,",
        claim: "Keep diagnostic output distinct from regular command responses",
        typing: None,
        state: Some("the diagnostic channel is independently configurable"),
        semantic: "machine-readable regular transcripts are not polluted by diagnostics",
    },
    SourceRule {
        id: "start-only-options",
        path: "Reference/operational-semantics.tex",
        anchor: "Some options can be set only when the solver is in \\mode{start} mode.",
        claim: "Reject start-only option changes after entering assert or query modes",
        typing: None,
        state: Some("a rejected option change leaves the prior value intact"),
        semantic: "option mode preconditions are explicit and atomic",
    },
    SourceRule {
        id: "poison-and-reset-recovery",
        path: "Reference/operational-semantics.tex",
        anchor: "or continue accepting commands.",
        claim: "Never publish a definitive result for a silently discarded problem command, and recover fully on reset",
        typing: None,
        state: Some("a fail-closed poisoned epoch yields unknown until a successful reset"),
        semantic: "soundness is preserved across recoverable implementation gaps",
    },
    SourceRule {
        id: "exit-any-mode",
        path: "Reference/operational-semantics.tex",
        anchor: "can be issued in any mode.",
        claim: "Accept exit in every execution mode and terminate after its response",
        typing: None,
        state: Some("no command after exit is executed"),
        semantic: "print-success, when enabled, precedes termination",
    },
];

pub(super) fn type_scope_requirements(_spec: DimensionSpec) -> Vec<Requirement> {
    TYPE_RULES
        .iter()
        .copied()
        .map(|rule| rule.requirement(TYPE_SCOPE_DIMENSION))
        .collect()
}

pub(super) fn command_state_requirements(_spec: DimensionSpec) -> Vec<Requirement> {
    let mut rows = COMMAND_RULES
        .iter()
        .map(|rule| {
            let allowed = rule
                .allowed
                .iter()
                .map(|mode| mode.id())
                .collect::<Vec<_>>()
                .join(",");
            SourceRule {
                id: rule.name,
                path: "Reference/operational-semantics.tex",
                anchor: rule.anchor,
                claim: "Implement the command's complete four-mode permission and transition row",
                typing: None,
                state: Some("accept exactly the modes named by the pinned transition graph"),
                semantic: "all four source modes have independent live witnesses",
            }
            .requirement(STATE_MACHINE_DIMENSION)
            .with_claim(format!(
                "Implement `{}` in exactly its SMT-LIB 2.7 modes ({allowed}) and apply its specified transition",
                rule.name
            ))
        })
        .collect::<Vec<_>>();
    rows.extend(
        STATE_EFFECT_RULES
            .iter()
            .copied()
            .map(|rule| rule.requirement(STATE_MACHINE_DIMENSION)),
    );
    rows
}

trait RequirementClaim {
    fn with_claim(self, claim: String) -> Self;
}

impl RequirementClaim for Requirement {
    fn with_claim(mut self, claim: String) -> Self {
        self.claim = claim;
        self
    }
}

fn source_rules_for_dimension(dimension_id: &str) -> Result<Vec<SourceRule>, String> {
    match dimension_id {
        TYPE_SCOPE_DIMENSION => Ok(TYPE_RULES.to_vec()),
        STATE_MACHINE_DIMENSION => {
            let mut rules = COMMAND_RULES
                .iter()
                .map(|rule| SourceRule {
                    id: rule.name,
                    path: "Reference/operational-semantics.tex",
                    anchor: rule.anchor,
                    claim: "command transition row",
                    typing: None,
                    state: None,
                    semantic: "four-mode transition matrix",
                })
                .collect::<Vec<_>>();
            rules.extend_from_slice(STATE_EFFECT_RULES);
            Ok(rules)
        }
        other => Err(format!(
            "no language-semantics source inventory for {other:?}"
        )),
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct BoundRule {
    requirement_id: String,
    source_sha256: String,
}

fn authenticate_rules(
    dimension: &Dimension,
    files: &[LanguageSourceFile],
) -> Result<Vec<BoundRule>, String> {
    let rules = source_rules_for_dimension(&dimension.id)?;
    if rules.len() != dimension.requirements.len() {
        return Err(format!(
            "{} source rule count {} differs from contract row count {}",
            dimension.id,
            rules.len(),
            dimension.requirements.len()
        ));
    }
    let requirements = dimension
        .requirements
        .iter()
        .map(|row| (row.id.as_str(), row))
        .collect::<BTreeMap<_, _>>();
    let mut bound = Vec::with_capacity(rules.len());
    for rule in rules {
        let requirement_id = format!("{}.{}", dimension.id, rule.id);
        let requirement = requirements
            .get(requirement_id.as_str())
            .ok_or_else(|| format!("{} has no canonical source row", requirement_id))?;
        let expected_locator = format!(
            "{}:anchor-sha256={}",
            rule.path,
            sha256_bytes(rule.anchor.as_bytes())
        );
        if requirement.source.cohort != SourceCohort::SmtlibLanguage
            || requirement.source.locator != expected_locator
        {
            return Err(format!("{} source locator drifted", requirement.id));
        }
        let file = files
            .iter()
            .find(|file| file.path == rule.path)
            .ok_or_else(|| format!("authenticated language snapshot is missing {}", rule.path))?;
        let occurrences = file.content.match_indices(rule.anchor).collect::<Vec<_>>();
        let [(byte_offset, _)] = occurrences.as_slice() else {
            return Err(format!(
                "authenticated {} must contain exactly one anchor for {}; found {}",
                rule.path,
                requirement.id,
                occurrences.len()
            ));
        };
        let byte_offset = *byte_offset;
        let span_end = byte_offset
            .checked_add(rule.anchor.len())
            .ok_or("language source anchor offset overflow")?;
        let line_start = file.content[..byte_offset]
            .rfind('\n')
            .map_or(0, |index| index + 1);
        let line_end = file.content[span_end..]
            .find('\n')
            .map_or(file.content.len(), |index| span_end + index);
        let containing_line = &file.content[line_start..line_end];
        let line_number = file.content[..byte_offset]
            .bytes()
            .filter(|byte| *byte == b'\n')
            .count()
            + 1;
        let source_binding = format!(
            "{}\0{}\0{}\0offset={}\0length={}\0line={}\0line-sha256={}\0{}",
            file.path,
            file.git_blob,
            file.content_sha256,
            byte_offset,
            rule.anchor.len(),
            line_number,
            sha256_bytes(containing_line.as_bytes()),
            rule.anchor
        );
        bound.push(BoundRule {
            requirement_id,
            source_sha256: sha256_bytes(source_binding.as_bytes()),
        });
    }
    bound.sort_by(|left, right| left.requirement_id.cmp(&right.requirement_id));
    Ok(bound)
}

pub(super) fn inventory_rows(
    dimension: &Dimension,
    files: &[LanguageSourceFile],
) -> Result<Vec<ValidatorCase>, String> {
    let bound = authenticate_rules(dimension, files)?;
    Ok(bound
        .into_iter()
        .map(|rule| ValidatorCase {
            id: format!("inventory.{}", rule.requirement_id),
            input_sha256: rule.source_sha256.clone(),
            expected: format!(
                "one unique exact byte span and containing-line hash in the authenticated SMT-LIB 2.7 language snapshot owns {}",
                rule.requirement_id
            ),
            observed: format!(
                "authenticated unique source-span binding sha256={} for {}",
                rule.source_sha256, rule.requirement_id
            ),
            stdout: None,
            stderr: None,
            exit_code: None,
            process: None,
            outcome: ValidatorCaseOutcome::Pass,
        })
        .collect())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Flavor {
    TypeScope,
    StateMachine,
}

impl Flavor {
    fn dimension_id(self) -> &'static str {
        match self {
            Self::TypeScope => TYPE_SCOPE_DIMENSION,
            Self::StateMachine => STATE_MACHINE_DIMENSION,
        }
    }

    fn validator_id(self) -> &'static str {
        match self {
            Self::TypeScope => TYPE_SCOPE_VALIDATOR_ID,
            Self::StateMachine => STATE_MACHINE_VALIDATOR_ID,
        }
    }

    fn validator_kind(self) -> ValidatorKind {
        match self {
            Self::TypeScope => ValidatorKind::TypeScopeConformance,
            Self::StateMachine => ValidatorKind::StateMachineConformance,
        }
    }

    fn cli_name(self) -> &'static str {
        match self {
            Self::TypeScope => "type-scope",
            Self::StateMachine => "command-state-machine",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ExpectedStatus {
    Accepted,
    Rejected,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum OutputExpectation {
    Accepted {
        marker: Option<&'static str>,
        required_lines: Vec<String>,
        verdict_count: Option<usize>,
    },
    Rejected {
        marker: &'static str,
        verdict_count: usize,
    },
    Exact {
        stdout: String,
        stderr: String,
        exit_code: i32,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CaseSpec {
    id: String,
    requirement_id: String,
    source_sha256: String,
    input: Vec<u8>,
    status: ExpectedStatus,
    output: OutputExpectation,
}

impl CaseSpec {
    fn expected(&self) -> String {
        let class = match self.status {
            ExpectedStatus::Accepted => "accepted-exit-zero",
            ExpectedStatus::Rejected => "rejected-exit-one-with-recovery",
        };
        format!(
            "authenticated-source-sha256={};requirement={};class={class};output={:?};guarded-process-complete",
            self.source_sha256, self.requirement_id, self.output
        )
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Execution {
    ay_sha256: String,
    resource_envelope: String,
    result: ValidatorResult,
    cases: CaseCounts,
    case_results: Vec<ValidatorCase>,
}

pub(super) fn run_type_scope(args: &[String]) -> Result<i32, String> {
    run_validator(Flavor::TypeScope, args)
}

pub(super) fn run_command_state(args: &[String]) -> Result<i32, String> {
    run_validator(Flavor::StateMachine, args)
}

fn run_validator(flavor: Flavor, args: &[String]) -> Result<i32, String> {
    let mut manifest: Option<PathBuf> = None;
    let mut receipt_path: Option<PathBuf> = None;
    let mut snapshot_path: Option<PathBuf> = None;
    let mut ay_override: Option<PathBuf> = None;
    let mut timeout_secs = 10u64;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--receipt" => {
                index += 1;
                receipt_path = Some(PathBuf::from(
                    args.get(index).ok_or("--receipt needs a path")?,
                ));
            }
            "--source-snapshot" => {
                index += 1;
                snapshot_path = Some(PathBuf::from(
                    args.get(index).ok_or("--source-snapshot needs a path")?,
                ));
            }
            "--ay" => {
                index += 1;
                ay_override = Some(PathBuf::from(args.get(index).ok_or("--ay needs a path")?));
            }
            "--timeout" => {
                index += 1;
                timeout_secs = args
                    .get(index)
                    .ok_or("--timeout needs seconds")?
                    .parse()
                    .map_err(|_| "--timeout must be a positive integer")?;
                if timeout_secs == 0 || timeout_secs > 3600 {
                    return Err("--timeout must be between 1 and 3600 seconds".to_string());
                }
            }
            flag if flag.starts_with("--") => {
                return Err(format!("unknown {} flag {flag:?}", flavor.cli_name()));
            }
            value => {
                if manifest.replace(PathBuf::from(value)).is_some() {
                    return Err(format!(
                        "{} takes exactly one manifest path",
                        flavor.cli_name()
                    ));
                }
            }
        }
        index += 1;
    }

    let manifest =
        manifest.ok_or_else(|| format!("{} needs a manifest path", flavor.cli_name()))?;
    let receipt_path =
        receipt_path.ok_or_else(|| format!("{} requires --receipt <path>", flavor.cli_name()))?;
    let snapshot_path = snapshot_path
        .as_deref()
        .ok_or_else(|| format!("{} requires --source-snapshot <path>", flavor.cli_name()))?;
    let loaded = load_contract(&manifest)?;
    let report = validate_contract(&loaded.contract, &loaded.base, ValidationMode::Structural)?;
    if loaded.contract.campaign_id == UNASSIGNED_CAMPAIGN {
        return Err("assign a real --campaign id before producing evidence".to_string());
    }
    let contract_envelope = loaded
        .contract
        .resource_envelope
        .as_deref()
        .ok_or_else(|| format!("{} requires contract.resource_envelope", flavor.cli_name()))?;
    let parsed_envelope = parse_resource_envelope(contract_envelope)?;
    if parsed_envelope.jobs != 1 {
        return Err(format!(
            "{} requires a one-job resource envelope",
            flavor.cli_name()
        ));
    }
    if parsed_envelope.timeout != Duration::from_secs(timeout_secs) {
        return Err(format!(
            "--timeout does not match contract.resource_envelope: expected {:?}",
            parsed_envelope.timeout
        ));
    }
    let dimension = semantic_dimension(&loaded.contract, flavor)?;
    let source = reference_inventory::load_language_source(
        &loaded.contract,
        dimension,
        &loaded.base,
        Some(snapshot_path),
    )?;
    let subject_ay = loaded
        .contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or_else(|| format!("{} requires subject.ay_executable", flavor.cli_name()))?;
    let ay = ay_override.unwrap_or_else(|| artifact_path(&loaded.base, &subject_ay.path));
    let output_relative = future_relative_output(&loaded.base, &receipt_path)?;
    let execution = execute(
        flavor,
        &loaded.contract,
        dimension,
        &ay,
        &source,
        Duration::from_secs(timeout_secs),
        Some(contract_envelope),
    )?;
    let current_exe = fs::canonicalize(
        std::env::current_exe().map_err(|error| format!("locating parity executable: {error}"))?,
    )
    .map_err(|error| format!("canonicalizing parity executable: {error}"))?;
    let validator_sha = sha256_file(&current_exe, "parity validator")?;
    let requirement_ids = dimension
        .requirements
        .iter()
        .map(|requirement| requirement.id.clone())
        .collect::<Vec<_>>();
    let receipt = ValidatorReceipt {
        schema: VALIDATOR_RECEIPT_SCHEMA.to_string(),
        campaign_id: loaded.contract.campaign_id.clone(),
        profile_id: PROFILE_ID.to_string(),
        profile_sha256: canonical_profile_sha256()?,
        dimension_id: dimension.id.clone(),
        requirement_ids,
        inventory_sha256: dimension.inventory.sha256.clone(),
        validator: ValidatorIdentity {
            id: flavor.validator_id().to_string(),
            kind: flavor.validator_kind(),
            path: current_exe.to_string_lossy().into_owned(),
            sha256: validator_sha,
        },
        subject: ReceiptSubject {
            ay_executable_sha256: Some(execution.ay_sha256),
            ay_shared_library_sha256: loaded
                .contract
                .subject
                .ay_shared_library
                .as_ref()
                .map(|artifact| artifact.sha256.clone()),
        },
        z3_binary_sha256: None,
        z3_shared_library_sha256: None,
        reference_inputs: vec![source.binding],
        auxiliary_tools: Vec::new(),
        source_provenance: None,
        resource_envelope: Some(execution.resource_envelope),
        exhaustive: true,
        result: execution.result,
        cases: execution.cases,
        case_results: execution.case_results,
    };
    let bytes = pretty_json(&receipt)?;
    atomic_write_new(&receipt_path, &bytes)?;
    let receipt_sha = sha256_bytes(&bytes);
    println!(
        "{}={} receipt={} sha256={}",
        flavor.cli_name(),
        if receipt.result == ValidatorResult::Pass {
            "PASS"
        } else {
            "FAIL"
        },
        output_relative,
        receipt_sha
    );
    println!(
        "attach to all {} rows: {{\"path\":\"{output_relative}\",\"sha256\":\"{receipt_sha}\"}}",
        dimension.requirements.len()
    );
    if !report.complete {
        println!(
            "note: the rest of the contract remains incomplete ({} existing blockers)",
            report.blockers.len()
        );
    }
    Ok(i32::from(receipt.result != ValidatorResult::Pass))
}

pub(super) fn validate_type_scope(
    receipt: &ValidatorReceipt,
    context: EvidenceContext<'_>,
) -> Result<(), String> {
    validate_and_replay(Flavor::TypeScope, receipt, context)
}

pub(super) fn validate_command_state(
    receipt: &ValidatorReceipt,
    context: EvidenceContext<'_>,
) -> Result<(), String> {
    validate_and_replay(Flavor::StateMachine, receipt, context)
}

fn validate_and_replay(
    flavor: Flavor,
    receipt: &ValidatorReceipt,
    context: EvidenceContext<'_>,
) -> Result<(), String> {
    if receipt.validator.kind != flavor.validator_kind()
        || context.dimension.id != flavor.dimension_id()
        || !receipt.exhaustive
        || receipt.z3_binary_sha256.is_some()
        || receipt.z3_shared_library_sha256.is_some()
        || !receipt.auxiliary_tools.is_empty()
        || receipt.source_provenance.is_some()
    {
        return Err(format!(
            "{} has invalid kind, dimension, exhaustive flag, or foreign bindings",
            flavor.validator_id()
        ));
    }
    let expected_requirement_ids = context
        .dimension
        .requirements
        .iter()
        .map(|requirement| requirement.id.clone())
        .collect::<Vec<_>>();
    if receipt.requirement_ids != expected_requirement_ids {
        return Err(format!(
            "{} does not cover the exact closed semantic inventory",
            flavor.validator_id()
        ));
    }
    let input = match receipt.reference_inputs.as_slice() {
        [input]
            if input.id == "smtlib-language"
                && input.cohort == SourceCohort::SmtlibLanguage
                && input.repository
                    == context
                        .contract
                        .profile
                        .standard
                        .language_sources
                        .repository
                && input.revision
                    == context.contract.profile.standard.language_sources.revision
                && input.selection_sha256
                    == context.contract.profile.standard.language_sources.sha256 =>
        {
            input
        }
        _ => {
            return Err(format!(
                "{} requires exactly the pinned SMT-LIB language snapshot",
                flavor.validator_id()
            ));
        }
    };

    if context.mode.replays_registered_validators() {
        let source = reference_inventory::load_bound_language_source(
            input,
            context.manifest_dir,
            &canonical_profile(),
        )?;
        let catalog = case_catalog(flavor, context.dimension, &source.files)?;
        validate_receipt_rows(flavor, receipt, &catalog)?;
        let envelope = receipt
            .resource_envelope
            .as_deref()
            .ok_or_else(|| format!("{} receipt has no resource envelope", flavor.cli_name()))?;
        let parsed = parse_resource_envelope(envelope)?;
        if parsed.jobs != 1 {
            return Err(format!(
                "{} receipts require a one-job resource envelope",
                flavor.cli_name()
            ));
        }
        let subject = context
            .contract
            .subject
            .ay_executable
            .as_ref()
            .ok_or_else(|| {
                format!(
                    "{} replay requires subject.ay_executable",
                    flavor.cli_name()
                )
            })?;
        let ay = artifact_path(context.manifest_dir, &subject.path);
        let live_source = LoadedLanguageSource {
            binding: input.clone(),
            files: source.files,
        };
        let live = execute(
            flavor,
            context.contract,
            context.dimension,
            &ay,
            &live_source,
            parsed.timeout,
            Some(envelope),
        )?;
        if receipt.result != live.result
            || receipt.cases != live.cases
            || receipt.case_results != live.case_results
        {
            return Err(format!(
                "{} receipt does not match a fresh authenticated executable replay",
                flavor.validator_id()
            ));
        }
    }
    Ok(())
}

fn execute(
    flavor: Flavor,
    contract: &Contract,
    dimension: &Dimension,
    ay_source: &Path,
    source: &LoadedLanguageSource,
    timeout: Duration,
    required_envelope: Option<&str>,
) -> Result<Execution, String> {
    if timeout.is_zero() || timeout > Duration::from_secs(3600) {
        return Err(format!(
            "{} timeout must be between 1ns and 3600 seconds",
            flavor.cli_name()
        ));
    }
    let subject = contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or_else(|| format!("{} requires subject.ay_executable", flavor.cli_name()))?;
    let staged = stage_authenticated_executable(ay_source, &subject.sha256, "AY executable")?;
    let catalog = case_catalog(flavor, dimension, &source.files)?;
    let repo_root = locate_repo_root()?;
    let resources = PlannedResources::plan(
        &repo_root,
        1,
        &format!("ay-z3-parity smtlib-conformance {}", flavor.cli_name()),
    )
    .map_err(|error| error.to_string())?;
    let resource_envelope = effective_execution_envelope(
        &resources.plan,
        ENFORCEMENT_RSS_WATCHDOG_V1,
        timeout.as_secs_f64(),
    )
    .map_err(|error| error.to_string())?;
    if let Some(expected) = required_envelope {
        if expected != resource_envelope {
            return Err(format!(
                "live {} replay resource envelope drift: expected {expected:?}, got {resource_envelope:?}",
                flavor.cli_name()
            ));
        }
    }

    let mut rows = Vec::with_capacity(catalog.len());
    for spec in &catalog {
        let output = resources
            .run_external_transcript(
                &staged.path,
                ["--quiet", "-in"],
                &spec.input,
                timeout,
                &format!("SMT-LIB {} case {}", flavor.cli_name(), spec.id),
            )
            .map_err(|error| error.to_string())?;
        rows.push(row_from_output(spec, output));
    }
    let post_sha = sha256_file(&staged.path, "staged AY after language semantic probes")?;
    if post_sha != subject.sha256 {
        return Err(format!(
            "authenticated AY bytes changed during {} probes",
            flavor.cli_name()
        ));
    }
    rows.sort_by(|left, right| left.id.cmp(&right.id));
    let mut expected_ids = catalog
        .iter()
        .map(|case| case.id.clone())
        .collect::<Vec<_>>();
    expected_ids.sort();
    let actual_ids = rows.iter().map(|row| row.id.clone()).collect::<Vec<_>>();
    if actual_ids != expected_ids {
        return Err(format!(
            "internal {} case inventory drift",
            flavor.cli_name()
        ));
    }
    let cases = case_counts_from_rows(&rows)?;
    Ok(Execution {
        ay_sha256: subject.sha256.clone(),
        resource_envelope,
        result: overall_validator_result(&rows),
        cases,
        case_results: rows,
    })
}

fn semantic_dimension(contract: &Contract, flavor: Flavor) -> Result<&Dimension, String> {
    contract
        .dimensions
        .iter()
        .find(|dimension| dimension.id == flavor.dimension_id())
        .ok_or_else(|| format!("closed {} dimension is missing", flavor.dimension_id()))
}

#[derive(Clone, Copy)]
struct TypePair {
    rule: &'static str,
    positive: &'static str,
    negative: &'static str,
}

const TYPE_PAIRS: &[TypePair] = &[
    TypePair {
        rule: "sort-symbol-resolution",
        positive: "(declare-sort U 0)\n(declare-const b Bool)\n(declare-const u U)",
        negative: "(declare-const x MissingSort)",
    },
    TypePair {
        rule: "sort-constructor-arity",
        positive: "(declare-sort Pair 2)\n(declare-const p (Pair Bool Int))",
        negative: "(declare-sort Pair 2)\n(declare-const p (Pair Bool))",
    },
    TypePair {
        rule: "variable-judgment",
        positive: "(declare-const x Bool)\n(assert x)",
        negative: "(assert free_x)",
    },
    TypePair {
        rule: "function-application-arity",
        positive: "(declare-fun f (Bool) Bool)\n(assert (f true))",
        negative: "(declare-fun f (Bool) Bool)\n(assert (f))",
    },
    TypePair {
        rule: "function-application-operands",
        positive: "(declare-fun f (Int) Bool)\n(assert (f 0))",
        negative: "(declare-fun f (Int) Bool)\n(assert (f true))",
    },
    TypePair {
        rule: "ambiguous-qualified-identifier",
        positive: "(declare-datatype List (par (T) ((nil) (cons (head T) (tail (List T))))))\n(declare-const xs (List Int))\n(assert (= xs (as nil (List Int))))",
        negative: "(declare-datatype List (par (T) ((nil) (cons (head T) (tail (List T))))))\n(declare-const xs (List Int))\n(assert (= xs nil))",
    },
    TypePair {
        rule: "formula-bool-sort",
        positive: "(assert (= 1 1))",
        negative: "(assert 1)",
    },
    TypePair {
        rule: "equality-common-sort",
        positive: "(assert (= true false))",
        negative: "(assert (= true 1))",
    },
    TypePair {
        rule: "ite-condition-and-branches",
        positive: "(assert (= (ite true 1 2) 1))",
        negative: "(assert (= (ite true 1 false) 1))",
    },
    TypePair {
        rule: "explicit-numeric-coercion",
        positive: "(assert (= (to_real 1) 1.0))",
        negative: "(assert (= (to_real 1.0) 1.0))",
    },
    TypePair {
        rule: "quantifier-binder",
        positive: "(assert (forall ((x Bool)) (= x x)))",
        negative: "(assert (forall ((x Bool)) 1))",
    },
    TypePair {
        rule: "binder-lexical-shadowing",
        positive: "(declare-const x Int)\n(assert (forall ((x Bool)) (= x x)))",
        negative: "(declare-const x Int)\n(assert (and (forall ((x Bool)) x) x))",
    },
    TypePair {
        rule: "theory-symbol-no-shadowing",
        positive: "(assert (forall ((user_name Bool)) user_name))",
        negative: "(assert (forall ((and Bool)) and))",
    },
    TypePair {
        rule: "let-simultaneous-scope",
        positive: "(declare-const x Int)\n(assert (= (let ((x 1) (y x)) y) x))",
        negative: "(assert (= (let ((x 1) (y x)) y) 1))",
    },
    TypePair {
        rule: "let-distinct-binders",
        positive: "(assert (= (let ((x 1) (y 2)) (+ x y)) 3))",
        negative: "(assert (= (let ((x 1) (x 2)) x) 2))",
    },
    TypePair {
        rule: "match-exhaustiveness",
        positive: "(declare-datatype O ((none) (some (val Bool))))\n(declare-const o O)\n(assert (match o ((none true) ((some x) x))))",
        negative: "(declare-datatype O ((none) (some (val Bool))))\n(declare-const o O)\n(assert (match o ((none true))))",
    },
    TypePair {
        rule: "match-pattern-scope",
        positive: "(declare-datatype O ((none) (some (val Bool))))\n(declare-const o O)\n(assert (match o ((none false) ((some x) x))))",
        negative: "(declare-datatype O ((none) (some (val Bool))))\n(declare-const o O)\n(assert (match o ((none x) ((some y) y))))",
    },
    TypePair {
        rule: "match-branch-common-sort",
        positive: "(declare-datatype O ((none) (some (val Bool))))\n(declare-const o O)\n(assert (= (match o ((none 0) ((some x) (ite x 1 2)))) 0))",
        negative: "(declare-datatype O ((none) (some (val Bool))))\n(declare-const o O)\n(assert (match o ((none true) ((some x) 0))))",
    },
    TypePair {
        rule: "annotation-sort-preservation",
        positive: "(assert (! true :named annotation_name))",
        negative: "(assert (! 1 :named annotation_name))",
    },
    TypePair {
        rule: "namespace-separation",
        positive: "(declare-sort Same 0)\n(declare-const Same Bool)",
        negative: "(declare-sort Same 0)\n(declare-sort Same 0)",
    },
    TypePair {
        rule: "sort-declaration-collision",
        positive: "(declare-sort S 0)\n(declare-sort T 0)",
        negative: "(declare-sort S 0)\n(declare-sort S 1)",
    },
    TypePair {
        rule: "function-declaration-collision",
        positive: "(declare-fun f (Bool) Bool)\n(declare-fun g (Bool) Bool)",
        negative: "(declare-fun f (Bool) Bool)\n(declare-fun f (Int) Int)",
    },
    TypePair {
        rule: "definition-body-result",
        positive: "(define-fun f ((x Int)) Int (+ x 1))",
        negative: "(define-fun f ((x Int)) Bool (+ x 1))",
    },
    TypePair {
        rule: "nonrecursive-definition",
        positive: "(define-fun f ((x Int)) Int (+ x 1))",
        negative: "(define-fun f ((x Int)) Int (f x))",
    },
    TypePair {
        rule: "mutual-recursive-definition",
        positive: "(define-funs-rec ((even ((x Int)) Bool) (odd ((x Int)) Bool)) ((ite (= x 0) true (odd (- x 1))) (ite (= x 0) false (even (- x 1)))))",
        negative: "(define-funs-rec ((f ((x Int)) Bool) (g ((x Int)) Bool)) ((g x) 0))",
    },
    TypePair {
        rule: "sort-alias-parameter-scope",
        positive: "(define-sort Pair (A B) (Array A B))\n(declare-const p (Pair Int Bool))",
        negative: "(define-sort Bad (A) (Array A Missing))",
    },
    TypePair {
        rule: "global-sort-parameter",
        positive: "(declare-sort-parameter P)\n(declare-fun id (P) P)\n(assert (forall ((x P)) (= (id x) (id x))))",
        negative: "(declare-sort-parameter P)\n(define-sort Bad () P)",
    },
    TypePair {
        rule: "datatype-parameter-scope",
        positive: "(declare-datatype Box (par (T) ((box (unbox T)))))\n(declare-const b (Box Int))",
        negative: "(declare-datatype Box (par (T) ((box (unbox U)))))",
    },
    TypePair {
        rule: "datatype-symbol-collisions",
        positive: "(declare-datatypes ((A 0) (B 0)) (((a)) ((b))))",
        negative: "(declare-datatypes ((A 0) (B 0)) (((same)) ((same))))",
    },
    TypePair {
        rule: "scoped-declaration-lifetime",
        positive: "(push 1)\n(declare-const scoped Bool)\n(pop 1)\n(declare-const scoped Int)",
        negative: "(push 1)\n(declare-const scoped Bool)\n(pop 1)\n(assert scoped)",
    },
    TypePair {
        rule: "global-declaration-lifetime",
        positive: "(set-option :global-declarations true)\n(push 1)\n(declare-const global_x Bool)\n(pop 1)\n(assert global_x)\n(reset-assertions)\n(assert global_x)",
        negative: "(set-option :global-declarations true)\n(declare-const global_x Bool)\n(reset)\n(set-logic ALL)\n(assert global_x)",
    },
    TypePair {
        rule: "reserved-user-symbol-prefixes",
        positive: "(declare-const ordinary_name Bool)",
        negative: "(declare-const .reserved Bool)",
    },
];

fn case_catalog(
    flavor: Flavor,
    dimension: &Dimension,
    files: &[LanguageSourceFile],
) -> Result<Vec<CaseSpec>, String> {
    let bound = authenticate_rules(dimension, files)?
        .into_iter()
        .map(|rule| (rule.requirement_id.clone(), rule))
        .collect::<BTreeMap<_, _>>();
    let mut cases = match flavor {
        Flavor::TypeScope => type_case_catalog(&bound)?,
        Flavor::StateMachine => state_case_catalog(&bound)?,
    };
    cases.sort_by(|left, right| left.id.cmp(&right.id));
    let mut seen = BTreeSet::new();
    for case in &cases {
        if !seen.insert(case.id.clone()) {
            return Err(format!(
                "duplicate {} case id {}",
                flavor.cli_name(),
                case.id
            ));
        }
        if !bound.contains_key(&case.requirement_id) {
            return Err(format!(
                "{} case {} names a non-canonical requirement",
                flavor.cli_name(),
                case.id
            ));
        }
    }
    for requirement in bound.keys() {
        if !cases.iter().any(|case| &case.requirement_id == requirement) {
            return Err(format!(
                "{} has no transcript for source rule {}",
                flavor.cli_name(),
                requirement
            ));
        }
    }
    Ok(cases)
}

fn type_case_catalog(bound: &BTreeMap<String, BoundRule>) -> Result<Vec<CaseSpec>, String> {
    if TYPE_PAIRS.len() != TYPE_RULES.len() {
        return Err("type/scope witness pairs do not cover the exact source rule list".to_string());
    }
    let expected = TYPE_RULES
        .iter()
        .map(|rule| rule.id)
        .collect::<BTreeSet<_>>();
    let actual = TYPE_PAIRS
        .iter()
        .map(|pair| pair.rule)
        .collect::<BTreeSet<_>>();
    if actual != expected || actual.len() != TYPE_PAIRS.len() {
        return Err("type/scope witness pair identities drifted".to_string());
    }
    let mut cases = Vec::with_capacity(TYPE_PAIRS.len() * 2);
    for pair in TYPE_PAIRS {
        let requirement_id = format!("{TYPE_SCOPE_DIMENSION}.{}", pair.rule);
        let source = bound
            .get(&requirement_id)
            .ok_or_else(|| format!("missing authenticated type rule {requirement_id}"))?;
        let positive_input = format!(
            "(set-logic ALL)\n{}\n(echo \"{TYPE_MARKER}\")\n(exit)\n",
            pair.positive
        );
        cases.push(CaseSpec {
            id: format!("type.{}.positive", pair.rule),
            requirement_id: requirement_id.clone(),
            source_sha256: source.source_sha256.clone(),
            input: positive_input.into_bytes(),
            status: ExpectedStatus::Accepted,
            output: OutputExpectation::Accepted {
                marker: Some(TYPE_MARKER),
                required_lines: Vec::new(),
                verdict_count: Some(0),
            },
        });
        let negative_input = format!(
            "(set-logic ALL)\n{}\n(echo \"{TYPE_MARKER}\")\n(exit)\n",
            pair.negative
        );
        cases.push(CaseSpec {
            id: format!("type.{}.negative", pair.rule),
            requirement_id,
            source_sha256: source.source_sha256.clone(),
            input: negative_input.into_bytes(),
            status: ExpectedStatus::Rejected,
            output: OutputExpectation::Rejected {
                marker: TYPE_MARKER,
                verdict_count: 0,
            },
        });
    }
    Ok(cases)
}

fn state_case_catalog(bound: &BTreeMap<String, BoundRule>) -> Result<Vec<CaseSpec>, String> {
    let command_names = COMMAND_RULES
        .iter()
        .map(|rule| rule.name)
        .collect::<BTreeSet<_>>();
    let standard_names = SMTLIB_COMMANDS.iter().copied().collect::<BTreeSet<_>>();
    if command_names != standard_names || command_names.len() != COMMAND_RULES.len() {
        return Err(
            "command-state transition rows are not exactly the 32 standard commands".to_string(),
        );
    }
    let mut cases = Vec::with_capacity(COMMAND_RULES.len() * Mode::ALL.len() + 24);
    for rule in COMMAND_RULES {
        let requirement_id = format!("{STATE_MACHINE_DIMENSION}.{}", rule.name);
        let source = bound
            .get(&requirement_id)
            .ok_or_else(|| format!("missing authenticated command-state rule {requirement_id}"))?;
        for mode in Mode::ALL {
            let allowed = rule.allowed.contains(&mode);
            let mut input = mode_prelude(mode, rule);
            input.push_str(rule.command);
            input.push('\n');
            if rule.result_class != ResultClass::Exit {
                input.push_str(&format!("(echo \"{STATE_MARKER}\")\n(exit)\n"));
            }
            let prelude_verdicts = usize::from(matches!(mode, Mode::Sat | Mode::Unsat));
            let verdict_count =
                prelude_verdicts + usize::from(allowed && rule.result_class == ResultClass::Check);
            let output = if allowed {
                let mut required_lines = Vec::new();
                if rule.result_class == ResultClass::Echo {
                    required_lines.push(STATE_PROBE_MARKER.to_string());
                }
                OutputExpectation::Accepted {
                    marker: (rule.result_class != ResultClass::Exit).then_some(STATE_MARKER),
                    required_lines,
                    verdict_count: Some(verdict_count),
                }
            } else {
                OutputExpectation::Rejected {
                    marker: STATE_MARKER,
                    verdict_count,
                }
            };
            cases.push(CaseSpec {
                id: format!("state.command.{}.{}", rule.name, mode.id()),
                requirement_id: requirement_id.clone(),
                source_sha256: source.source_sha256.clone(),
                input: input.into_bytes(),
                status: if allowed {
                    ExpectedStatus::Accepted
                } else {
                    ExpectedStatus::Rejected
                },
                output,
            });
        }
    }

    push_effect_cases(&mut cases, bound)?;
    Ok(cases)
}

fn mode_prelude(mode: Mode, rule: &CommandRule) -> String {
    let mut input = String::from(
        "(set-option :produce-assertions true)\n\
         (set-option :produce-assignments true)\n\
         (set-option :produce-models true)\n\
         (set-option :produce-proofs true)\n\
         (set-option :produce-unsat-assumptions true)\n\
         (set-option :produce-unsat-cores true)\n",
    );
    if mode == Mode::Start {
        return input;
    }
    input.push_str("(set-logic ALL)\n");
    if rule.name == "pop" {
        input.push_str("(push 1)\n");
    }
    match mode {
        Mode::Start | Mode::Assert => {}
        Mode::Sat => {
            input.push_str("(assert (! true :named state_named_true))\n(check-sat)\n");
        }
        Mode::Unsat if rule.name == "get-unsat-assumptions" => {
            input.push_str(
                "(declare-const state_assumption Bool)\n\
                 (check-sat-assuming (state_assumption (not state_assumption)))\n",
            );
        }
        Mode::Unsat => {
            input.push_str("(assert (! false :named state_named_false))\n(check-sat)\n");
        }
    }
    input
}

fn push_effect_cases(
    cases: &mut Vec<CaseSpec>,
    bound: &BTreeMap<String, BoundRule>,
) -> Result<(), String> {
    push_effect_accepted(
        cases,
        bound,
        "initial-mode-and-set-logic",
        "positive",
        "(set-logic ALL)\n(assert true)",
        &[],
        0,
    )?;
    push_effect_rejected(
        cases,
        bound,
        "initial-mode-and-set-logic",
        "second-set-logic",
        "(set-logic ALL)\n(set-logic QF_UF)",
        0,
    )?;
    push_effect_rejected(
        cases,
        bound,
        "error-atomicity-and-recovery",
        "declaration-collision",
        "(set-logic ALL)\n(declare-const atomic_x Bool)\n(declare-const atomic_x Bool)\n(assert atomic_x)\n(check-sat)",
        1,
    )?;
    push_effect_rejected(
        cases,
        bound,
        "error-atomicity-and-recovery",
        "pop-underflow",
        "(set-logic ALL)\n(pop 1)\n(assert true)\n(check-sat)",
        1,
    )?;
    push_effect_accepted(
        cases,
        bound,
        "push-pop-stack-effects",
        "assertion-lifetime",
        "(set-logic ALL)\n(assert true)\n(push 1)\n(assert false)\n(check-sat)\n(pop 1)\n(check-sat)",
        &["unsat", "sat"],
        2,
    )?;
    push_effect_rejected(
        cases,
        bound,
        "push-pop-stack-effects",
        "underflow-atomic",
        "(set-logic ALL)\n(push 1)\n(pop 2)\n(pop 1)\n(check-sat)",
        1,
    )?;
    push_effect_accepted(
        cases,
        bound,
        "reset-assertions-effects",
        "clear-local-context",
        "(set-option :produce-assertions true)\n(set-logic ALL)\n(declare-const reset_x Bool)\n(assert false)\n(push 1)\n(assert false)\n(reset-assertions)\n(declare-const reset_x Int)\n(get-assertions)\n(check-sat)",
        &["()", "sat"],
        1,
    )?;
    push_effect_accepted(
        cases,
        bound,
        "reset-assertions-effects",
        "preserve-options",
        "(set-option :produce-assertions true)\n(set-logic ALL)\n(assert true)\n(reset-assertions)\n(get-assertions)",
        &["()"],
        0,
    )?;
    push_effect_accepted(
        cases,
        bound,
        "reset-complete-effects",
        "fresh-state",
        "(set-option :global-declarations true)\n(set-logic ALL)\n(declare-const reset_global Bool)\n(reset)\n(get-option :global-declarations)\n(set-logic ALL)\n(declare-const reset_global Int)",
        &["false"],
        0,
    )?;
    push_effect_rejected(
        cases,
        bound,
        "reset-complete-effects",
        "returns-start-mode",
        "(set-logic ALL)\n(reset)\n(assert true)",
        0,
    )?;
    push_effect_accepted(
        cases,
        bound,
        "global-declarations-effects",
        "survive-stack-reset",
        "(set-option :global-declarations true)\n(set-logic ALL)\n(push 1)\n(declare-const persistent Bool)\n(pop 1)\n(assert persistent)\n(reset-assertions)\n(assert persistent)",
        &[],
        0,
    )?;
    push_effect_rejected(
        cases,
        bound,
        "global-declarations-effects",
        "removed-by-reset",
        "(set-option :global-declarations true)\n(set-logic ALL)\n(declare-const persistent Bool)\n(reset)\n(set-logic ALL)\n(assert persistent)",
        0,
    )?;
    push_effect_accepted(
        cases,
        bound,
        "temporary-assumptions",
        "query-local",
        "(set-logic ALL)\n(check-sat-assuming (false))\n(check-sat)",
        &["unsat", "sat"],
        2,
    )?;
    push_effect_rejected(
        cases,
        bound,
        "temporary-assumptions",
        "bool-typing",
        "(set-logic ALL)\n(check-sat-assuming (1))\n(check-sat)",
        1,
    )?;
    push_effect_rejected(
        cases,
        bound,
        "sat-artifact-epoch",
        "mutation-invalidates",
        "(set-option :produce-models true)\n(set-logic ALL)\n(check-sat)\n(get-model)\n(assert true)\n(get-model)",
        1,
    )?;
    push_effect_rejected(
        cases,
        bound,
        "sat-artifact-epoch",
        "later-query-invalidates",
        "(set-option :produce-models true)\n(set-logic ALL)\n(check-sat)\n(check-sat-assuming (false))\n(get-model)",
        2,
    )?;
    push_effect_rejected(
        cases,
        bound,
        "unsat-artifact-epoch",
        "mutation-invalidates",
        "(set-option :produce-unsat-cores true)\n(set-logic ALL)\n(assert (! false :named epoch_false))\n(check-sat)\n(get-unsat-core)\n(push 1)\n(get-unsat-core)",
        1,
    )?;
    push_effect_rejected(
        cases,
        bound,
        "unsat-artifact-epoch",
        "later-query-invalidates",
        "(set-option :produce-unsat-cores true)\n(set-logic ALL)\n(assert (! false :named epoch_false))\n(check-sat)\n(reset-assertions)\n(check-sat)\n(get-unsat-core)",
        2,
    )?;
    push_effect_exact(
        cases,
        bound,
        "success-response-timing",
        "immediate",
        "(set-option :print-success true)\n(set-option :print-success false)\n(echo \"__ay_command_state_completed__\")\n(exit)\n",
        &format!("success\n{STATE_MARKER}\n"),
        "",
        0,
    )?;
    push_effect_exact(
        cases,
        bound,
        "regular-output-channel",
        "stderr-routing",
        "(set-option :print-success true)\n(set-option :regular-output-channel \"stderr\")\n(echo \"__ay_regular_routed__\")\n(set-option :regular-output-channel \"stdout\")\n(set-option :print-success false)\n(echo \"__ay_command_state_completed__\")\n(exit)\n",
        &format!("success\nsuccess\n{STATE_MARKER}\n"),
        "success\n__ay_regular_routed__\n",
        0,
    )?;
    push_effect_accepted(
        cases,
        bound,
        "diagnostic-output-channel",
        "independent-option",
        "(set-option :diagnostic-output-channel \"stdout\")\n(get-option :diagnostic-output-channel)",
        &["stdout"],
        0,
    )?;
    push_effect_rejected(
        cases,
        bound,
        "diagnostic-output-channel",
        "regular-error-separation",
        "(set-option :diagnostic-output-channel \"stderr\")\n(set-logic ALL)\n(assert 1)",
        0,
    )?;
    push_effect_accepted(
        cases,
        bound,
        "start-only-options",
        "accepted-in-start",
        "(set-option :produce-models true)\n(set-logic ALL)\n(check-sat)\n(get-model)",
        &["sat"],
        1,
    )?;
    push_effect_rejected(
        cases,
        bound,
        "start-only-options",
        "rejected-in-assert",
        "(set-logic ALL)\n(set-option :produce-models true)\n(check-sat)\n(get-model)",
        1,
    )?;
    push_effect_rejected(
        cases,
        bound,
        "poison-and-reset-recovery",
        "discarded-problem-command",
        "(set-option :diagnostic-output-channel \"stdout\")\n(set-logic ALL)\n(include \"definitely-missing-ay-conformance-file.smt2\")\n(check-sat)\n(reset)\n(set-logic ALL)\n(check-sat)",
        2,
    )?;
    push_effect_exact(
        cases,
        bound,
        "exit-any-mode",
        "success-before-exit",
        "(set-option :print-success true)\n(exit)\n(echo \"must-not-run\")\n",
        "success\nsuccess\n",
        "",
        0,
    )?;
    Ok(())
}

fn push_effect_accepted(
    cases: &mut Vec<CaseSpec>,
    bound: &BTreeMap<String, BoundRule>,
    rule: &str,
    variant: &str,
    body: &str,
    required_lines: &[&str],
    verdict_count: usize,
) -> Result<(), String> {
    let requirement_id = format!("{STATE_MACHINE_DIMENSION}.{rule}");
    let source = bound
        .get(&requirement_id)
        .ok_or_else(|| format!("missing authenticated command-state effect {requirement_id}"))?;
    let input = format!("{body}\n(echo \"{STATE_MARKER}\")\n(exit)\n");
    cases.push(CaseSpec {
        id: format!("state.effect.{rule}.{variant}"),
        requirement_id,
        source_sha256: source.source_sha256.clone(),
        input: input.into_bytes(),
        status: ExpectedStatus::Accepted,
        output: OutputExpectation::Accepted {
            marker: Some(STATE_MARKER),
            required_lines: required_lines
                .iter()
                .map(|line| (*line).to_string())
                .collect(),
            verdict_count: Some(verdict_count),
        },
    });
    Ok(())
}

fn push_effect_rejected(
    cases: &mut Vec<CaseSpec>,
    bound: &BTreeMap<String, BoundRule>,
    rule: &str,
    variant: &str,
    body: &str,
    verdict_count: usize,
) -> Result<(), String> {
    let requirement_id = format!("{STATE_MACHINE_DIMENSION}.{rule}");
    let source = bound
        .get(&requirement_id)
        .ok_or_else(|| format!("missing authenticated command-state effect {requirement_id}"))?;
    let input = format!("{body}\n(echo \"{STATE_MARKER}\")\n(exit)\n");
    cases.push(CaseSpec {
        id: format!("state.effect.{rule}.{variant}"),
        requirement_id,
        source_sha256: source.source_sha256.clone(),
        input: input.into_bytes(),
        status: ExpectedStatus::Rejected,
        output: OutputExpectation::Rejected {
            marker: STATE_MARKER,
            verdict_count,
        },
    });
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn push_effect_exact(
    cases: &mut Vec<CaseSpec>,
    bound: &BTreeMap<String, BoundRule>,
    rule: &str,
    variant: &str,
    input: &str,
    stdout: &str,
    stderr: &str,
    exit_code: i32,
) -> Result<(), String> {
    let requirement_id = format!("{STATE_MACHINE_DIMENSION}.{rule}");
    let source = bound
        .get(&requirement_id)
        .ok_or_else(|| format!("missing authenticated command-state effect {requirement_id}"))?;
    cases.push(CaseSpec {
        id: format!("state.effect.{rule}.{variant}"),
        requirement_id,
        source_sha256: source.source_sha256.clone(),
        input: input.as_bytes().to_vec(),
        status: if exit_code == 0 {
            ExpectedStatus::Accepted
        } else {
            ExpectedStatus::Rejected
        },
        output: OutputExpectation::Exact {
            stdout: stdout.to_string(),
            stderr: stderr.to_string(),
            exit_code,
        },
    });
    Ok(())
}

fn row_from_output(spec: &CaseSpec, output: GuardedTranscriptOutput) -> ValidatorCase {
    let exit_code = output.status.as_ref().and_then(|status| status.code());
    let stdout_utf8 = String::from_utf8(output.stdout);
    let stderr_utf8 = String::from_utf8(output.stderr);
    let streams_valid = stdout_utf8.is_ok() && stderr_utf8.is_ok();
    let stdout = stdout_utf8.map_or_else(
        |error| String::from_utf8_lossy(error.as_bytes()).into_owned(),
        |value| value,
    );
    let stderr = stderr_utf8.map_or_else(
        |error| String::from_utf8_lossy(error.as_bytes()).into_owned(),
        |value| value,
    );
    let process = ProcessObservation {
        stdin_complete: output.stdin_complete,
        timed_out: output.timed_out,
        memout: output.memout,
        stdout_truncated: output.stdout_truncated,
        stderr_truncated: output.stderr_truncated,
    };
    let (outcome, observed) =
        evaluate_observation(spec, exit_code, &process, &stdout, &stderr, streams_valid);
    ValidatorCase {
        id: spec.id.clone(),
        input_sha256: sha256_bytes(&spec.input),
        expected: spec.expected(),
        observed,
        stdout: Some(stdout),
        stderr: Some(stderr),
        exit_code,
        process: Some(process),
        outcome,
    }
}

fn evaluate_observation(
    spec: &CaseSpec,
    exit_code: Option<i32>,
    process: &ProcessObservation,
    stdout: &str,
    stderr: &str,
    streams_valid: bool,
) -> (ValidatorCaseOutcome, String) {
    let mut failures = Vec::new();
    let outcome = if process.memout {
        failures.push("memout");
        ValidatorCaseOutcome::Memout
    } else if process.timed_out {
        failures.push("timeout");
        ValidatorCaseOutcome::Timeout
    } else if !process.stdin_complete
        || process.stdout_truncated
        || process.stderr_truncated
        || !streams_valid
    {
        if !process.stdin_complete {
            failures.push("stdin-incomplete");
        }
        if process.stdout_truncated {
            failures.push("stdout-truncated");
        }
        if process.stderr_truncated {
            failures.push("stderr-truncated");
        }
        if !streams_valid {
            failures.push("non-utf8-stream");
        }
        ValidatorCaseOutcome::Fail
    } else if exit_code.is_none() {
        failures.push("no-exit-code");
        ValidatorCaseOutcome::Crash
    } else {
        validate_semantic_observation(spec, exit_code, stdout, stderr, &mut failures);
        if failures.is_empty() {
            ValidatorCaseOutcome::Pass
        } else {
            ValidatorCaseOutcome::Fail
        }
    };
    let detail = if failures.is_empty() {
        "match".to_string()
    } else {
        failures.join(",")
    };
    let observed = format!(
        "exit={exit_code:?};stdin-complete={};timeout={};memout={};stdout-truncated={};stderr-truncated={};streams-utf8={streams_valid};stdout-sha256={};stderr-sha256={};semantic={detail}",
        process.stdin_complete,
        process.timed_out,
        process.memout,
        process.stdout_truncated,
        process.stderr_truncated,
        sha256_bytes(stdout.as_bytes()),
        sha256_bytes(stderr.as_bytes()),
    );
    (outcome, observed)
}

fn validate_semantic_observation(
    spec: &CaseSpec,
    exit_code: Option<i32>,
    stdout: &str,
    stderr: &str,
    failures: &mut Vec<&'static str>,
) {
    let lines = stdout.lines().collect::<Vec<_>>();
    match &spec.output {
        OutputExpectation::Exact {
            stdout: expected_stdout,
            stderr: expected_stderr,
            exit_code: expected_exit,
        } => {
            if exit_code != Some(*expected_exit) {
                failures.push("exit-class");
            }
            if stdout != expected_stdout {
                failures.push("stdout-exact");
            }
            if stderr != expected_stderr {
                failures.push("stderr-exact");
            }
        }
        OutputExpectation::Accepted {
            marker,
            required_lines,
            verdict_count,
        } => {
            if exit_code != Some(0) {
                failures.push("exit-class");
            }
            if !stderr.is_empty() {
                failures.push("stderr-nonempty");
            }
            if lines.iter().any(|line| line.starts_with("(error ")) {
                failures.push("unexpected-error");
            }
            if lines.iter().any(|line| *line == "unsupported") {
                failures.push("unsupported");
            }
            if let Some(marker) = marker {
                if lines.iter().filter(|line| **line == *marker).count() != 1 {
                    failures.push("completion-marker");
                }
            }
            if required_lines
                .iter()
                .any(|required| !lines.iter().any(|line| *line == required))
            {
                failures.push("required-output-line");
            }
            if let Some(expected) = verdict_count {
                if count_verdicts(&lines) != *expected {
                    failures.push("verdict-count");
                }
            }
        }
        OutputExpectation::Rejected {
            marker,
            verdict_count,
        } => {
            if exit_code != Some(1) {
                failures.push("exit-class");
            }
            if !stderr.is_empty() {
                failures.push("stderr-nonempty");
            }
            if !lines.iter().any(|line| line.starts_with("(error \"")) {
                failures.push("missing-error");
            }
            if lines.iter().filter(|line| **line == *marker).count() != 1 {
                failures.push("recovery-marker");
            }
            if lines.iter().any(|line| *line == "unsupported") {
                failures.push("unsupported-instead-of-error");
            }
            if count_verdicts(&lines) != *verdict_count {
                failures.push("verdict-count");
            }
        }
    }
}

fn count_verdicts(lines: &[&str]) -> usize {
    lines
        .iter()
        .filter(|line| matches!(**line, "sat" | "unsat" | "unknown"))
        .count()
}

fn validate_receipt_rows(
    flavor: Flavor,
    receipt: &ValidatorReceipt,
    catalog: &[CaseSpec],
) -> Result<(), String> {
    if receipt.case_results.len() != catalog.len() {
        return Err(format!(
            "{} has {} rows; exact catalog has {}",
            flavor.validator_id(),
            receipt.case_results.len(),
            catalog.len()
        ));
    }
    for (row, spec) in receipt.case_results.iter().zip(catalog) {
        let (Some(process), Some(stdout), Some(stderr)) = (
            row.process.as_ref(),
            row.stdout.as_deref(),
            row.stderr.as_deref(),
        ) else {
            return Err(format!(
                "{} row {} lacks a guarded raw transcript",
                flavor.validator_id(),
                spec.id
            ));
        };
        if row.id != spec.id
            || row.input_sha256 != sha256_bytes(&spec.input)
            || row.expected != spec.expected()
        {
            return Err(format!(
                "{} row {} is not bound to the closed source/case catalog",
                flavor.validator_id(),
                spec.id
            ));
        }
        if row.outcome == ValidatorCaseOutcome::Pass {
            let (derived_outcome, derived_observed) =
                evaluate_observation(spec, row.exit_code, process, stdout, stderr, true);
            if derived_outcome != ValidatorCaseOutcome::Pass || row.observed != derived_observed {
                return Err(format!(
                    "{} row {} claims pass without its required raw transcript",
                    flavor.validator_id(),
                    row.id
                ));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn command_transition_rows_are_exactly_the_standard_commands() {
        assert_eq!(COMMAND_RULES.len(), SMTLIB_COMMANDS.len());
        assert_eq!(
            COMMAND_RULES
                .iter()
                .map(|rule| rule.name)
                .collect::<BTreeSet<_>>(),
            SMTLIB_COMMANDS.iter().copied().collect::<BTreeSet<_>>()
        );
    }

    #[test]
    fn type_pairs_are_bijective_with_source_rules() {
        assert_eq!(TYPE_PAIRS.len(), TYPE_RULES.len());
        assert_eq!(
            TYPE_PAIRS
                .iter()
                .map(|pair| pair.rule)
                .collect::<BTreeSet<_>>(),
            TYPE_RULES
                .iter()
                .map(|rule| rule.id)
                .collect::<BTreeSet<_>>()
        );
    }

    #[test]
    fn accepted_and_rejected_outputs_are_rederived() {
        let process = ProcessObservation {
            stdin_complete: true,
            timed_out: false,
            memout: false,
            stdout_truncated: false,
            stderr_truncated: false,
        };
        let accepted = CaseSpec {
            id: "accepted".to_string(),
            requirement_id: "row".to_string(),
            source_sha256: "a".repeat(64),
            input: Vec::new(),
            status: ExpectedStatus::Accepted,
            output: OutputExpectation::Accepted {
                marker: Some(TYPE_MARKER),
                required_lines: Vec::new(),
                verdict_count: Some(0),
            },
        };
        assert_eq!(
            evaluate_observation(
                &accepted,
                Some(0),
                &process,
                &format!("{TYPE_MARKER}\n"),
                "",
                true
            )
            .0,
            ValidatorCaseOutcome::Pass
        );
        let rejected = CaseSpec {
            id: "rejected".to_string(),
            requirement_id: "row".to_string(),
            source_sha256: "b".repeat(64),
            input: Vec::new(),
            status: ExpectedStatus::Rejected,
            output: OutputExpectation::Rejected {
                marker: TYPE_MARKER,
                verdict_count: 0,
            },
        };
        assert_eq!(
            evaluate_observation(
                &rejected,
                Some(1),
                &process,
                &format!("(error \"bad\")\n{TYPE_MARKER}\n"),
                "",
                true
            )
            .0,
            ValidatorCaseOutcome::Pass
        );
    }
}
