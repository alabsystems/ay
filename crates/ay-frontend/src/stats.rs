// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Frontend-level SMT formula statistics.
//!
//! These statistics are computed from parsed SMT-LIB commands before
//! elaboration/solving. They are lightweight and deterministic.

use std::collections::BTreeMap;

use crate::command::{Command, DatatypeDec, QualifiedIdentifier, Sort, SygusGrammar, Term};
use crate::sexp::{PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE};

/// Parsed-formula statistics collected from SMT-LIB commands.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct FormulaStats {
    /// Number of parsed commands.
    pub commands: u64,
    /// Number of parsed term AST nodes.
    pub terms: u64,
    /// Sort occurrence counts keyed by sort constructor/name.
    pub sort_distribution: BTreeMap<String, u64>,
    /// Theory/operator usage counts keyed by theory family.
    pub theory_usage: BTreeMap<String, u64>,
}

impl FormulaStats {
    /// Build frontend statistics from a full parsed command stream.
    #[must_use]
    pub fn from_commands(commands: &[Command]) -> Self {
        let mut stats = Self::default();
        for command in commands {
            stats.observe_command(command);
        }
        stats
    }

    /// Observe one command and update counters.
    pub fn observe_command(&mut self, command: &Command) {
        self.commands += 1;
        match command {
            Command::DeclareSort(name, _) => self.bump_sort(name),
            Command::DefineSort(_, _, sort) => self.collect_sort(sort),
            Command::DeclareDatatype(_, dt) => {
                self.bump_theory("datatypes");
                self.collect_datatype(dt);
            }
            Command::DeclareDatatypes(sort_decls, datatypes) => {
                self.observe_datatypes(sort_decls, datatypes);
            }
            Command::DeclareFun(_, args, ret) => self.observe_fun_sig(args, ret),
            Command::DeclareConst(_, sort) => self.collect_sort(sort),
            Command::DeclareVar(_, sort) => {
                self.bump_theory("sygus");
                self.collect_sort(sort);
            }
            Command::DefineFun(_, bindings, ret, body)
            | Command::DefineFunRec(_, bindings, ret, body) => {
                self.observe_fun_def(bindings, ret, body);
            }
            Command::DefineFunsRec(declarations, bodies) => {
                self.observe_funs_rec(declarations, bodies);
            }
            Command::SynthFun(_, bindings, ret, grammar) => {
                self.bump_theory("sygus");
                self.observe_fun_sig_from_bindings(bindings, ret);
                if let Some(grammar) = grammar {
                    self.observe_sygus_grammar(grammar);
                }
            }
            Command::SynthInv(_, bindings, grammar) => {
                self.bump_theory("sygus");
                for (_, sort) in bindings {
                    self.collect_sort(sort);
                }
                self.bump_sort("Bool");
                if let Some(grammar) = grammar {
                    self.observe_sygus_grammar(grammar);
                }
            }
            Command::SygusConstraint(term) => {
                self.bump_theory("sygus");
                self.collect_term(term);
            }
            Command::InvConstraint(_, _, _, _) | Command::CheckSynth => {
                self.bump_theory("sygus");
            }
            Command::Assert(term)
            | Command::Maximize(term)
            | Command::Minimize(term)
            | Command::Eval(term)
            | Command::Simplify(term) => self.collect_term(term),
            Command::CheckSatAssuming(terms) => {
                for t in terms {
                    self.collect_term(t);
                }
            }
            Command::GetValue(terms) => {
                for (_, t) in terms {
                    self.collect_term(t);
                }
            }
            _ => {}
        }
    }

    fn observe_datatypes(
        &mut self,
        sort_decls: &[crate::command::SortDec],
        datatypes: &[DatatypeDec],
    ) {
        self.bump_theory("datatypes");
        for s in sort_decls {
            self.bump_sort(&s.name);
        }
        for dt in datatypes {
            self.collect_datatype(dt);
        }
    }

    fn observe_fun_sig(&mut self, args: &[Sort], ret: &Sort) {
        for sort in args {
            self.collect_sort(sort);
        }
        self.collect_sort(ret);
    }

    fn observe_fun_sig_from_bindings(&mut self, bindings: &[(String, Sort)], ret: &Sort) {
        for (_, sort) in bindings {
            self.collect_sort(sort);
        }
        self.collect_sort(ret);
    }

    fn observe_fun_def(&mut self, bindings: &[(String, Sort)], ret: &Sort, body: &Term) {
        for (_, sort) in bindings {
            self.collect_sort(sort);
        }
        self.collect_sort(ret);
        self.collect_term(body);
    }

    fn observe_funs_rec(
        &mut self,
        declarations: &[crate::command::FuncDeclaration],
        bodies: &[Term],
    ) {
        for (_, bindings, ret) in declarations {
            for (_, sort) in bindings {
                self.collect_sort(sort);
            }
            self.collect_sort(ret);
        }
        for body in bodies {
            self.collect_term(body);
        }
    }

    fn observe_sygus_grammar(&mut self, grammar: &SygusGrammar) {
        for rule in &grammar.nonterminals {
            self.collect_sort(&rule.sort);
        }
    }

    fn collect_datatype(&mut self, datatype: &DatatypeDec) {
        for constructor in &datatype.constructors {
            for selector in &constructor.selectors {
                self.collect_sort(&selector.sort);
            }
        }
    }

    fn collect_term(&mut self, term: &Term) {
        // Stack-safety guard: the term tree is attacker-controlled and can be
        // arbitrarily deep, which would otherwise overflow the stack here.
        stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || {
            self.collect_term_inner(term);
        });
    }

    fn collect_term_inner(&mut self, term: &Term) {
        self.terms += 1;
        match term {
            Term::Const(_) | Term::Symbol(_) => {}
            Term::App(function, args) => {
                self.bump_theory(classify_operator(function));
                for arg in args {
                    self.collect_term(arg);
                }
            }
            Term::IndexedApp(function, _indices, args) => {
                self.bump_theory(classify_operator(function));
                for arg in args {
                    self.collect_term(arg);
                }
            }
            Term::QualifiedApp(function, sort, args) => {
                if let QualifiedIdentifier::Symbol(function) = function {
                    self.bump_theory(classify_operator(function));
                }
                self.collect_sort(sort);
                for arg in args {
                    self.collect_term(arg);
                }
            }
            Term::Let(bindings, body) => {
                for (_, value) in bindings {
                    self.collect_term(value);
                }
                self.collect_term(body);
            }
            Term::Forall(bindings, body)
            | Term::Exists(bindings, body)
            | Term::Lambda(bindings, body) => {
                self.bump_theory("quantifiers");
                for (_, sort) in bindings {
                    self.collect_sort(sort);
                }
                self.collect_term(body);
            }
            Term::Annotated(body, _) => {
                self.collect_term(body);
            }
            Term::Match(scrutinee, cases) => {
                self.bump_theory("datatypes");
                self.collect_term(scrutinee);
                for (_, body) in cases {
                    self.collect_term(body);
                }
            }
        }
    }

    fn collect_sort(&mut self, sort: &Sort) {
        // Stack-safety guard for deeply nested sorts (see collect_term).
        stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || {
            self.collect_sort_inner(sort);
        });
    }

    fn collect_sort_inner(&mut self, sort: &Sort) {
        match sort {
            Sort::Simple(name) => {
                self.bump_sort(name);
            }
            Sort::Parameterized(name, args) => {
                self.bump_sort(name);
                for arg in args {
                    self.collect_sort(arg);
                }
            }
            Sort::Indexed(name, _) => {
                self.bump_sort(name);
            }
        }
    }

    fn bump_sort(&mut self, sort: &str) {
        *self.sort_distribution.entry(sort.to_string()).or_insert(0) += 1;
    }

    fn bump_theory(&mut self, theory: &str) {
        *self.theory_usage.entry(theory.to_string()).or_insert(0) += 1;
    }
}

impl std::fmt::Display for FormulaStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "(:formula-statistics")?;
        writeln!(f, "  :commands {}", self.commands)?;
        writeln!(f, "  :terms {}", self.terms)?;
        for (name, count) in &self.sort_distribution {
            let key = sanitize_stat_key(name);
            writeln!(f, "  :sort.{key} {count}")?;
        }
        for (name, count) in &self.theory_usage {
            writeln!(f, "  :theory.{name} {count}")?;
        }
        write!(f, ")")
    }
}

/// Collect frontend formula statistics from parsed commands.
#[must_use]
pub fn collect_formula_stats(commands: &[Command]) -> FormulaStats {
    FormulaStats::from_commands(commands)
}

fn sanitize_stat_key(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    for c in name.chars() {
        if c.is_ascii_alphanumeric() || c == '_' || c == '-' || c == '.' {
            out.push(c);
        } else {
            out.push('_');
        }
    }
    out
}

fn classify_operator(function: &str) -> &'static str {
    if function.starts_with("str.") {
        return "strings";
    }
    if function.starts_with("re.") {
        return "regex";
    }
    if function.starts_with("seq.") {
        return "sequences";
    }
    if function.starts_with("fp.") {
        return "fp";
    }
    if function.starts_with("bv")
        || function.starts_with("(_ bv")
        || function.starts_with("(_ extract")
        || function.starts_with("(_ zero_extend")
        || function.starts_with("(_ sign_extend")
        || function.starts_with("(_ rotate_")
    {
        return "bitvec";
    }
    if function == "select" || function == "store" || function == "const" {
        return "arrays";
    }
    if matches!(
        function,
        "+" | "-"
            | "*"
            | "/"
            | "div"
            | "mod"
            | "abs"
            | "<"
            | "<="
            | ">"
            | ">="
            | "to_real"
            | "to_int"
            | "is_int"
    ) {
        return "arith";
    }
    if matches!(
        function,
        "and" | "or" | "not" | "=>" | "xor" | "ite" | "=" | "distinct"
    ) {
        return "bool";
    }
    if function.starts_with("is-") {
        return "datatypes";
    }
    "uf_or_other"
}

#[cfg(test)]
#[path = "stats_tests.rs"]
mod tests;
