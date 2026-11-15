// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The document's terms, hash-consed: the proof's definitions expanded and,
//! read as the consumer, its parsing boundary applied (see `reader`).

use std::collections::{HashMap, HashSet};

use super::query::{atoms, live_query, Signature};
use super::reader::{decimal_literal, hex_as_binary, Command, Sexp};

#[path = "document/proof_commands.rs"]
mod proof_commands;

/// The bit-vector operators whose result is as wide as their first operand.
const SAME_WIDTH: &[&str] = &[
    "bvnot", "bvneg", "bvand", "bvor", "bvxor", "bvnand", "bvnor", "bvxnor", "bvadd", "bvsub",
    "bvmul", "bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod", "bvshl", "bvlshr", "bvashr",
];

/// The bit-vector operators whose result is one bit wide.
const ONE_BIT: &[&str] = &["bvcomp", "bvredor", "bvredand"];

/// A hash-consed term: the consumer compares terms structurally after it
/// expands the proof's `define-fun` macros, and a bit-blasted circuit shares
/// its subterms, so expanding into trees would be exponential.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum Node {
    Atom(String),
    List(Vec<u32>),
}

pub(super) struct Document {
    pub(super) commands: Vec<Command>,
    /// Apply the consumer's parsing boundary (literal spelling, `zero_extend`).
    consumer: bool,
    /// The problem's live symbols (by spelling) and their elaborated
    /// signatures: the only source of a symbol's sort.
    signatures: HashMap<String, Signature>,
    /// The problem's assertions live at its query, expanded.
    pub(super) assertions: Vec<u32>,
    /// Every name the problem declares or defines, or its live assertions
    /// mention.
    problem_symbols: HashSet<String>,
    /// Every live symbol the problem declares or defines, by spelling: never
    /// an operator head (see [`Document::head`]).
    declared: HashSet<String>,
    /// Why the problem's script is not read as one query (a `pop` below
    /// the bottom of the assertion stack).
    pub(super) problem_defects: Vec<String>,
    /// The proof `define-fun`s of a name the problem uses.
    pub(super) redefined: Vec<String>,
    /// Why the proof is not read as Carcara reads it: an unreadable proof, a
    /// macro with parameters, or one defined after a command that uses its
    /// name (or defined twice).
    pub(super) proof_defects: Vec<String>,
    nodes: Vec<Node>,
    interned: HashMap<Node, u32>,
    expanded_names: HashMap<String, u32>,
}

impl Document {
    /// The proof as printed: definitions expanded, spellings kept.
    pub(super) fn read(proof: &str) -> Self {
        Self::build(proof, false)
    }

    /// The problem and proof as the consumer parses them. The problem's
    /// assertions are read from the problem alone, before any proof
    /// definition exists (Carcara parses the problem first, so a proof
    /// `define-fun` never rewrites a premise), and only those live at the
    /// problem's query: the first `check-sat`, `check-sat-assuming` (whose
    /// assumptions are added) or `exit`, after `push`/`pop`,
    /// `reset-assertions` and `reset` have applied.
    ///
    /// REGRESSION (measured 2026-10-07 on 4373bc24b): the proof was read
    /// first and its macros expanded inside the problem's assertions, so
    /// `(define-fun p () Bool false)` turned `(assert p)` into `false` and a
    /// refutation of the satisfiable `(assert p)` was counted as checked; and
    /// every `assert` in the script was a premise, so `(push 1) (assert
    /// false) (pop 1)`, `(assert false) (reset-assertions)` and an `(assert
    /// false)` after the `check-sat` were refuted too.
    pub(super) fn read_as_consumer(problem: &str, proof: &str) -> Self {
        let mut document = Self::empty(true);
        let query = live_query(problem);
        document.signatures = query.signatures;
        document.problem_defects = query.defects;
        document.assertions = query
            .assertions
            .iter()
            .map(|term| document.expand(term))
            .collect();
        // The problem's own names, as the problem reads them: a proof
        // definition of one of them is refused (see `read_proof`).
        document.declared = query.symbols.clone();
        let mut used = query.symbols;
        for term in &query.assertions {
            atoms(term, &mut used);
        }
        document.problem_symbols = used;
        // The problem's atoms were memoized as themselves; the proof's
        // definitions start from an empty macro table.
        document.expanded_names.clear();
        document.read_proof(proof);
        document
    }

    fn empty(consumer: bool) -> Self {
        Self {
            commands: Vec::new(),
            consumer,
            signatures: HashMap::new(),
            assertions: Vec::new(),
            problem_symbols: HashSet::new(),
            declared: HashSet::new(),
            problem_defects: Vec::new(),
            redefined: Vec::new(),
            proof_defects: Vec::new(),
            nodes: Vec::new(),
            interned: HashMap::new(),
            expanded_names: HashMap::new(),
        }
    }

    fn build(proof: &str, consumer: bool) -> Self {
        let mut document = Self::empty(consumer);
        document.read_proof(proof);
        document
    }

    pub(super) fn intern(&mut self, node: Node) -> u32 {
        if let Some(&id) = self.interned.get(&node) {
            return id;
        }
        let id = u32::try_from(self.nodes.len()).expect("term count");
        self.nodes.push(node.clone());
        self.interned.insert(node, id);
        id
    }

    pub(super) fn atom(&mut self, text: &str) -> u32 {
        self.intern(Node::Atom(text.to_string()))
    }

    /// `(head args…)`.
    pub(super) fn app(&mut self, head: &str, args: &[u32]) -> u32 {
        let mut children = vec![self.atom(head)];
        children.extend_from_slice(args);
        self.intern(Node::List(children))
    }

    /// `((_ @bit_of index) term)`, Carcara's bit of a word that is not an `@bbterm`.
    pub(super) fn bit_of(&mut self, index: usize, term: u32) -> u32 {
        let indexed = [
            self.atom("_"),
            self.atom("@bit_of"),
            self.atom(&index.to_string()),
        ];
        let head = self.intern(Node::List(indexed.to_vec()));
        self.intern(Node::List(vec![head, term]))
    }

    /// The bit-vector constant `value` of `width` bits, in the consumer's spelling.
    pub(super) fn constant(&mut self, value: usize, width: usize) -> u32 {
        let bits: String = (0..width)
            .rev()
            .map(|i| {
                if i < usize::BITS as usize && value >> i & 1 == 1 {
                    '1'
                } else {
                    '0'
                }
            })
            .collect();
        self.atom(&format!("#b{bits}"))
    }

    /// `term` with every proof `define-fun` name replaced by its body, as the
    /// consumer's parser does, and (as the consumer) its literals and
    /// `zero_extend` normalized.
    pub(super) fn expand(&mut self, term: &Sexp) -> u32 {
        match term {
            Sexp::Atom(name) => {
                if let Some(&id) = self.expanded_names.get(name) {
                    return id;
                }
                let spelled = if self.consumer {
                    hex_as_binary(name)
                } else {
                    None
                };
                let id = self.intern(Node::Atom(spelled.unwrap_or_else(|| name.clone())));
                self.expanded_names.insert(name.clone(), id);
                id
            }
            Sexp::List(items) => {
                if let Some(binary) = decimal_literal(items).filter(|_| self.consumer) {
                    return self.atom(&binary);
                }
                // The consumer's parser drops `(! t :named n …)` annotations.
                if let [bang, annotated, ..] = &items[..] {
                    if self.consumer && bang.is_atom("!") {
                        return self.expand(annotated);
                    }
                }
                let children: Vec<u32> = items.iter().map(|item| self.expand(item)).collect();
                if self.consumer {
                    if let Some(extended) = self.eliminate_zero_extend(&children) {
                        return extended;
                    }
                }
                self.intern(Node::List(children))
            }
        }
    }

    fn eliminate_zero_extend(&mut self, children: &[u32]) -> Option<u32> {
        let [head, operand] = children else {
            return None;
        };
        let Node::List(indexed) = &self.nodes[*head as usize] else {
            return None;
        };
        let [under, name, extra] = indexed.as_slice() else {
            return None;
        };
        if !self.is_atom(*under, "_") || !self.is_atom(*name, "zero_extend") {
            return None;
        }
        let extra: usize = self.atom_text(*extra)?.parse().ok()?;
        if extra == 0 {
            return Some(*operand);
        }
        let zero = self.constant(0, extra);
        Some(self.app("concat", &[zero, *operand]))
    }

    pub(super) fn node(&self, id: u32) -> &Node {
        &self.nodes[id as usize]
    }

    pub(super) fn atom_text(&self, id: u32) -> Option<&str> {
        match &self.nodes[id as usize] {
            Node::Atom(text) => Some(text),
            Node::List(_) => None,
        }
    }

    /// The operator an application `id` applies: its head atom, unless that
    /// atom is a symbol the problem declares, whose application is the
    /// user's function whatever it is spelled like, and no rule's operator.
    ///
    /// REGRESSION (measured 2026-10-07 on 7ae4f642c): the head's bare name
    /// was the operator, so the problem's own `(declare-fun ite (Bool Int)
    /// Int)` was folded by `evaluate` as the connective and a refutation of a
    /// satisfiable problem was counted as checked.
    pub(super) fn head(&self, id: u32) -> Option<&str> {
        self.head_atom(id)
            .filter(|head| !self.declared.contains(*head))
    }

    /// The head atom of an application, operator or user function alike.
    fn head_atom(&self, id: u32) -> Option<&str> {
        match &self.nodes[id as usize] {
            Node::List(children) => children.first().and_then(|&c| self.atom_text(c)),
            Node::Atom(_) => None,
        }
    }

    pub(super) fn args(&self, id: u32) -> Vec<u32> {
        match &self.nodes[id as usize] {
            Node::List(children) if !children.is_empty() => children[1..].to_vec(),
            _ => Vec::new(),
        }
    }

    /// The arguments of `id` when it is an application of `head`.
    pub(super) fn op(&self, id: u32, head: &str) -> Option<Vec<u32>> {
        (self.head(id) == Some(head)).then(|| self.args(id))
    }

    pub(super) fn is_atom(&self, id: u32, text: &str) -> bool {
        self.atom_text(id) == Some(text)
    }

    /// The operator name and index atoms of an indexed head `(_ name i…)`.
    pub(super) fn indexed_name(&self, head: u32) -> Option<(String, Vec<u32>)> {
        let Node::List(indexed) = &self.nodes[head as usize] else {
            return None;
        };
        let [under, operator, indices @ ..] = indexed.as_slice() else {
            return None;
        };
        if !self.is_atom(*under, "_") {
            return None;
        }
        Some((self.atom_text(*operator)?.to_string(), indices.to_vec()))
    }

    /// The indices of an indexed operator application `((_ name i…) args…)`.
    pub(super) fn indexed(&self, id: u32, name: &str) -> Option<(Vec<usize>, Vec<u32>)> {
        let Node::List(children) = &self.nodes[id as usize] else {
            return None;
        };
        let (&head, args) = children.split_first()?;
        let Node::List(indexed) = &self.nodes[head as usize] else {
            return None;
        };
        let [under, operator, indices @ ..] = indexed.as_slice() else {
            return None;
        };
        if !self.is_atom(*under, "_") || !self.is_atom(*operator, name) {
            return None;
        }
        let indices = indices
            .iter()
            .map(|&index| self.atom_text(index)?.parse().ok())
            .collect::<Option<Vec<usize>>>()?;
        Some((indices, args.to_vec()))
    }

    /// The bits of a bit-vector constant, least significant first.
    pub(super) fn constant_bits(&self, id: u32) -> Option<Vec<bool>> {
        let digits = self.atom_text(id)?.strip_prefix("#b")?;
        digits
            .bytes()
            .rev()
            .map(|digit| match digit {
                b'0' => Some(false),
                b'1' => Some(true),
                _ => None,
            })
            .collect()
    }

    /// The bit-vector width of `id` as the consumer's sort inference gives it,
    /// or `None` where this reader does not model the sort.
    pub(super) fn width(&self, id: u32) -> Option<usize> {
        if let Some(bits) = self.constant_bits(id) {
            return Some(bits.len());
        }
        if let Some(name) = self.atom_text(id) {
            return self
                .symbol_sort(name, 0)?
                .bitvec_width()
                .map(|w| w as usize);
        }
        if let Some((indices, args)) = self.indexed(id, "extract") {
            let [i, j] = indices[..] else { return None };
            return (args.len() == 1 && i >= j).then(|| i - j + 1);
        }
        for name in [
            "sign_extend",
            "zero_extend",
            "repeat",
            "rotate_left",
            "rotate_right",
        ] {
            if let Some((indices, args)) = self.indexed(id, name) {
                let ([k], [arg]) = (indices.as_slice(), args.as_slice()) else {
                    return None;
                };
                let width = self.width(*arg)?;
                return match name {
                    "repeat" => width.checked_mul(*k),
                    "rotate_left" | "rotate_right" => Some(width),
                    _ => width.checked_add(*k),
                };
            }
        }
        let head = self.head_atom(id)?;
        let args = self.args(id);
        if self.signatures.contains_key(head) {
            // A user function: its elaborated result sort, whatever its name.
            return self
                .symbol_sort(head, args.len())?
                .bitvec_width()
                .map(|w| w as usize);
        }
        if self.declared.contains(head) {
            // An overloaded problem function: no one result sort, and never
            // the operator it is spelled like.
            return None;
        }
        match head {
            "@bbterm" => Some(args.len()),
            "concat" => args.iter().map(|&arg| self.width(arg)).sum(),
            "ite" => self.width(*args.get(1)?),
            "select" => self.array_element_width(*args.first()?),
            _ if ONE_BIT.contains(&head) => Some(1),
            _ if SAME_WIDTH.contains(&head) => self.width(*args.first()?),
            _ => None,
        }
    }

    /// The elaborated result sort of the live problem symbol `name` applied
    /// to `arity` arguments (`None` when it is not one, or is overloaded).
    fn symbol_sort(&self, name: &str, arity: usize) -> Option<&ay_core::Sort> {
        let signature = self.signatures.get(name)?;
        (signature.arity == arity).then_some(&signature.sort)
    }

    fn array_element_width(&self, array: u32) -> Option<usize> {
        if let Some(name) = self.atom_text(array) {
            let element = self.symbol_sort(name, 0)?.array_element()?;
            return element.bitvec_width().map(|w| w as usize);
        }
        if let Some(head) = self
            .head_atom(array)
            .filter(|h| self.signatures.contains_key(*h))
        {
            let arity = self.args(array).len();
            let element = self.symbol_sort(head, arity)?.array_element()?;
            return element.bitvec_width().map(|w| w as usize);
        }
        if let Node::List(children) = &self.nodes[array as usize] {
            // `((as const (Array I E)) v)`: the element sort is written.
            if let Some(Node::List(qualified)) = children.first().map(|&h| &self.nodes[h as usize])
            {
                if let [r#as, constant, sort] = qualified[..] {
                    if self.is_atom(r#as, "as") && self.is_atom(constant, "const") {
                        return self.array_sort_element_width(sort);
                    }
                }
            }
        }
        match self.head(array)? {
            "store" => self.array_element_width(*self.args(array).first()?),
            "ite" => self.array_element_width(*self.args(array).get(1)?),
            _ => None,
        }
    }

    /// The element width of an `(Array I (_ BitVec w))` sort node.
    fn array_sort_element_width(&self, sort: u32) -> Option<usize> {
        let [_, element] = self.op(sort, "Array")?[..] else {
            return None;
        };
        let [under, bitvec, width] = self.args_of_list(element)?[..] else {
            return None;
        };
        (self.is_atom(under, "_") && self.is_atom(bitvec, "BitVec")).then_some(())?;
        self.atom_text(width)?.parse().ok()
    }

    fn args_of_list(&self, id: u32) -> Option<Vec<u32>> {
        match &self.nodes[id as usize] {
            Node::List(children) => Some(children.clone()),
            Node::Atom(_) => None,
        }
    }

    /// Whether a declared constant is `Int` (`None` when it is not declared).
    pub(super) fn declared_sort_is_int(&self, atom: u32) -> Option<bool> {
        let sort = self.symbol_sort(self.atom_text(atom)?, 0)?;
        Some(matches!(sort, ay_core::Sort::Int))
    }

    /// A bounded rendering for failure messages.
    pub(super) fn show(&self, id: u32) -> String {
        let mut out = String::new();
        self.render(id, &mut out);
        if out.len() > 240 {
            out.truncate(240);
            out.push('…');
        }
        out
    }

    fn render(&self, id: u32, out: &mut String) {
        if out.len() > 240 {
            return;
        }
        match &self.nodes[id as usize] {
            Node::Atom(atom) => out.push_str(atom),
            Node::List(children) => {
                out.push('(');
                for (i, &child) in children.iter().enumerate() {
                    if i > 0 {
                        out.push(' ');
                    }
                    self.render(child, out);
                }
                out.push(')');
            }
        }
    }
}
