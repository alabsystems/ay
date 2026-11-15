// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Printed-surface judgement for Alethe `la_generic` steps.
//!
//! `la_generic` is a RELATION over its printed operands: the checker negates
//! each printed literal, flattens both sides to a linear combination over the
//! terms it can read as arithmetic, scales each row by the printed
//! coefficient and asks whether the sum is a contradiction. An opaque term —
//! an uninterpreted application, an `ite`, a `select`, a `choice` — is one
//! atom of that combination, keyed by the PARSED term, so two spellings of
//! one internal `TermId` are two atoms to the checker and the rows never
//! cancel.
//!
//! The ninth false green of this campaign lived exactly there. A negated
//! universal `(not (forall ((z Int)) (or (< z 0) (>= (g z) (ite (= z z) z
//! 0)))))` is simplified at term construction (`(ite (= z z) z 0)` is `z` to
//! the store), Skolemized, and its instance literal ships in its AUTHORED
//! spelling through the printer's own Skolem channel
//! (`register_substituted_surface_overrides` installs the authored body under
//! `binder := choice` on the instance's subterms), while every wire-rule
//! promotion that decided `la_generic` — `promoted_wire_rule` and its
//! siblings, fed `wire_term_overrides` — was judging the PRODUCER's table
//! only, where that literal is an identity spelling. Every internal signal
//! green; pinned carcara 1.1.0: `final disequality is not contradictory`.
//! Same mechanism as the sixth, seventh and eighth shapes: the object AY
//! verified and the object it shipped were not the same object.
//!
//! [`printed_la_generic_holds`] replays the pinned checker's own decision
//! procedure (`carcara/src/checker/rules/linear_arithmetic.rs::la_generic`)
//! over the exact literal text and `:args` a step is about to ship. It is
//! wired at ONE place — `AlethePrinter::format_step`, over the rendered bytes
//! of every step — so every one of the fourteen sites that can print `:rule
//! la_generic` is judged over the text it ships, whatever channel spelled it.
//! It can only refuse; a refusal declines the step to the honest `hole` (or
//! declines the export at an `assume`, which has no hole), never to a
//! different rule name and never to a bridge AY did not derive.
//!
//! # What is replayed, and what "the same atom" means here
//!
//! * `negate_disequality`: a literal is `(not (R a b))` with `R` one of `<`,
//!   `<=`, `>`, `>=`, `=`, hypothesis `a R b`; or `(R a b)` with `R` an order
//!   relation, hypothesis `a R' b` for the converse `R'`. A positive
//!   equality, a doubled `not`, a `distinct` or any other head refuses.
//! * `LinearComb::from_term`: `+` flattens; unary `-` negates; n-ary `-`
//!   subtracts; a BINARY `*` with one operand `as_fraction` scales the other;
//!   anything `as_fraction` is a constant; everything else is one opaque
//!   atom. `as_fraction` is a numeral, a decimal, a GMP-style `n/d`, a `(/ n
//!   d)` or `(div n d)` over signed numerals, or `(- x)` of one of those.
//! * `strengthen`, exactly as the pinned build does it — INCLUDING that it
//!   strengthens whenever the row's constant is integral, with no sort
//!   check: `x > c` becomes `x >= floor(c) + gcd(coefficients, c)`, and a
//!   `>=` row with a non-integral constant becomes `>= floor(c) + 1`. The
//!   eighth shape's own `t14` (`(>= (g c) c)`, `(<= (+ (g c) 1) c)`, args `1
//!   1`) is accepted by carcara ONLY through this strengthening — the
//!   rational sum is `1 > 0`, not a contradiction — so a replay without it
//!   would hole a step the checker accepts and destroy evidence the campaign
//!   already has. MEASURED against the pinned build on that document.
//! * the fold and the final test: the left side empty, and `0 op c` false.
//!
//! Atom identity is the parsed term's: `|x|` is `x` when `x` is a legal
//! simple symbol ([`bare_symbol`]), `(! t :attr ..)` is `t`, alternate
//! bit-vector literal spellings are one constant, and whitespace inside an
//! application is nothing. Everything else is byte comparison, the
//! conservative direction for a predicate that can only refuse. Binder names
//! are NOT identified modulo renaming: carcara's term pool interns a `choice`
//! by its exact binder, and two `choice` spellings that differ only in the
//! binder are two atoms to `LinearComb` (the printer spells one witness one
//! way, so this never over-refuses a document AY prints).

use super::parse_printed_bitvec_literal;
use super::printed_command::{
    clause_literals, printed_commands, rendered_rule_field_names, PrintedCommandRead,
};
use super::quantifier_surface::bare_symbol;
use super::surface_tokens::split_smt_term_slices_bounded;
use num_bigint::BigInt;
use num_integer::Integer as _;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::collections::BTreeMap;

#[path = "alethe_printer_la_generic_surface/readings.rs"]
pub(super) mod readings;

/// Byte cap on one rendered step handed to the judgement.
const MAX_STEP_BYTES: usize = 4 * 1024 * 1024;

/// Cap on parsed nodes across one step's judgement.
const MAX_STEP_NODES: usize = 1 << 20;

/// Nesting cap for the reader and the flattening.
const MAX_DEPTH: usize = 2_048;

struct Budget {
    nodes: usize,
}

impl Budget {
    fn charge(&mut self) -> Option<()> {
        self.nodes = self.nodes.checked_add(1)?;
        (self.nodes <= MAX_STEP_NODES).then_some(())
    }
}

/// A printed term read back as carcara parses it: attributes dropped,
/// quoted simple symbols unquoted.
enum Node<'a> {
    Atom(&'a str),
    List(Vec<Node<'a>>),
}

fn read<'a>(text: &'a str, depth: usize, budget: &mut Budget) -> Option<Node<'a>> {
    read_in(text, depth, budget, &StepDefinitions::NONE)
}

/// The nullary `define-fun`s one rendered step introduces, by name.
///
/// A lowering that names its long subterms (`complete_blast` binds every word
/// longer than its inline limit to a proof-local `(define-fun w () S body)`)
/// prints those definitions in the SAME rendered text as the steps that use
/// them, and the checker inlines each one before any rule runs. A judgement
/// that reads such a step without them reads two names for one polynomial as
/// two atoms and refuses a step the checker accepts.
pub(super) struct StepDefinitions<'a> {
    /// Name to body; `None` for a name the step defines more than once, which
    /// no judgement may read (the checker refuses the redefinition itself).
    bodies: BTreeMap<&'a str, Option<&'a str>>,
}

impl<'a> StepDefinitions<'a> {
    /// No definitions: every symbol is an atom.
    pub(super) const NONE: StepDefinitions<'static> = StepDefinitions {
        bodies: BTreeMap::new(),
    };

    fn body(&self, symbol: &str) -> Option<Option<&'a str>> {
        self.bodies.get(symbol).copied()
    }

    /// `text` with a name this step defines replaced by the term it names, as
    /// the checker inlines it (followed through further names); `text` itself
    /// when it is an application or an undefined name; `None` for a name the
    /// step defines twice, or a chain past [`MAX_DEPTH`].
    pub(super) fn inline_top(&self, text: &'a str) -> Option<&'a str> {
        let mut current = text.trim();
        for _ in 0..MAX_DEPTH {
            if current.starts_with('(') {
                return Some(current);
            }
            match self.body(bare_symbol(current)) {
                Some(Some(body)) => current = body.trim(),
                Some(None) => return None,
                None => return Some(current),
            }
        }
        None
    }
}

/// Every nullary `(define-fun NAME () SORT BODY)` command of one rendered
/// step, read as a COMMAND object ([`printed_commands`]). Unreadable text
/// defines nothing.
pub(super) fn printed_step_definitions(rendered: &str) -> StepDefinitions<'_> {
    let mut bodies = BTreeMap::new();
    let Ok(commands) = printed_commands(rendered) else {
        return StepDefinitions { bodies };
    };
    for command in commands {
        let PrintedCommandRead::Command(command) = command else {
            continue;
        };
        if command.head() != "define-fun"
            || command.field_count() != 5
            || command.field(2) != Some("()")
        {
            continue;
        }
        let (Some(name), Some(body)) = (command.field(1), command.field(4)) else {
            continue;
        };
        bodies
            .entry(bare_symbol(name))
            .and_modify(|seen: &mut Option<&str>| *seen = None)
            .or_insert(Some(body));
    }
    StepDefinitions { bodies }
}

/// [`read`], inlining the step's own `define-fun`s the way the checker does.
fn read_in<'a>(
    text: &'a str,
    depth: usize,
    budget: &mut Budget,
    definitions: &StepDefinitions<'a>,
) -> Option<Node<'a>> {
    budget.charge()?;
    if depth > MAX_DEPTH {
        return None;
    }
    let text = text.trim();
    let Some(inner) = text.strip_prefix('(').and_then(|t| t.strip_suffix(')')) else {
        let quoted = text.starts_with('"') || text.starts_with('|');
        if text.is_empty()
            || (!quoted && (text.contains(['(', ')']) || text.contains(char::is_whitespace)))
        {
            return None;
        }
        let symbol = bare_symbol(text);
        return match definitions.body(symbol) {
            Some(Some(body)) => read_in(body, depth + 1, budget, definitions),
            Some(None) => None,
            None => Some(Node::Atom(symbol)),
        };
    };
    let fields = split_smt_term_slices_bounded(inner, usize::MAX, MAX_STEP_BYTES).ok()?;
    if fields.first().copied() == Some("!") {
        return read_in(fields.get(1)?, depth + 1, budget, definitions);
    }
    if fields.is_empty() {
        return None;
    }
    let items = fields
        .iter()
        .map(|field| read_in(field, depth + 1, budget, definitions))
        .collect::<Option<Vec<_>>>()?;
    Some(Node::List(items))
}

/// The key `LinearComb` files an opaque atom under: the parsed term's one
/// spelling.
fn key(node: &Node<'_>, out: &mut String) {
    match node {
        Node::Atom(atom) => match parse_printed_bitvec_literal(atom) {
            Some((value, width)) => {
                out.push_str("#bv");
                out.push_str(&value.to_string());
                out.push(':');
                out.push_str(&width.to_string());
            }
            None => out.push_str(atom),
        },
        Node::List(items) => {
            if let Some((value, width)) = bitvec_list_literal(items) {
                out.push_str("#bv");
                out.push_str(&value.to_string());
                out.push(':');
                out.push_str(&width.to_string());
                return;
            }
            out.push('(');
            for (index, item) in items.iter().enumerate() {
                if index > 0 {
                    out.push(' ');
                }
                key(item, out);
            }
            out.push(')');
        }
    }
}

/// `(_ bvN W)`, the list spelling of a bit-vector literal.
fn bitvec_list_literal(items: &[Node<'_>]) -> Option<(num_bigint::BigUint, u32)> {
    let [Node::Atom(underscore), Node::Atom(value), Node::Atom(width)] = items else {
        return None;
    };
    if *underscore != "_" {
        return None;
    }
    parse_printed_bitvec_literal(&format!("(_ {value} {width})"))
}

fn head<'s>(node: &'s Node<'_>) -> Option<(&'s str, &'s [Node<'s>])> {
    let Node::List(items) = node else {
        return None;
    };
    let Node::Atom(head) = items.first()? else {
        return None;
    };
    Some((head, &items[1..]))
}

/// carcara's lexer on one token: a numeral, a decimal, or a GMP-style
/// fraction, each optionally `-`-prefixed. A leading zero is a lexer error
/// there and a refusal here.
fn number_token(token: &str) -> Option<BigRational> {
    let (negated, body) = match token.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, token),
    };
    let first_len = body.bytes().take_while(u8::is_ascii_digit).count();
    if first_len == 0 {
        return None;
    }
    let (first, rest) = body.split_at(first_len);
    if first.len() > 1 && first.starts_with('0') {
        return None;
    }
    let value = if rest.is_empty() {
        BigRational::from_integer(first.parse::<BigInt>().ok()?)
    } else {
        let delimiter = rest.as_bytes()[0];
        let second = &rest[1..];
        if !matches!(delimiter, b'/' | b'.') || !second.bytes().all(|b| b.is_ascii_digit()) {
            return None;
        }
        match delimiter {
            b'/' => {
                let numer = first.parse::<BigInt>().ok()?;
                let denom = second.parse::<BigInt>().ok()?;
                if denom.is_zero() {
                    return None;
                }
                BigRational::new(numer, denom)
            }
            _ => {
                let numer = format!("{first}{second}").parse::<BigInt>().ok()?;
                let denom = BigInt::from(10u32).pow(u32::try_from(second.len()).ok()?);
                BigRational::new(numer, denom)
            }
        }
    };
    Some(if negated { -value } else { value })
}

/// `Term::as_number`: an integer or real constant.
fn as_number(node: &Node<'_>) -> Option<BigRational> {
    match node {
        Node::Atom(atom) => number_token(atom),
        Node::List(_) => None,
    }
}

/// `Term::as_signed_number`: a constant or `(- constant)`.
fn as_signed_number(node: &Node<'_>) -> Option<BigRational> {
    match head(node) {
        Some(("-", [inner])) => as_number(inner).map(|r| -r),
        _ => as_number(node),
    }
}

/// `Term::as_fraction`, verbatim: `(- x)` of an unsigned fraction, or an
/// unsigned fraction — `(/ n d)` / `(div n d)` over signed numbers, or a
/// number. A zero divisor aborts the pinned checker, so it refuses here.
fn as_fraction(node: &Node<'_>) -> Option<BigRational> {
    fn unsigned(node: &Node<'_>) -> Option<BigRational> {
        match head(node) {
            Some(("/" | "div", [numer, denom])) => {
                let denom = as_signed_number(denom)?;
                if denom.is_zero() {
                    return None;
                }
                Some(as_signed_number(numer)? / denom)
            }
            _ => as_number(node),
        }
    }
    match head(node) {
        Some(("-", [inner])) => unsigned(inner).map(|r| -r),
        _ => unsigned(node),
    }
}

/// carcara's `LinearComb`: atoms to coefficients, plus the constant. This
/// is `la_generic`'s reader and ONLY `la_generic`'s: it never expands a
/// product of two non-fraction factors (measured: `(* n c)` against `(* c
/// n)` are two atoms to it), while the pinned build's `poly_simp` reads a
/// [`Polynomial`].
#[derive(Default)]
struct LinearComb {
    atoms: BTreeMap<String, BigRational>,
    constant: BigRational,
}

impl LinearComb {
    fn insert(&mut self, atom: String, value: BigRational) {
        if value.is_zero() {
            return;
        }
        match self.atoms.get_mut(&atom) {
            Some(existing) => {
                *existing += value;
                if existing.is_zero() {
                    self.atoms.remove(&atom);
                }
            }
            None => {
                self.atoms.insert(atom, value);
            }
        }
    }

    /// `LinearComb::add_term`, verbatim.
    fn add_term(
        &mut self,
        node: &Node<'_>,
        coeff: &BigRational,
        depth: usize,
        budget: &mut Budget,
    ) -> Option<()> {
        budget.charge()?;
        if depth > MAX_DEPTH {
            return None;
        }
        match head(node) {
            Some(("+", args)) if !args.is_empty() => {
                for arg in args {
                    self.add_term(arg, coeff, depth + 1, budget)?;
                }
            }
            Some(("-", [arg])) => {
                self.add_term(arg, &-coeff, depth + 1, budget)?;
            }
            Some(("-", [first, rest @ ..])) => {
                self.add_term(first, coeff, depth + 1, budget)?;
                for arg in rest {
                    self.add_term(arg, &-coeff, depth + 1, budget)?;
                }
            }
            Some(("*", [left, right])) => {
                let (var, inner) = match (as_fraction(left), as_fraction(right)) {
                    (None, Some(c)) => (left, c),
                    (Some(c), _) => (right, c),
                    (None, None) => {
                        let mut atom = String::new();
                        key(node, &mut atom);
                        self.insert(atom, coeff.clone());
                        return Some(());
                    }
                };
                self.add_term(var, &(inner * coeff), depth + 1, budget)?;
            }
            _ => {
                if let Some(r) = as_fraction(node) {
                    self.constant += r * coeff;
                } else {
                    let mut atom = String::new();
                    key(node, &mut atom);
                    self.insert(atom, coeff.clone());
                }
            }
        }
        Some(())
    }

    fn from_term(node: &Node<'_>, budget: &mut Budget) -> Option<Self> {
        let mut result = Self::default();
        result.add_term(node, &BigRational::one(), 0, budget)?;
        Some(result)
    }

    fn neg(&mut self) {
        for coeff in self.atoms.values_mut() {
            *coeff = -coeff.clone();
        }
        self.constant = -self.constant.clone();
    }

    fn sub(mut self, mut other: Self) -> Self {
        other.neg();
        for (atom, coeff) in other.atoms {
            self.insert(atom, coeff);
        }
        self.constant += other.constant;
        self
    }

    fn add(mut self, other: Self) -> Self {
        for (atom, coeff) in other.atoms {
            self.insert(atom, coeff);
        }
        self.constant += other.constant;
        self
    }

    fn mul(&mut self, scalar: &BigRational) {
        if scalar.is_zero() {
            self.atoms.clear();
            self.constant = BigRational::zero();
            return;
        }
        if scalar.is_one() {
            return;
        }
        for coeff in self.atoms.values_mut() {
            *coeff *= scalar;
        }
        self.constant *= scalar;
    }

    /// `LinearComb::coefficients_gcd`, verbatim: 1 unless the constant and
    /// every coefficient are integral; the gcd starts from the constant's
    /// (signed) numerator and is clamped to at least 1.
    fn coefficients_gcd(&self) -> BigInt {
        if !self.constant.is_integer() {
            return BigInt::one();
        }
        let mut result = self.constant.numer().clone();
        for coeff in self.atoms.values() {
            if result.is_one() {
                return BigInt::one();
            }
            if coeff.is_integer() {
                result = result.gcd(coeff.numer());
            } else {
                return BigInt::one();
            }
        }
        std::cmp::max(BigInt::one(), result)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Op {
    LessThan,
    LessEq,
    GreaterThan,
    GreaterEq,
    Equals,
}

impl Op {
    fn parse(head: &str) -> Option<Self> {
        Some(match head {
            "<" => Self::LessThan,
            "<=" => Self::LessEq,
            ">" => Self::GreaterThan,
            ">=" => Self::GreaterEq,
            "=" => Self::Equals,
            _ => return None,
        })
    }

    fn negate(self) -> Option<Self> {
        Some(match self {
            Self::LessThan => Self::GreaterEq,
            Self::GreaterThan => Self::LessEq,
            Self::LessEq => Self::GreaterThan,
            Self::GreaterEq => Self::LessThan,
            Self::Equals => return None,
        })
    }
}

/// `negate_disequality`, verbatim: the hypothesis one printed literal
/// contributes, as `(op, left, right)`.
fn negate_disequality<'s>(literal: &'s Node<'s>) -> Option<(Op, &'s Node<'s>, &'s Node<'s>)> {
    let (op, args) = match head(literal) {
        Some(("not", [inner])) => {
            let (relation, args) = head(inner)?;
            (Op::parse(relation)?, args)
        }
        Some((relation, args)) => (Op::parse(relation)?.negate()?, args),
        None => return None,
    };
    let [left, right] = args else {
        return None;
    };
    Some((op, left, right))
}

/// `strengthen`, verbatim — including that the pinned build strengthens on
/// the integrality of the row's constant alone, with no sort check.
fn strengthen(op: Op, disequality: &mut LinearComb, a: &BigRational) -> Op {
    let is_integer = if a.is_zero() {
        true
    } else if a.is_one() {
        disequality.constant.is_integer()
    } else {
        (disequality.constant.clone() * a).is_integer()
    };
    match op {
        Op::GreaterEq if is_integer => op,
        Op::GreaterThan if is_integer => {
            // The gcd is taken AFTER the floor, as the checker does it.
            disequality.constant = disequality.constant.floor();
            let gcd = disequality.coefficients_gcd();
            disequality.constant += BigRational::from_integer(gcd);
            Op::GreaterEq
        }
        Op::GreaterThan | Op::GreaterEq => {
            disequality.constant = disequality.constant.floor() + BigRational::one();
            Op::GreaterEq
        }
        _ => op,
    }
}

/// Replay pinned carcara 1.1.0's `la_generic` over the exact literal text
/// and `:args` a step is about to ship. `true` exactly when the checker
/// accepts the step; anything the replay cannot read is a refusal.
pub(super) fn printed_la_generic_holds(literals: &[&str], args: &[&str]) -> bool {
    if literals.len() != args.len() {
        return false;
    }
    let mut budget = Budget { nodes: 0 };
    let mut acc = LinearComb::default();
    let mut acc_op = Op::Equals;
    for (literal, arg) in literals.iter().zip(args) {
        let Some(arg) = read(arg, 0, &mut budget) else {
            return false;
        };
        let Some(a) = as_fraction(&arg) else {
            return false;
        };
        let Some(literal) = read(literal, 0, &mut budget) else {
            return false;
        };
        let Some((mut op, left, right)) = negate_disequality(&literal) else {
            return false;
        };
        let (Some(s1), Some(s2)) = (
            LinearComb::from_term(left, &mut budget),
            LinearComb::from_term(right, &mut budget),
        ) else {
            return false;
        };
        let mut disequality = s1.sub(s2);
        disequality.constant = -disequality.constant.clone();
        if op == Op::LessThan {
            disequality.neg();
            op = Op::GreaterThan;
        } else if op == Op::LessEq {
            disequality.neg();
            op = Op::GreaterEq;
        }
        let op = strengthen(op, &mut disequality, &a);
        let scale = match op {
            Op::Equals => a,
            _ => a.abs(),
        };
        disequality.mul(&scale);
        acc = acc.add(disequality);
        acc_op = match (acc_op, op) {
            (_, Op::GreaterEq) => Op::GreaterEq,
            (Op::Equals, Op::GreaterThan) => Op::GreaterThan,
            _ => acc_op,
        };
    }
    let right = &acc.constant;
    let is_disequality_true = match BigRational::zero().cmp(right) {
        std::cmp::Ordering::Less => matches!(acc_op, Op::LessThan | Op::LessEq),
        std::cmp::Ordering::Equal => matches!(acc_op, Op::LessEq | Op::GreaterEq | Op::Equals),
        std::cmp::Ordering::Greater => matches!(acc_op, Op::GreaterThan | Op::GreaterEq),
    };
    acc.atoms.is_empty() && !is_disequality_true
}

/// carcara's `Polynomial` (`checker/rules/polynomial.rs` at the pinned
/// `9a352ee`): monomials — multisets of opaque atoms — to coefficients, plus
/// the constant. A monomial is keyed by its sorted atom keys, which is the
/// checker's pointer-sorted `Vec<Rc<Term>>` modulo the order it happens to
/// sort in.
#[derive(Default)]
struct Polynomial {
    monomials: BTreeMap<Vec<String>, BigRational>,
    constant: BigRational,
}

impl Polynomial {
    fn insert(&mut self, monomial: Vec<String>, value: BigRational) {
        if value.is_zero() {
            return;
        }
        match self.monomials.get_mut(&monomial) {
            Some(existing) => {
                *existing += value;
                if existing.is_zero() {
                    self.monomials.remove(&monomial);
                }
            }
            None => {
                self.monomials.insert(monomial, value);
            }
        }
    }

    /// `Polynomial::add_term`, verbatim, for the arithmetic operators. The
    /// bit-vector arms (`bvadd`, `bvsub`, `bvneg`, `bvmul`, a bit-vector
    /// literal) are refused: the checker reduces such a polynomial modulo
    /// `2^width` from the term's SORT, which the printed text does not carry,
    /// and no site of this printer emits a bit-vector `poly_simp`.
    fn add_term(
        &mut self,
        node: &Node<'_>,
        coeff: &BigRational,
        depth: usize,
        budget: &mut Budget,
    ) -> Option<()> {
        budget.charge()?;
        if depth > MAX_DEPTH {
            return None;
        }
        match head(node) {
            Some(("+", args)) if !args.is_empty() => {
                for arg in args {
                    self.add_term(arg, coeff, depth + 1, budget)?;
                }
            }
            Some(("-", [arg])) => {
                self.add_term(arg, &-coeff, depth + 1, budget)?;
            }
            Some(("-", [first, rest @ ..])) => {
                self.add_term(first, coeff, depth + 1, budget)?;
                for arg in rest {
                    self.add_term(arg, &-coeff, depth + 1, budget)?;
                }
            }
            Some(("*", args)) if !args.is_empty() => {
                let mut product: Option<Polynomial> = None;
                for arg in args {
                    let factor = Polynomial::from_term(arg, depth + 1, budget)?;
                    product = Some(match product {
                        Some(acc) => acc.mul(factor),
                        None => factor,
                    });
                }
                let product = product?;
                for (monomial, inner) in product.monomials {
                    self.insert(monomial, inner * coeff);
                }
                self.constant += coeff * product.constant;
            }
            Some(("/", [numer, denom])) if as_fraction(denom).is_some_and(|r| !r.is_zero()) => {
                let r = as_fraction(denom)?;
                self.add_term(numer, &(coeff / r), depth + 1, budget)?;
            }
            Some(("to_real", [arg])) => {
                self.add_term(arg, coeff, depth + 1, budget)?;
            }
            Some(("/" | "div", [_, denom])) if as_fraction(denom).is_some_and(|r| r.is_zero()) => {
                let mut atom = String::new();
                key(node, &mut atom);
                self.insert(vec![atom], coeff.clone());
            }
            Some(("bvadd" | "bvsub" | "bvneg" | "bvmul", _)) => return None,
            _ => {
                if let Some(r) = as_fraction(node) {
                    self.constant += r * coeff;
                } else if is_bitvec_literal(node) {
                    return None;
                } else {
                    let mut atom = String::new();
                    key(node, &mut atom);
                    self.insert(vec![atom], coeff.clone());
                }
            }
        }
        Some(())
    }

    fn from_term(node: &Node<'_>, depth: usize, budget: &mut Budget) -> Option<Self> {
        let mut result = Self::default();
        result.add_term(node, &BigRational::one(), depth, budget)?;
        Some(result)
    }

    /// `Polynomial::mul`, verbatim.
    fn mul(self, other: Self) -> Self {
        let mut result = Self::default();
        for (x_1, c_1) in self.monomials {
            for (x_2, c_2) in &other.monomials {
                let mut monomial = x_1.clone();
                monomial.extend(x_2.iter().cloned());
                monomial.sort_unstable();
                result.insert(monomial, c_1.clone() * c_2);
            }
            result.insert(x_1, c_1 * &other.constant);
        }
        for (x_2, c_2) in other.monomials {
            result.insert(x_2, c_2 * &self.constant);
        }
        result.constant += self.constant * other.constant;
        result
    }

    fn sub(mut self, other: Self) -> Self {
        for (monomial, coeff) in other.monomials {
            self.insert(monomial, -coeff);
        }
        self.constant -= other.constant;
        self
    }

    fn is_zero(&self) -> bool {
        self.monomials.is_empty() && self.constant.is_zero()
    }
}

/// `#b..`, `#x..` or `(_ bvN W)`.
fn is_bitvec_literal(node: &Node<'_>) -> bool {
    match node {
        Node::Atom(atom) => parse_printed_bitvec_literal(atom).is_some(),
        Node::List(items) => bitvec_list_literal(items).is_some(),
    }
}

/// Replay pinned carcara 1.1.0's `poly_simp` over two printed terms: the
/// step `(cl (= t s))` is accepted exactly when `Polynomial(t) -
/// Polynomial(s)` is zero — the checker's `polynomial.rs` at the pinned
/// `9a352ee`, which normalizes NONLINEAR monomials (`(* (+ i 1) (+ i 1))` IS
/// `(+ (* i i) (+ (* 2 i) 1))`), not the `LinearComb` of `la_generic`.
/// MEASURED on the pinned binary (`probe_ring.py`, 2026-09-13): the ring
/// identity and `(= (* x y) (* y x))` are `valid`, the identity with a wrong
/// constant is `invalid` ("terms are not equal after polynomial
/// normalization"). The carcara source tree under `~/.cargo/git/checkouts`
/// (`fecb422`) is NOT the pinned source — its `poly_simp` is the linear
/// comparison — and a first draft ported that, holing the ring identity the
/// checker accepts and moving a NIA verdict to `unknown`; the pinned
/// `9a352ee` was fetched and this is its `Polynomial::from_term`, verbatim.
///
/// `Some(true)` / `Some(false)` is the checker's answer. `None` — no
/// judgement — for the two things the text cannot decide: a bit-vector term
/// (the checker reduces modulo `2^width` from the SORT, which the printed
/// text does not carry; no site of this printer prints a bit-vector
/// `poly_simp`) and text this reader cannot parse (`match`). A judgement may
/// only refuse what the checker refuses.
///
/// This is also the rule for a constant identity between two spellings — a
/// decimal against its fraction, `i` against `(+ i 0)`. It is NOT
/// `la_generic`: that rule negates each literal and a positive equality has
/// no negation it reads (`negate_disequality` refuses `=` outright).
/// MEASURED on the pinned build (`probe_eq2.py`, 2026-09-13):
/// `(cl (= 1.5 (/ 3.0 2.0)))` is `invalid` under `la_generic :args (1)` ("is
/// not a valid disequality operation") and `valid` under `poly_simp`.
pub(super) fn printed_poly_simp_holds(left: &str, right: &str) -> Option<bool> {
    printed_poly_simp_holds_under(left, right, &StepDefinitions::NONE)
}

/// [`printed_poly_simp_holds`] for a step printed beside its own
/// `define-fun`s ([`printed_step_definitions`]): a defined name is read as its
/// body, as the checker reads it. Without this, `complete_blast`'s
/// `(= w12 w15)` — two names for `(bvmul #b..10000000 src)` and its doubling
/// chain — read as two distinct atoms, `Some(false)`, and the whole
/// certificate became one `hole` (70 of external-codegen's strict-gate obligations,
/// measured 2026-09-28 on build 10607, e.g. `base - src*2^7 == base -
/// (src<<7)`). A name the step defines twice reads as no judgement.
pub(super) fn printed_poly_simp_holds_under(
    left: &str,
    right: &str,
    definitions: &StepDefinitions<'_>,
) -> Option<bool> {
    let mut budget = Budget { nodes: 0 };
    let left = read_in(left, 0, &mut budget, definitions)?;
    let right = read_in(right, 0, &mut budget, definitions)?;
    let left = Polynomial::from_term(&left, 0, &mut budget)?;
    let right = Polynomial::from_term(&right, 0, &mut budget)?;
    Some(left.sub(right).is_zero())
}

/// Whether the pinned checker refuses the `poly_simp` step `(= left right)`
/// of `rendered`, judged over the step's own `define-fun`s
/// ([`printed_poly_simp_holds_under`]); they are read into `definitions` the
/// first time a step needs them.
pub(super) fn printed_poly_simp_refused<'a>(
    left: &'a str,
    right: &'a str,
    rendered: &'a str,
    definitions: &std::cell::OnceCell<StepDefinitions<'a>>,
) -> bool {
    let definitions = definitions.get_or_init(|| printed_step_definitions(rendered));
    printed_poly_simp_holds_under(left, right, definitions) == Some(false)
}

/// One `:rule la_generic` command read off a rendered step.
pub(super) struct PrintedLaGeneric<'a> {
    /// The command's own id token (`t14`, `t14.split`, ..).
    pub name: &'a str,
    /// The printed clause literals.
    pub literals: Vec<&'a str>,
    /// The printed `:args`.
    pub args: Vec<&'a str>,
}

/// One command of a rendered step that claims an arithmetic rule this
/// judgement replays.
pub(super) enum PrintedArithCommand<'a> {
    /// `(step NAME (cl ..) :rule la_generic :args (..))`.
    LaGeneric(PrintedLaGeneric<'a>),
    /// `(step NAME (cl (= t s)) :rule poly_simp)`.
    PolySimp {
        name: &'a str,
        left: &'a str,
        right: &'a str,
    },
    /// A command whose RULE FIELD names one of the two rules and whose shape
    /// this reader cannot decompose — a step this printer never emits. Judged
    /// as a refusal: a reader that cannot read a step cannot approve it.
    Unreadable { name: Option<&'a str> },
}

/// Every command of one rendered step that claims `la_generic` or
/// `poly_simp`, read as COMMAND OBJECTS — head, clause, rule field, args —
/// and never as a substring of rendered text.
///
/// `None` when the rendered text is not a sequence of balanced commands at
/// all (only a budget overrun or a printer that emitted something this reader
/// cannot split); the caller then falls back to
/// [`rendered_rule_field_names_arith`], which decides on TOKENS, so an
/// unreadable step is never silently equivalent to a refusal.
///
/// Why this is structural. Until 2026-09-16 the reader scanned rendered LINES
/// for the substring `" :rule la_generic"` and required each hit to parse as a
/// step, returning `None` — read by the caller as a refusal — when it did not.
/// Three shapes that are not code triggered it, each on a document the pinned
/// checker calls `valid`: a legal quoted function symbol
/// `|g :rule la_generic :args (1 1)|`, a QF_SLIA string literal
/// `" :rule la_generic :args (1 1)"`, and `"x :rule poly_simp)"`. Each was an
/// `assume` leaf, which has no hole, so the whole export was declined and the
/// verdict moved to `unknown` under `--strict-proofs`. A judgement that
/// claims to read the proof must read the proof.
pub(super) fn printed_arith_commands(rendered: &str) -> Option<Vec<PrintedArithCommand<'_>>> {
    let commands = printed_commands(rendered).ok()?;
    // Names this step's own `define-fun`s bind: the checker expands them.
    let defined: super::HashSet<String> = commands
        .iter()
        .filter_map(|read| match read {
            PrintedCommandRead::Command(command) if command.head() == "define-fun" => {
                command.field(1).map(|name| bare_symbol(name).to_string())
            }
            _ => None,
        })
        .collect();
    let mut out = Vec::new();
    for read in commands {
        let command = match read {
            PrintedCommandRead::Command(command) => command,
            PrintedCommandRead::Unsplittable(text) => {
                // A command this reader cannot split into fields cannot name
                // a rule to this reader either. `rendered_rule_field_names`
                // is the token-level backstop for exactly this case;
                // refusing here would refuse on the bytes of an operand.
                if rendered_rule_field_names_arith(text) {
                    out.push(PrintedArithCommand::Unreadable { name: None });
                }
                continue;
            }
        };
        let Some(rule_at) = command.keyword_position(":rule") else {
            continue;
        };
        let rule = command.rule();
        let is_la_generic = rule == Some("la_generic");
        let is_poly_simp = rule == Some("poly_simp");
        if !is_la_generic && !is_poly_simp {
            continue;
        }
        let name = (command.head() == "step").then(|| command.name()).flatten();
        let unreadable = PrintedArithCommand::Unreadable { name };
        let (Some(name), Some(clause)) = (name, command.field(2)) else {
            out.push(unreadable);
            continue;
        };
        let Some(literals) = clause_literals(clause) else {
            out.push(unreadable);
            continue;
        };
        if is_poly_simp {
            // `poly_simp` is premise-free and argument-free at every site
            // this printer emits: `(step NAME (cl (= t s)) :rule poly_simp)`.
            let [equality] = literals.as_slice() else {
                out.push(unreadable);
                continue;
            };
            let sides = equality
                .strip_prefix("(=")
                .and_then(|inner| inner.strip_suffix(')'))
                .and_then(|inner| {
                    split_smt_term_slices_bounded(inner, usize::MAX, MAX_STEP_BYTES).ok()
                });
            match (command.field_count(), sides.as_deref()) {
                // Text this reader cannot expand (a local definition names a
                // bit-vector term, which it does not judge either): read as
                // free atoms, the complete bit-blast's `(= @w6 @w5)` was a
                // nonzero difference and every such lemma shipped as `hole`.
                (5, Some([left, right]))
                    if super::first_symbol_token_in(left, &defined).is_some()
                        || super::first_symbol_token_in(right, &defined).is_some() => {}
                (5, Some([left, right])) => {
                    out.push(PrintedArithCommand::PolySimp { name, left, right })
                }
                _ => out.push(unreadable),
            }
            continue;
        }
        // `la_generic` is premise-free and carries exactly one `:args` list.
        let args = (command.field_count() == 7 && command.field(5) == Some(":args"))
            .then(|| command.args())
            .flatten();
        match args {
            Some(args) if rule_at == 3 => {
                out.push(PrintedArithCommand::LaGeneric(PrintedLaGeneric {
                    name,
                    literals,
                    args,
                }));
            }
            _ => out.push(unreadable),
        }
    }
    Some(out)
}

/// Whether some `:rule` KEYWORD in `text` is followed by `la_generic` or
/// `poly_simp`, reading SMT-LIB tokens ([`rendered_rule_field_names`]).
pub(super) fn rendered_rule_field_names_arith(text: &str) -> bool {
    rendered_rule_field_names(text, &["la_generic", "poly_simp"])
}

#[cfg(test)]
#[path = "alethe_printer_la_generic_surface_tests.rs"]
mod tests;
