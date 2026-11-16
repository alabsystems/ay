// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Printed-surface judgements for Alethe `forall_inst` and `sko_forall` /
//! `sko_ex` steps.
//!
//! Both rules are SYNTACTIC: the checker reads the quantifier's binder list
//! and body off the printed text, applies the printed `:args` (or the
//! anchor's `choice`) as a substitution, and asks whether the printed
//! instance is that substitution image. AY's own checker asks the same
//! question over the term store and is right to accept a step whose term-level
//! instance is exact — but the document ships TEXT, and every rendering
//! channel the printer consults (the producer's surface-override table, the
//! Skolem `choice` table, the structural fallback) can spell one `TermId`
//! differently from another channel. The eighth false green of this campaign
//! was exactly that: the `forall_inst` `:args` printed a Skolem witness as its
//! `choice` term while the instance body — rendered from an override the
//! producer built before the printer existed — printed the witness by its
//! internal name. Same `TermId`, two spellings, and carcara refused the
//! document at the parser.
//!
//! [`printed_forall_inst_holds`] and [`printed_skolem_step_holds`] replay
//! pinned carcara 1.1.0's own decision procedure over the exact literal text a
//! step is about to ship. They can only refuse; a refusal declines the step to
//! the honest `hole`, never to a different rule name and never to a bridge AY
//! did not derive.
//!
//! # What "equal" means here, and why it is measured rather than assumed
//!
//! carcara compares PARSED terms, not bytes. `forall_inst` ends in
//! `assert_alpha_equiv_expected` and the Skolem rules in `alpha_equiv`, both
//! `Polyeq::new().mod_reordering(true).alpha_equiv(true)`
//! (`carcara/src/ast/polyeq.rs`), and its parser folds several spellings to
//! one term. [`printed_terms_alpha_equivalent`] mirrors the four identities
//! that matter for text AY prints:
//!
//! * a binary `(= a b)` equals `(= b a)` (`is_mod_reordering`);
//! * binders equal modulo renaming of bound variables, compared by De Bruijn
//!   position, with a bound variable never equal to a free one
//!   (`DeBruijnMap::compare`);
//! * `(! t :attr ..)` is `t` (the parser discards attributes);
//! * alternate bit-vector literal spellings and `1.0` / `1` are one constant
//!   (`Constant::BitVec`, and the `Real`/`Integer` case in `Term::eq`).
//!
//! Everything else is byte comparison — the conservative direction for a
//! predicate that can only refuse.
//!
//! And the substitution is carcara's, not SMT-LIB's: the pinned checker
//! cannot substitute through a `let` (it leaves the `let`'s values alone, or
//! aborts), so a quantifier body holding a `let` has no image the checker
//! would accept and both judgements decline it — see [`substitute`]. Measured
//! on the eighth shape's fixture with a `let` in the Skolemized body, where the
//! one-spelling document was refused at `t1.t1` `refl` under a green flag.

use super::surface_tokens::{split_alethe_application_bounded, split_smt_term_slices_bounded};
use super::{parse_printed_bitvec_literal, split_smt_terms};
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::quote_symbol;
use std::borrow::Cow;

/// Byte cap on one printed term handed to the tokenizer.
const MAX_SURFACE_BYTES: usize = 4 * 1024 * 1024;

/// Cap on parsed nodes across one judgement: a step past this declines rather
/// than scanning.
pub(super) const MAX_SURFACE_NODES: usize = 1 << 20;

/// Nesting cap for the recursive reader, substitution and comparison.
const MAX_SURFACE_DEPTH: usize = 2_048;

/// Binder keywords whose binding list `((x S) ..)` scopes over the body.
const BINDER_KEYWORDS: [&str; 4] = ["forall", "exists", "choice", "lambda"];

/// A printed term read back as the tree carcara parses it to.
///
/// `span` is the source text of the node, kept for the literal-spelling
/// identities that need the original bytes; it is empty for a node the
/// substitution synthesized.
#[derive(Clone, Debug)]
pub(super) struct Sexp<'a> {
    span: &'a str,
    node: Node<'a>,
}

#[derive(Clone, Debug)]
enum Node<'a> {
    /// Owned only for a capture-avoidance rename, which no input can spell.
    Atom(Cow<'a, str>),
    List(Vec<Sexp<'a>>),
}

/// Work accounting shared by one judgement.
#[derive(Default)]
struct Budget<'p> {
    nodes: usize,
    progress: Option<&'p mut dyn FnMut(u64) -> bool>,
    refused: bool,
}

impl Budget<'_> {
    fn charge(&mut self) -> Option<()> {
        self.nodes = self.nodes.checked_add(1)?;
        if self.nodes > MAX_SURFACE_NODES {
            return None;
        }
        self.spend(1)
    }

    fn spend(&mut self, amount: u64) -> Option<()> {
        if self.refused {
            return None;
        }
        if let Some(progress) = self.progress.as_mut() {
            // A callback unwind is already a sticky refusal if it is caught.
            self.refused = true;
            if !progress(amount) {
                return None;
            }
            self.refused = false;
        }
        Some(())
    }

    fn admit_text(&mut self, text: &str) -> Option<()> {
        if self.progress.is_none() {
            return Some(());
        }
        // The borrowed scanner may allocate one field slice per input byte.
        // Charge that worst-case vector and its scans before entering it.
        let per_byte = size_of::<&str>().checked_add(8)?;
        self.spend(u64::try_from(text.len().checked_mul(per_byte)?).ok()?)
    }

    fn compare_text(&mut self, left: &str, right: &str) -> Option<()> {
        if self.progress.is_none() {
            return Some(());
        }
        let bytes = left.len().checked_add(right.len())?;
        self.spend(u64::try_from(bytes).ok()?)
    }

    fn admit_items(&mut self, count: usize) -> Option<()> {
        if self.progress.is_none() {
            return Some(());
        }
        self.spend(u64::try_from(count.checked_mul(size_of::<Sexp<'_>>())?).ok()?)
    }

    fn admit_literals(&mut self, left: &str, right: &str) -> Option<()> {
        if self.progress.is_none() {
            return Some(());
        }
        // Both parser calls are eager, even against a nonnumeric opponent.
        // Debit each plausible numeral separately; the underlying parser
        // accepts whitespace after '(' as well as between '_' and 'bv'.
        for text in [left, right] {
            let text = text.trim();
            let numeric = text.starts_with("#b")
                || text.starts_with("#x")
                || text
                    .strip_prefix('(')
                    .and_then(|s| s.split_whitespace().next())
                    == Some("_");
            if numeric {
                // Decimal BigUint parsing can be quadratic in its digits.
                self.spend(u64::try_from(text.len().checked_mul(text.len())?).ok()?)?;
            }
        }
        Some(())
    }
}

/// Read one printed term. `None` on malformed text, an unsupported construct
/// (`match`, which panics the pinned checker), or an exhausted budget.
fn read<'a>(text: &'a str, depth: usize, budget: &mut Budget<'_>) -> Option<Sexp<'a>> {
    budget.charge()?;
    if depth > MAX_SURFACE_DEPTH || text.len() > MAX_SURFACE_BYTES {
        return None;
    }
    budget.admit_text(text)?;
    let text = text.trim();
    let Some(inner) = text.strip_prefix('(').and_then(|t| t.strip_suffix(')')) else {
        // A string literal or quoted symbol may contain anything; a simple
        // token may not contain a delimiter.
        let quoted = text.starts_with('"') || text.starts_with('|');
        if text.is_empty()
            || (!quoted && (text.contains(['(', ')']) || text.contains(char::is_whitespace)))
        {
            return None;
        }
        // `|x|` and `x` are one symbol to every SMT-LIB reader: the bars are
        // delimiters, not part of the name. A quoted symbol whose contents
        // are a legal simple symbol is read as that simple symbol, so the
        // two spellings compare equal (the authored binder sort `|S|`
        // against the anchor's `S`).
        return Some(Sexp {
            span: text,
            node: Node::Atom(Cow::Borrowed(bare_symbol(text))),
        });
    };
    let fields = split_smt_term_slices_bounded(inner, usize::MAX, MAX_SURFACE_BYTES).ok()?;
    // `(! t :attr v ..)` is `t` to carcara's parser.
    if fields.first().copied() == Some("!") {
        let body = fields.get(1)?;
        return read(body, depth + 1, budget);
    }
    if fields.first().copied() == Some("match") {
        return None;
    }
    budget.admit_items(fields.len())?;
    let items = fields
        .iter()
        .map(|field| read(field, depth + 1, budget))
        .collect::<Option<Vec<_>>>()?;
    Some(Sexp {
        span: text,
        node: Node::List(items),
    })
}

/// `|x|` read as `x` when `x` is a symbol AY would print bare — a legal
/// simple symbol that is not a reserved word ([`quote_symbol`] is the
/// authority: it returns its input unchanged exactly then). `|true|`, `|let|`
/// and every token with a delimiter inside keep their bars, so a quoted
/// reserved word is never identified with the keyword it spells.
pub(super) fn bare_symbol(text: &str) -> &str {
    text.strip_prefix('|')
        .and_then(|t| t.strip_suffix('|'))
        .filter(|inner| quote_symbol(inner) == *inner)
        .unwrap_or(text)
}

/// The binder names of a binding list `((x S) (y T) ..)` or a `let` list
/// `((x v) (y w) ..)`; `None` unless every entry is a pair-or-more whose head
/// is an atom.
fn binding_names<'s>(list: &'s Sexp<'_>) -> Option<Vec<&'s str>> {
    let Node::List(entries) = &list.node else {
        return None;
    };
    entries
        .iter()
        .map(|entry| match &entry.node {
            Node::List(fields) if fields.len() >= 2 => match &fields[0].node {
                Node::Atom(name) => Some(name.as_ref()),
                Node::List(_) => None,
            },
            _ => None,
        })
        .collect()
}

fn alpha_binding_names<'s>(
    left: &'s Sexp<'_>,
    right: &'s Sexp<'_>,
    budget: &mut Budget<'_>,
) -> Option<(Vec<&'s str>, Vec<&'s str>)> {
    let (Node::List(left_entries), Node::List(right_entries)) = (&left.node, &right.node) else {
        return None;
    };
    // Admit both name vectors and the two scope extensions before either is
    // allocated. A Sexp slot is larger than these two borrowed-name slots.
    budget.admit_items(left_entries.len().checked_add(right_entries.len())?)?;
    Some((binding_names(left)?, binding_names(right)?))
}

/// Every atom of `term`, over-approximating its free symbols.
fn atoms<'s>(term: &'s Sexp<'_>, out: &mut Vec<&'s str>) {
    match &term.node {
        Node::Atom(atom) => out.push(atom.as_ref()),
        Node::List(items) => items.iter().for_each(|item| atoms(item, out)),
    }
}

/// Capture-avoiding simultaneous substitution over a printed term, mirroring
/// carcara's `Substitution::apply`: a binder that rebinds a substituted
/// variable shadows it; a binder whose name is free in a substituted value is
/// renamed to a symbol no document can spell (`@` is not a simple-symbol
/// character), which the alpha-equivalent comparison then absorbs.
///
/// A `let` reached by the substitution declines (`None`). carcara 1.1.0's
/// `Substitution::apply` never applies the substitution to a `let`'s VALUES
/// (its `Term::Let` arm applies only the capture renaming to them, and
/// `can_skip_instead_of_renaming` records that "value lists" are "currently
/// not supported"), so the image it computes for `(let ((v (g x))) (>= v x))`
/// under `x := c` is `(let ((v (g x))) (>= v c))` — never the term AY prints.
/// MEASURED on the pinned build with a Skolemized `(not (forall ((z Int)) (or
/// (< z 0) (let ((gz (g z))) (>= gz z)))))`: `t1.t1` `refl`: reflexivity
/// failed; with the binder only in the `let`'s body (`(let ((zero 0)) (>= (g
/// z) (+ z zero)))`) the checker aborts (`called Option::unwrap() on a None
/// value`, `ast/substitution.rs`). Either way the step cannot check, and a
/// predicate that can only refuse refuses. A `let` INSIDE a substituted value
/// is untouched by this: carcara inserts the value verbatim, and the same
/// document's `forall_inst` steps at a `choice` whose body holds that `let`
/// were accepted once the two refused steps were holed.
fn substitute<'a>(
    term: &Sexp<'a>,
    substitution: &HashMap<String, Sexp<'a>>,
    fresh: &mut usize,
    depth: usize,
    budget: &mut Budget<'_>,
) -> Option<Sexp<'a>> {
    budget.charge()?;
    if depth > MAX_SURFACE_DEPTH {
        return None;
    }
    let items = match &term.node {
        Node::Atom(atom) => {
            return Some(
                substitution
                    .get(atom.as_ref())
                    .cloned()
                    .unwrap_or_else(|| term.clone()),
            );
        }
        Node::List(items) => items,
    };
    let head = match items.first().map(|item| &item.node) {
        Some(Node::Atom(head)) => Some(head.as_ref()),
        _ => None,
    };
    let is_binder = head.is_some_and(|head| BINDER_KEYWORDS.contains(&head));
    let is_let = head == Some("let");
    if is_let {
        // The pinned checker cannot substitute through a `let` (see above);
        // the honest floor for any step whose image this would be is the hole.
        return None;
    }
    if is_binder && items.len() == 3 {
        let names: Vec<String> = binding_names(&items[1])?
            .into_iter()
            .map(str::to_string)
            .collect();
        let mut inner = substitution.clone();
        let mut value_free: Vec<&str> = Vec::new();
        for value in substitution.values() {
            atoms(value, &mut value_free);
        }
        // (original binder, fresh name) for every binder a substituted value
        // would capture.
        let mut rebound: Vec<(String, String)> = Vec::new();
        for name in &names {
            if inner.remove(name).is_some() {
                continue;
            }
            if value_free.contains(&name.as_str()) {
                rebound.push((name.clone(), format!("@ay_capture_{fresh}")));
                *fresh += 1;
            }
        }
        let fresh_atom = |fresh_name: &str| Sexp {
            span: "",
            node: Node::Atom(Cow::Owned(fresh_name.to_string())),
        };
        // The binding list (sorts are untouched), with captured binders
        // renamed.
        let Node::List(entries) = &items[1].node else {
            return None;
        };
        let mut new_entries = Vec::with_capacity(entries.len());
        for entry in entries {
            let Node::List(fields) = &entry.node else {
                return None;
            };
            let Node::Atom(name) = &fields[0].node else {
                return None;
            };
            let mut new_fields = Vec::with_capacity(fields.len());
            let renamed = rebound
                .iter()
                .find(|(original, _)| original == name.as_ref());
            new_fields.push(match renamed {
                Some((_, fresh_name)) => fresh_atom(fresh_name),
                None => fields[0].clone(),
            });
            new_fields.extend(fields[1..].iter().cloned());
            new_entries.push(Sexp {
                span: entry.span,
                node: Node::List(new_fields),
            });
        }
        for (original, fresh_name) in &rebound {
            inner.insert(original.clone(), fresh_atom(fresh_name));
        }
        let body = substitute(&items[2], &inner, fresh, depth + 1, budget)?;
        return Some(Sexp {
            span: term.span,
            node: Node::List(vec![
                items[0].clone(),
                Sexp {
                    span: items[1].span,
                    node: Node::List(new_entries),
                },
                body,
            ]),
        });
    }
    let substituted = items
        .iter()
        .map(|item| substitute(item, substitution, fresh, depth + 1, budget))
        .collect::<Option<Vec<_>>>()?;
    Some(Sexp {
        span: term.span,
        node: Node::List(substituted),
    })
}

/// The carcara `DeBruijnMap`: one scope per binder, bound names looked up
/// innermost-first, compared by position.
#[derive(Default)]
struct BinderScopes<'s> {
    left: Vec<&'s str>,
    right: Vec<&'s str>,
}

impl BinderScopes<'_> {
    fn compare_atoms(&self, left: &str, right: &str, budget: &mut Budget<'_>) -> Option<bool> {
        let left_index = Self::position(&self.left, left, budget)?;
        let right_index = Self::position(&self.right, right, budget)?;
        Some(match (left_index, right_index) {
            (None, None) => {
                left == right || literal_spellings_agree_with_progress(left, right, budget)?
            }
            (Some(l), Some(r)) => l == r,
            _ => false,
        })
    }

    fn position(names: &[&str], name: &str, budget: &mut Budget<'_>) -> Option<Option<usize>> {
        for (index, candidate) in names.iter().enumerate().rev() {
            budget.compare_text(candidate, name)?;
            if *candidate == name {
                return Some(Some(index));
            }
        }
        Some(None)
    }
}

fn literal_spellings_agree_with_progress(
    left: &str,
    right: &str,
    budget: &mut Budget<'_>,
) -> Option<bool> {
    // Parsing decimal bit-vector numerals can be quadratic in their digit
    // count. Charge only a literal comparison that is actually attempted,
    // never the global alpha-equivalence node cap for an ordinary fold.
    budget.admit_literals(left, right)?;
    Some(literal_spellings_agree(left, right))
}

/// Two atoms carcara parses to one constant: alternate bit-vector literal
/// spellings, or an integral decimal against its integer.
fn literal_spellings_agree(left: &str, right: &str) -> bool {
    if let (Some(l), Some(r)) = (
        parse_printed_bitvec_literal(left),
        parse_printed_bitvec_literal(right),
    ) {
        return l == r;
    }
    match (integral_numeral(left), integral_numeral(right)) {
        (Some(l), Some(r)) => l == r,
        _ => false,
    }
}

/// The integer digits of a numeral or of a decimal with an all-zero fraction.
fn integral_numeral(text: &str) -> Option<&str> {
    let (digits, fraction) = text.split_once('.').unwrap_or((text, "0"));
    (!digits.is_empty()
        && digits.bytes().all(|b| b.is_ascii_digit())
        && !fraction.is_empty()
        && fraction.bytes().all(|b| b == b'0'))
    .then_some(digits)
}

/// carcara's `Polyeq` with `mod_reordering` and `alpha_equiv` on (`modulo`),
/// or with both off (syntactic identity), replayed over two printed terms.
fn alpha_equivalent<'s>(
    left: &'s Sexp<'_>,
    right: &'s Sexp<'_>,
    scopes: &mut BinderScopes<'s>,
    modulo: bool,
    depth: usize,
    budget: &mut Budget<'_>,
) -> Option<bool> {
    budget.charge()?;
    if depth > MAX_SURFACE_DEPTH {
        return None;
    }
    budget.compare_text(left.span, right.span)?;
    match (&left.node, &right.node) {
        (Node::Atom(l), Node::Atom(r)) if modulo => scopes.compare_atoms(l, r, budget),
        (Node::Atom(l), Node::Atom(r)) => {
            Some(l == r || literal_spellings_agree_with_progress(l, r, budget)?)
        }
        (Node::Atom(_), Node::List(_)) | (Node::List(_), Node::Atom(_)) => {
            budget.admit_literals(left.span, right.span)?;
            // `#x00` against `(_ bv0 8)`.
            Some(matches!(
                (
                    parse_printed_bitvec_literal(left.span),
                    parse_printed_bitvec_literal(right.span)
                ),
                (Some(l), Some(r)) if l == r
            ))
        }
        (Node::List(l), Node::List(r)) => {
            if l.len() != r.len() {
                return Some(false);
            }
            let head = match (l.first().map(|i| &i.node), r.first().map(|i| &i.node)) {
                (Some(Node::Atom(lh)), Some(Node::Atom(rh))) if lh == rh => Some(lh.as_ref()),
                _ => None,
            };
            if modulo && head == Some("=") && l.len() == 3 {
                let straight = alpha_equivalent(&l[1], &r[1], scopes, modulo, depth + 1, budget)?
                    && alpha_equivalent(&l[2], &r[2], scopes, modulo, depth + 1, budget)?;
                if straight {
                    return Some(true);
                }
                return Some(
                    alpha_equivalent(&l[1], &r[2], scopes, modulo, depth + 1, budget)?
                        && alpha_equivalent(&l[2], &r[1], scopes, modulo, depth + 1, budget)?,
                );
            }
            let binds = head.is_some_and(|h| BINDER_KEYWORDS.contains(&h) || h == "let");
            if modulo && binds && l.len() == 3 {
                let Some((left_names, right_names)) = alpha_binding_names(&l[1], &r[1], budget)
                else {
                    return if budget.refused { None } else { Some(false) };
                };
                if left_names.len() != right_names.len() {
                    return Some(false);
                }
                // Sorts (or `let` values) compare in the OUTER scope, then the
                // names are pushed and the bodies compare in the inner one.
                let (Node::List(le), Node::List(re)) = (&l[1].node, &r[1].node) else {
                    return Some(false);
                };
                for (left_entry, right_entry) in le.iter().zip(re) {
                    let (Node::List(lf), Node::List(rf)) = (&left_entry.node, &right_entry.node)
                    else {
                        return Some(false);
                    };
                    if lf.len() != rf.len() {
                        return Some(false);
                    }
                    for (lv, rv) in lf[1..].iter().zip(&rf[1..]) {
                        if !alpha_equivalent(lv, rv, scopes, modulo, depth + 1, budget)? {
                            return Some(false);
                        }
                    }
                }
                let pushed = left_names.len();
                scopes.left.extend(left_names);
                scopes.right.extend(right_names);
                let result = alpha_equivalent(&l[2], &r[2], scopes, modulo, depth + 1, budget);
                scopes.left.truncate(scopes.left.len() - pushed);
                scopes.right.truncate(scopes.right.len() - pushed);
                return result;
            }
            for (li, ri) in l.iter().zip(r) {
                if !alpha_equivalent(li, ri, scopes, modulo, depth + 1, budget)? {
                    return Some(false);
                }
            }
            Some(true)
        }
    }
}

/// Whether two printed terms are one term to carcara's `alpha_equiv`.
pub(super) fn printed_terms_alpha_equivalent(left: &str, right: &str) -> bool {
    let mut budget = Budget::default();
    let (Some(l), Some(r)) = (read(left, 0, &mut budget), read(right, 0, &mut budget)) else {
        return false;
    };
    alpha_equivalent(&l, &r, &mut BinderScopes::default(), true, 0, &mut budget).unwrap_or(false)
}

/// The same bounded judgement, charged to one borrowed owner during each
/// parse and comparison, including swapped-equality retries and its last poll.
pub(super) fn printed_terms_alpha_equivalent_with_progress(
    left: &str,
    right: &str,
    progress: &mut dyn FnMut(u64) -> bool,
) -> bool {
    let mut budget = Budget {
        progress: Some(progress),
        ..Budget::default()
    };
    let Some(l) = read(left, 0, &mut budget) else {
        return false;
    };
    let Some(r) = read(right, 0, &mut budget) else {
        return false;
    };
    alpha_equivalent(&l, &r, &mut BinderScopes::default(), true, 0, &mut budget) == Some(true)
        && budget.spend(0).is_some()
}

/// Whether two printed terms parse to the SAME term (carcara's `assert_eq`).
fn printed_terms_identical(left: &str, right: &str, budget: &mut Budget<'_>) -> Option<bool> {
    let (l, r) = (read(left, 0, budget)?, read(right, 0, budget)?);
    alpha_equivalent(&l, &r, &mut BinderScopes::default(), false, 0, budget)
}

/// The binder list of a printed quantifier, as `(name, sort text)` pairs.
fn printed_bindings(list: &str) -> Option<Vec<(String, String)>> {
    let entries = split_smt_terms(list.strip_prefix('(')?.strip_suffix(')')?)?;
    entries
        .iter()
        .map(|entry| {
            let fields = split_smt_terms(entry.strip_prefix('(')?.strip_suffix(')')?)?;
            let [name, sort] = fields.as_slice() else {
                return None;
            };
            Some((bare_symbol(name).to_string(), sort.clone()))
        })
        .collect()
}

/// Replay pinned carcara 1.1.0's `forall_inst`
/// (`carcara/src/checker/rules/quantifier.rs`) over the exact literal text and
/// `:args` a step is about to ship.
///
/// * one literal, of the form `(or (not (forall BINDINGS BODY)) RESULT)`;
/// * exactly one argument per binder, binders pairwise distinct (carcara
///   keys the substitution by variable, so a repeated binder would silently
///   drop an argument; refusing is the conservative reading);
/// * `RESULT` alpha-equivalent to `BODY` under the simultaneous substitution
///   of the printed arguments for the binders.
///
/// The binder sort check (`assert_eq(sort, &pool.sort(value))`) is not
/// replayed: the sorts are not recoverable from the printed argument, and the
/// term-level validator has already checked them on the same `TermId`s.
pub(super) fn printed_forall_inst_holds(literal: &str, args: &[&str]) -> bool {
    let mut budget = Budget::default();
    let Ok(disjuncts) = split_alethe_application_bounded(literal, "or", 2, MAX_SURFACE_BYTES)
    else {
        return false;
    };
    let [negated, result] = disjuncts.as_slice() else {
        return false;
    };
    let Ok(quantified) = split_alethe_application_bounded(negated, "not", 1, MAX_SURFACE_BYTES)
    else {
        return false;
    };
    let [quantified] = quantified.as_slice() else {
        return false;
    };
    let Ok(parts) = split_alethe_application_bounded(quantified, "forall", 2, MAX_SURFACE_BYTES)
    else {
        return false;
    };
    let [bindings, body] = parts.as_slice() else {
        return false;
    };
    let Some(bindings) = printed_bindings(bindings) else {
        return false;
    };
    if bindings.len() != args.len() || bindings.is_empty() {
        return false;
    }
    let mut substitution: HashMap<String, Sexp<'_>> = HashMap::default();
    for ((name, _sort), value) in bindings.iter().zip(args) {
        let Some(value) = read(value, 0, &mut budget) else {
            return false;
        };
        if substitution.insert(name.clone(), value).is_some() {
            return false;
        }
    }
    let (Some(body), Some(result)) = (read(body, 0, &mut budget), read(result, 0, &mut budget))
    else {
        return false;
    };
    let mut fresh = 0usize;
    let Some(expected) = substitute(&body, &substitution, &mut fresh, 0, &mut budget) else {
        return false;
    };
    alpha_equivalent(
        &expected,
        &result,
        &mut BinderScopes::default(),
        true,
        0,
        &mut budget,
    )
    .unwrap_or(false)
}

/// The printed pieces of one certified Skolem step, as the printer is about
/// to emit them.
pub(super) struct PrintedSkolemStep<'a> {
    /// `sko_forall` or `sko_ex`.
    pub rule: &'a str,
    /// The printed quantifier, `(forall ((x S)) BODY)` or the `exists` twin.
    pub quantified: &'a str,
    /// The anchor's binder token.
    pub binder: &'a str,
    /// The anchor's binder sort text.
    pub sort: &'a str,
    /// The anchor's `choice` term.
    pub choice: &'a str,
    /// The left side of the anchored `refl`.
    pub body: &'a str,
    /// The printed instance, right side of both the `refl` and the step.
    pub instance: &'a str,
}

/// Replay pinned carcara 1.1.0's `sko_forall` / `sko_ex`
/// (`generic_skolemization_rule`, `carcara/src/checker/rules/subproof.rs`) and
/// the anchored `refl` it closes over, on the exact text the three commands
/// ship.
///
/// * the printed quantifier is `(RULE-QUANTIFIER ((x S)) BODY)` with ONE
///   binder, and the anchor assigns exactly that `x` (`BindingIsNotInContext`
///   otherwise) at that sort;
/// * the `refl` step's left side IS `BODY` (`assert_eq(previous_equality.0,
///   phi)` is syntactic identity, not polyeq);
/// * the anchor's term is alpha-equivalent to `(choice ((x S)) (not BODY))`
///   for `sko_forall` and `(choice ((x S)) BODY)` for `sko_ex`;
/// * the printed instance is alpha-equivalent to `BODY[x := choice]`, which is
///   the anchored `refl` with the context applied to its left side.
pub(super) fn printed_skolem_step_holds(step: &PrintedSkolemStep<'_>) -> bool {
    let mut budget = Budget::default();
    let Some((binder, body)) = printed_skolem_frame(step, &mut budget) else {
        return false;
    };
    let (Some(body), Some(choice), Some(instance)) = (
        read(body, 0, &mut budget),
        read(step.choice, 0, &mut budget),
        read(step.instance, 0, &mut budget),
    ) else {
        return false;
    };
    let mut substitution: HashMap<String, Sexp<'_>> = HashMap::default();
    substitution.insert(binder, choice);
    let mut fresh = 0usize;
    let Some(expected) = substitute(&body, &substitution, &mut fresh, 0, &mut budget) else {
        return false;
    };
    alpha_equivalent(
        &expected,
        &instance,
        &mut BinderScopes::default(),
        true,
        0,
        &mut budget,
    )
    .unwrap_or(false)
}

/// The checks every printed Skolem step shares, whatever derives its
/// previous command: one binder, the anchor's binder and sort, the anchored
/// body identical to the quantifier's, and the `choice` the rule expects.
/// Returns that binder and the quantifier's printed body.
fn printed_skolem_frame<'a>(
    step: &PrintedSkolemStep<'a>,
    budget: &mut Budget<'_>,
) -> Option<(String, &'a str)> {
    let keyword = match step.rule {
        "sko_forall" => "forall",
        "sko_ex" => "exists",
        _ => return None,
    };
    let parts =
        split_alethe_application_bounded(step.quantified, keyword, 2, MAX_SURFACE_BYTES).ok()?;
    let [bindings, body] = parts.as_slice() else {
        return None;
    };
    let bindings = printed_bindings(bindings)?;
    let [(binder, sort)] = bindings.as_slice() else {
        return None;
    };
    if binder != bare_symbol(step.binder)
        || printed_terms_identical(sort, step.sort, budget) != Some(true)
        || printed_terms_identical(body, step.body, budget) != Some(true)
    {
        return None;
    }
    let expected_choice = if keyword == "forall" {
        format!("(choice (({binder} {sort})) (not {body}))")
    } else {
        format!("(choice (({binder} {sort})) {body})")
    };
    printed_terms_alpha_equivalent(step.choice, &expected_choice).then(|| (binder.clone(), *body))
}

/// The same rule closed over a CONSTANT instead of the substitution image
/// (`constant_skolem_bridge.rs`): carcara's `generic_skolemization_rule`
/// asserts only that the previous command is `(= phi psi)` with `phi` the
/// quantifier's body and `psi` the step's right side, and Clean's export
/// guard that `psi` does not mention the binder.
///
/// * the frame [`printed_skolem_step_holds`] checks (quantifier, binder,
///   sort, anchored body, `choice`);
/// * `last_bridge`, the command the closing step follows, is `(= BODY b)`
///   with `BODY` the printed quantifier body BYTE FOR BYTE (stricter than
///   the checker's parsed `assert_eq`);
/// * `b` is `true` or `false`, and the printed instance is exactly `b`.
pub(super) fn printed_constant_skolem_step_holds(
    step: &PrintedSkolemStep<'_>,
    last_bridge: &str,
) -> bool {
    let mut budget = Budget::default();
    let Some((_, body)) = printed_skolem_frame(step, &mut budget) else {
        return false;
    };
    let Ok(sides) = split_alethe_application_bounded(last_bridge, "=", 2, MAX_SURFACE_BYTES) else {
        return false;
    };
    let [left, right] = sides.as_slice() else {
        return false;
    };
    *left == body && matches!(*right, "true" | "false") && step.instance == *right
}

#[cfg(test)]
#[path = "alethe_printer_quantifier_surface_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "alethe_printer_quantifier_surface_progress_tests.rs"]
mod progress_tests;
