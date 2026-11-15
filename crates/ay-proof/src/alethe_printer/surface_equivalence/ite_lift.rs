// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An authored atom over a term-level `ite` against its Shannon-lifted
//! canonical formula.
//!
//! Elaboration lifts `(P .. (ite c a b) ..)` to the FORMULA
//! `(ite c' (P .. a ..) (P .. b ..))`, possibly re-spelling each atom
//! (`(= k 1)` as `(= 1 k)`). The array-frame update axiom
//! `forall k. snew[k] = ite(k = 1, val, s[k])` is the measured case: its
//! instance at `0` is AUTHORED as
//! `(= (select snew 0) (ite (= 0 1) val (select s 0)))`, the text pinned
//! carcara's `forall_inst` needs, while AY's own instance is
//! `(ite (= 1 0) (= val (select snew 0)) (= (select snew 0) (select s 0)))`,
//! which the refutation consumes with `ite1` / `ite2`. Without this schema the
//! instance could not be confined to its `forall_inst`
//! (`confined_forall_instance`), the authored text leaked into those steps,
//! and carcara refused the document: "term `(= (select snew 0) (ite ..))` is
//! of the wrong form, expected `(ite phi_1 phi_2 phi_3)`".
//!
//! No single pinned-carcara rule relates the two. With `S = (P .. s ..)`,
//! `s = (ite c a b)`, `Sa` / `Sb` the application with `a` / `b` for `s`, and
//! `L = (ite c Sa Sb)`:
//!
//! ```text
//! (cl (ite c (= s a) (= s b)))    ite_intro over (= s s), eq_reflexive,
//!                                 equiv_pos2, resolution, and
//! (cl (not c) (= s a)), (cl c (= s b))            ite2, ite1
//! (cl (not (= u u)).. (not (= s a)) (not S) Sa) and its three siblings
//!                                 eq_congruent_pred (+ eq_reflexive per u)
//! (cl (not S) L), (cl S (not L))  ite_pos1/2, ite_neg1/2, resolution
//! (cl (= S L))                    equiv_neg1, equiv_neg2, resolution
//! (cl (= S C))                    (= L C) by the general schemas, then trans
//! ```
//!
//! Every step is an instance of its rule over the exact text it prints. Only a
//! Boolean canonical `ite`, a plain-symbol non-connective head with the `ite`
//! as a DIRECT argument, an un-negated condition, and pairwise distinct atoms
//! are attempted (so no resolution can meet a second, accidental pivot);
//! anything else declines and the caller keeps its existing refusal.

use super::super::*;
use super::{CanonicalNode, Derivation};

/// Heads carcara's `eq_congruent_pred` reads as ONE application with
/// positional arguments, and that the lift distributes over: a plain (possibly
/// quoted) symbol that is neither a Boolean connective nor a binder.
fn liftable_head(head: &str) -> bool {
    !head.starts_with('(')
        && !super::is_binding_head(head)
        && !matches!(head, "not" | "and" | "or" | "=>" | "xor" | "ite")
}

/// `text` with every leading `(not ..)` removed, in the spelling the external
/// checker's parser interns (so two texts it reads as one atom collide here).
fn atom_of(text: &str) -> String {
    let mut current = text.to_string();
    while let Some(inner) = split_application(&current, "not") {
        let [inner] = inner.as_slice() else {
            break;
        };
        current = inner.clone();
    }
    let mut nodes = 0usize;
    printed_resolution::normalise_printed_spelling(&current, 0, &mut nodes)
}

/// The printed pieces of one lift of the `ite` argument at one position.
struct LiftShape<'a> {
    surface: &'a str,
    ite: &'a str,
    condition: String,
    then_value: String,
    else_value: String,
    then_atom: String,
    else_atom: String,
    lifted: String,
    /// Distinct texts of the arguments the lift leaves in place.
    kept: Vec<&'a str>,
    /// `eq_congruent_pred` hypotheses, positionally, for each branch value.
    then_hypotheses: String,
    else_hypotheses: String,
}

impl<'a> LiftShape<'a> {
    fn new(head: &str, surface: &'a str, args: &'a [String], position: usize) -> Option<Self> {
        let ite = args.get(position)?.as_str();
        let parts = split_application(ite, "ite")?;
        let [condition, then_value, else_value] = parts.as_slice() else {
            return None;
        };
        if split_application(condition, "not").is_some() {
            return None;
        }
        let replaced = |value: &str| -> String {
            let fields: Vec<&str> = args
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    if index == position {
                        value
                    } else {
                        arg.as_str()
                    }
                })
                .collect();
            format!("({head} {})", fields.join(" "))
        };
        let hypotheses = |value: &str| -> String {
            args.iter()
                .enumerate()
                .map(|(index, arg)| {
                    if index == position {
                        format!("(not (= {ite} {value}))")
                    } else {
                        format!("(not (= {arg} {arg}))")
                    }
                })
                .collect::<Vec<_>>()
                .join(" ")
        };
        let then_atom = replaced(then_value);
        let else_atom = replaced(else_value);
        let mut kept: Vec<&str> = Vec::new();
        for (index, arg) in args.iter().enumerate() {
            if index != position && !kept.contains(&arg.as_str()) {
                kept.push(arg.as_str());
            }
        }
        let shape = Self {
            surface,
            ite,
            lifted: format!("(ite {condition} {then_atom} {else_atom})"),
            then_hypotheses: hypotheses(then_value),
            else_hypotheses: hypotheses(else_value),
            condition: condition.clone(),
            then_value: then_value.clone(),
            else_value: else_value.clone(),
            then_atom,
            else_atom,
            kept,
        };
        shape.atoms_are_distinct().then_some(shape)
    }

    /// Every literal the derivation resolves on names a DIFFERENT atom, so
    /// each resolution has exactly the one pivot it is written for.
    fn atoms_are_distinct(&self) -> bool {
        let mut atoms: Vec<String> = vec![
            atom_of(&self.condition),
            atom_of(self.surface),
            atom_of(&self.lifted),
            atom_of(&self.then_atom),
            atom_of(&self.else_atom),
            atom_of(&format!("(= {} {})", self.ite, self.then_value)),
            atom_of(&format!("(= {} {})", self.ite, self.else_value)),
        ];
        atoms.extend(
            self.kept
                .iter()
                .map(|arg| atom_of(&format!("(= {arg} {arg})"))),
        );
        let count = atoms.len();
        atoms.sort_unstable();
        atoms.dedup();
        atoms.len() == count
    }
}

impl AlethePrinter<'_> {
    /// `(= surface canonical)` when `canonical` is a Boolean `ite` and
    /// `surface` is an atom over a term-level `ite` whose lift reaches it.
    pub(super) fn ite_lift_equivalence(
        &self,
        id: &str,
        surface: &str,
        canonical: CanonicalNode<'_>,
        depth: usize,
        derivation: &mut Derivation,
    ) -> bool {
        if *self.terms.sort(canonical.term) != Sort::Bool
            || !matches!(self.terms.get(canonical.term), TermData::Ite(..))
            || split_application(canonical.text, "ite").is_none_or(|parts| parts.len() != 3)
        {
            return false;
        }
        let Some(head) = printed_head_symbol(surface).filter(|head| liftable_head(head)) else {
            return false;
        };
        let Some(args) = split_application(surface, &head) else {
            return false;
        };
        for position in 0..args.len() {
            let Some(shape) = LiftShape::new(&head, surface, &args, position) else {
                continue;
            };
            let checkpoint = derivation.steps.len();
            if self.emit_ite_lift(id, &shape, canonical, depth, derivation) {
                return true;
            }
            derivation.steps.truncate(checkpoint);
        }
        false
    }

    fn emit_ite_lift(
        &self,
        id: &str,
        shape: &LiftShape<'_>,
        canonical: CanonicalNode<'_>,
        depth: usize,
        derivation: &mut Derivation,
    ) -> bool {
        // The lifted text may already BE the document's canonical text;
        // otherwise it reaches it through a derived equality.
        if shape.lifted == canonical.text {
            emit_lift_steps(id, shape, &mut derivation.steps);
            return true;
        }
        let leg = format!("{id}.lc");
        if !self.derive_printed_equivalence(&leg, &shape.lifted, canonical, depth + 1, derivation) {
            return false;
        }
        let lifted_id = format!("{id}.sl");
        emit_lift_steps(&lifted_id, shape, &mut derivation.steps);
        derivation.steps.push(format!(
            "(step {id} (cl (= {} {})) :rule trans :premises ({lifted_id} {leg}))",
            shape.surface, canonical.text
        ));
        true
    }
}

/// The steps concluding `(cl (= S L))` under `id`.
fn emit_lift_steps(id: &str, shape: &LiftShape<'_>, steps: &mut Vec<String>) {
    let reflexivities = emit_branch_facts(id, shape, steps);
    emit_lift_resolutions(id, shape, &reflexivities, steps);
}

/// The branch clauses of the `ite` definition and the four congruence
/// clauses. Returns the reflexivity step ids the congruences need resolved.
fn emit_branch_facts(id: &str, shape: &LiftShape<'_>, steps: &mut Vec<String>) -> String {
    let LiftShape {
        surface,
        ite,
        condition,
        then_value,
        else_value,
        then_atom,
        else_atom,
        kept,
        then_hypotheses,
        else_hypotheses,
        ..
    } = shape;
    super::super::ite_branch_projection::emit_definition_branches(
        id,
        ite,
        condition,
        then_value,
        else_value,
        super::super::ite_branch_projection::EqualityOrientation::IteFirst,
        steps,
    );
    let mut reflexivities = Vec::with_capacity(kept.len());
    for (index, arg) in kept.iter().enumerate() {
        steps.push(format!(
            "(step {id}.r{index} (cl (= {arg} {arg})) :rule eq_reflexive)"
        ));
        reflexivities.push(format!("{id}.r{index}"));
    }
    // Congruence both ways for each branch value.
    for (tag, hypotheses, from, to) in [
        ("ga", then_hypotheses, *surface, then_atom.as_str()),
        ("gA", then_hypotheses, then_atom.as_str(), *surface),
        ("gb", else_hypotheses, *surface, else_atom.as_str()),
        ("gB", else_hypotheses, else_atom.as_str(), *surface),
    ] {
        steps.push(format!(
            "(step {id}.{tag} (cl {hypotheses} (not {from}) {to}) :rule eq_congruent_pred)"
        ));
    }
    reflexivities.join(" ")
}

/// The `ite` tautologies of `L` and the resolutions down to `(cl (= S L))`.
fn emit_lift_resolutions(
    id: &str,
    shape: &LiftShape<'_>,
    reflexivities: &str,
    steps: &mut Vec<String>,
) {
    let LiftShape {
        surface,
        condition,
        then_atom,
        else_atom,
        lifted,
        ..
    } = shape;
    steps.push(format!(
        "(step {id}.p1 (cl (not {lifted}) {condition} {else_atom}) :rule ite_pos1)"
    ));
    steps.push(format!(
        "(step {id}.p2 (cl (not {lifted}) (not {condition}) {then_atom}) :rule ite_pos2)"
    ));
    steps.push(format!(
        "(step {id}.n1 (cl {lifted} {condition} (not {else_atom})) :rule ite_neg1)"
    ));
    steps.push(format!(
        "(step {id}.n2 (cl {lifted} (not {condition}) (not {then_atom})) :rule ite_neg2)"
    ));
    let chain = |branch: &str, congruence: &str, tautology: &str| -> String {
        let mut premises = format!("{id}.{branch} {id}.{congruence}");
        if !reflexivities.is_empty() {
            premises.push(' ');
            premises.push_str(reflexivities);
        }
        format!("{premises} {id}.{tautology}")
    };
    // (cl (not S) L) and (cl S (not L)), one branch at a time.
    for (tag, clause, premises) in [
        (
            "fa",
            format!("(not {condition}) (not {surface}) {lifted}"),
            chain("t", "ga", "n2"),
        ),
        (
            "fb",
            format!("{condition} (not {surface}) {lifted}"),
            chain("f", "gb", "n1"),
        ),
        (
            "ba",
            format!("(not {condition}) {surface} (not {lifted})"),
            chain("t", "gA", "p2"),
        ),
        (
            "bb",
            format!("{condition} {surface} (not {lifted})"),
            chain("f", "gB", "p1"),
        ),
    ] {
        steps.push(format!(
            "(step {id}.{tag} (cl {clause}) :rule resolution :premises ({premises}))"
        ));
    }
    steps.push(format!(
        "(step {id}.fw (cl (not {surface}) {lifted}) :rule resolution :premises ({id}.fa {id}.fb))"
    ));
    steps.push(format!(
        "(step {id}.bw (cl {surface} (not {lifted})) :rule resolution :premises ({id}.ba {id}.bb))"
    ));
    let equality = format!("(= {surface} {lifted})");
    steps.push(format!(
        "(step {id}.q1 (cl {equality} (not {surface}) (not {lifted})) :rule equiv_neg1)"
    ));
    steps.push(format!(
        "(step {id}.q2 (cl {equality} {surface} {lifted}) :rule equiv_neg2)"
    ));
    steps.push(format!(
        "(step {id}.e1 (cl {equality} {lifted}) :rule resolution :premises ({id}.q2 {id}.fw))"
    ));
    steps.push(format!(
        "(step {id}.e2 (cl {equality} (not {lifted})) :rule resolution :premises ({id}.q1 {id}.bw))"
    ));
    steps.push(format!(
        "(step {id} (cl {equality}) :rule resolution :premises ({id}.e1 {id}.e2))"
    ));
}

#[cfg(test)]
mod tests;
