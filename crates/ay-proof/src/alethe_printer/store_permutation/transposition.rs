// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One checked adjacent-transposition derivation.

use super::super::*;

struct TranspositionTerms<'a> {
    tag: &'a str,
    premise: &'a str,
    rest: &'a str,
    jo: &'a str,
    wo: &'a str,
    ii: &'a str,
    vi: &'a str,
    before: String,
    after: String,
    inner_left: String,
    inner_right: String,
    witness: String,
    selected: String,
    eq_outer: String,
    eq_inner: String,
    not_outer: String,
    not_inner: String,
    nf: String,
}

/// Emit one adjacent transposition
/// `store(store(X,ii,vi),jo,wo) = store(store(X,jo,wo),ii,vi)` as a
/// self-contained subproof under step name `tag`.
///
/// `premise` names the clause assumption `(not (= dl dr))` with
/// `{dl, dr} == {ii, jo}`; that disequality refutes the case in which the
/// extensionality witness equals both indices.
#[allow(clippy::too_many_arguments)]
pub(super) fn write_store_transposition(
    output: &mut String,
    tag: &str,
    rest: &str,
    outer: &(String, String),
    inner: &(String, String),
    index_sort: &str,
    premise: &str,
    diseq: (&str, &str),
    id: ProofId,
) -> Option<(String, String)> {
    let terms = TranspositionTerms::new(tag, rest, outer, inner, index_sort, premise, id);
    write_opening(output, &terms);
    write_misses_both_case(output, &terms);
    write_outer_index_case(output, &terms);
    write_inner_index_case(output, &terms);
    write_both_indices_case(output, &terms, diseq)?;
    write_closing(output, &terms);
    Some((terms.before, terms.after))
}

impl<'a> TranspositionTerms<'a> {
    #[allow(clippy::too_many_arguments)]
    fn new(
        tag: &'a str,
        rest: &'a str,
        outer: &'a (String, String),
        inner: &'a (String, String),
        index_sort: &str,
        premise: &'a str,
        id: ProofId,
    ) -> Self {
        let (jo, wo) = (&outer.0, &outer.1);
        let (ii, vi) = (&inner.0, &inner.1);
        let before = format!("(store (store {rest} {ii} {vi}) {jo} {wo})");
        let after = format!("(store (store {rest} {jo} {wo}) {ii} {vi})");
        let inner_left = format!("(store {rest} {ii} {vi})");
        let inner_right = format!("(store {rest} {jo} {wo})");
        let binder = EXT_CHOICE_BINDER;
        let witness = format!(
            "(choice (({binder} {index_sort})) (or (= {before} {after}) \
             (not (= (select {before} {binder}) (select {after} {binder})))))"
        );
        let selected = format!("(= (select {before} {witness}) (select {after} {witness}))");
        let eq_outer = format!("(= {jo} {witness})");
        let eq_inner = format!("(= {ii} {witness})");
        let not_outer = format!("(not {eq_outer})");
        let not_inner = format!("(not {eq_inner})");
        Self {
            tag,
            premise,
            rest,
            jo,
            wo,
            ii,
            vi,
            before,
            after,
            inner_left,
            inner_right,
            witness,
            selected,
            eq_outer,
            eq_inner,
            not_outer,
            not_inner,
            nf: format!("{id}.nf"),
        }
    }
}

fn write_opening(output: &mut String, terms: &TranspositionTerms<'_>) {
    let TranspositionTerms {
        tag,
        before,
        after,
        selected,
        ..
    } = terms;
    output.push_str(&format!(
        "(anchor :step {tag}.sp0)\n\
         (assume {tag}.h (not (= {before} {after})))\n\
         (step {tag}.ext (cl (not {selected})) :rule arrays_ext :premises ({tag}.h))\n"
    ));
}

fn write_misses_both_case(output: &mut String, terms: &TranspositionTerms<'_>) {
    let TranspositionTerms {
        tag,
        rest,
        before,
        after,
        inner_left,
        inner_right,
        witness,
        selected,
        eq_outer,
        eq_inner,
        not_outer,
        not_inner,
        nf,
        ..
    } = terms;
    output.push_str(&format!(
        "(anchor :step {tag}.nn0)\n\
         (assume {tag}.nn.j {not_outer})\n\
         (assume {tag}.nn.i {not_inner})\n\
         (step {tag}.nn.1 (cl (= (select {before} {witness}) (select {inner_left} {witness}))) :rule arrays_row :premises ({tag}.nn.j))\n\
         (step {tag}.nn.2 (cl (= (select {inner_left} {witness}) (select {rest} {witness}))) :rule arrays_row :premises ({tag}.nn.i))\n\
         (step {tag}.nn.3 (cl (= (select {before} {witness}) (select {rest} {witness}))) :rule trans :premises ({tag}.nn.1 {tag}.nn.2))\n\
         (step {tag}.nn.4 (cl (= (select {after} {witness}) (select {inner_right} {witness}))) :rule arrays_row :premises ({tag}.nn.i))\n\
         (step {tag}.nn.5 (cl (= (select {inner_right} {witness}) (select {rest} {witness}))) :rule arrays_row :premises ({tag}.nn.j))\n\
         (step {tag}.nn.6 (cl (= (select {after} {witness}) (select {rest} {witness}))) :rule trans :premises ({tag}.nn.4 {tag}.nn.5))\n\
         (step {tag}.nn.7 (cl (= (select {rest} {witness}) (select {after} {witness}))) :rule symm :premises ({tag}.nn.6))\n\
         (step {tag}.nn.8 (cl {selected}) :rule trans :premises ({tag}.nn.3 {tag}.nn.7))\n\
         (step {tag}.nn.9 (cl) :rule resolution :premises ({tag}.ext {tag}.nn.8))\n\
         (step {tag}.nn0 (cl (not {not_outer}) (not {not_inner}) false) :rule subproof :discharge ({tag}.nn.j {tag}.nn.i))\n\
         (step {tag}.nn1 (cl (not {not_outer}) (not {not_inner})) :rule resolution :premises ({tag}.nn0 {nf}))\n\
         (step {tag}.na (cl (not (not {not_outer})) {eq_outer}) :rule not_not)\n\
         (step {tag}.nb (cl (not (not {not_inner})) {eq_inner}) :rule not_not)\n\
         (step {tag}.nn2 (cl (not {not_inner}) {eq_outer}) :rule resolution :premises ({tag}.nn1 {tag}.na))\n\
         (step {tag}.nnR (cl {eq_outer} {eq_inner}) :rule resolution :premises ({tag}.nn2 {tag}.nb))\n"
    ));
}

fn write_outer_index_case(output: &mut String, terms: &TranspositionTerms<'_>) {
    let TranspositionTerms {
        tag,
        jo,
        wo,
        before,
        after,
        inner_right,
        witness,
        selected,
        eq_outer,
        eq_inner,
        not_inner,
        nf,
        ..
    } = terms;
    output.push_str(&format!(
        "(anchor :step {tag}.pj0)\n\
         (assume {tag}.pj.j {eq_outer})\n\
         (assume {tag}.pj.i {not_inner})\n\
         (step {tag}.pj.1 (cl (= (select {before} {jo}) {wo})) :rule arrays_idx)\n\
         (step {tag}.pj.2 (cl (= (select {before} {jo}) (select {before} {witness}))) :rule cong :premises ({tag}.pj.j))\n\
         (step {tag}.pj.3 (cl (= (select {before} {witness}) (select {before} {jo}))) :rule symm :premises ({tag}.pj.2))\n\
         (step {tag}.pj.4 (cl (= (select {before} {witness}) {wo})) :rule trans :premises ({tag}.pj.3 {tag}.pj.1))\n\
         (step {tag}.pj.5 (cl (= (select {after} {witness}) (select {inner_right} {witness}))) :rule arrays_row :premises ({tag}.pj.i))\n\
         (step {tag}.pj.6 (cl (= (select {inner_right} {jo}) {wo})) :rule arrays_idx)\n\
         (step {tag}.pj.7 (cl (= (select {inner_right} {jo}) (select {inner_right} {witness}))) :rule cong :premises ({tag}.pj.j))\n\
         (step {tag}.pj.8 (cl (= (select {inner_right} {witness}) (select {inner_right} {jo}))) :rule symm :premises ({tag}.pj.7))\n\
         (step {tag}.pj.9 (cl (= (select {inner_right} {witness}) {wo})) :rule trans :premises ({tag}.pj.8 {tag}.pj.6))\n\
         (step {tag}.pj.10 (cl (= (select {after} {witness}) {wo})) :rule trans :premises ({tag}.pj.5 {tag}.pj.9))\n\
         (step {tag}.pj.11 (cl (= {wo} (select {after} {witness}))) :rule symm :premises ({tag}.pj.10))\n\
         (step {tag}.pj.12 (cl {selected}) :rule trans :premises ({tag}.pj.4 {tag}.pj.11))\n\
         (step {tag}.pj.13 (cl) :rule resolution :premises ({tag}.ext {tag}.pj.12))\n\
         (step {tag}.pj0 (cl (not {eq_outer}) (not {not_inner}) false) :rule subproof :discharge ({tag}.pj.j {tag}.pj.i))\n\
         (step {tag}.pj1 (cl (not {eq_outer}) (not {not_inner})) :rule resolution :premises ({tag}.pj0 {nf}))\n\
         (step {tag}.pjR (cl (not {eq_outer}) {eq_inner}) :rule resolution :premises ({tag}.pj1 {tag}.nb))\n"
    ));
}

fn write_inner_index_case(output: &mut String, terms: &TranspositionTerms<'_>) {
    let TranspositionTerms {
        tag,
        ii,
        vi,
        before,
        after,
        inner_left,
        witness,
        selected,
        eq_outer,
        eq_inner,
        not_outer,
        nf,
        ..
    } = terms;
    output.push_str(&format!(
        "(anchor :step {tag}.pi0)\n\
         (assume {tag}.pi.i {eq_inner})\n\
         (assume {tag}.pi.j {not_outer})\n\
         (step {tag}.pi.1 (cl (= (select {before} {witness}) (select {inner_left} {witness}))) :rule arrays_row :premises ({tag}.pi.j))\n\
         (step {tag}.pi.2 (cl (= (select {inner_left} {ii}) {vi})) :rule arrays_idx)\n\
         (step {tag}.pi.3 (cl (= (select {inner_left} {ii}) (select {inner_left} {witness}))) :rule cong :premises ({tag}.pi.i))\n\
         (step {tag}.pi.4 (cl (= (select {inner_left} {witness}) (select {inner_left} {ii}))) :rule symm :premises ({tag}.pi.3))\n\
         (step {tag}.pi.5 (cl (= (select {inner_left} {witness}) {vi})) :rule trans :premises ({tag}.pi.4 {tag}.pi.2))\n\
         (step {tag}.pi.6 (cl (= (select {before} {witness}) {vi})) :rule trans :premises ({tag}.pi.1 {tag}.pi.5))\n\
         (step {tag}.pi.7 (cl (= (select {after} {ii}) {vi})) :rule arrays_idx)\n\
         (step {tag}.pi.8 (cl (= (select {after} {ii}) (select {after} {witness}))) :rule cong :premises ({tag}.pi.i))\n\
         (step {tag}.pi.9 (cl (= {vi} (select {after} {ii}))) :rule symm :premises ({tag}.pi.7))\n\
         (step {tag}.pi.10 (cl (= {vi} (select {after} {witness}))) :rule trans :premises ({tag}.pi.9 {tag}.pi.8))\n\
         (step {tag}.pi.11 (cl {selected}) :rule trans :premises ({tag}.pi.6 {tag}.pi.10))\n\
         (step {tag}.pi.12 (cl) :rule resolution :premises ({tag}.ext {tag}.pi.11))\n\
         (step {tag}.pi0 (cl (not {eq_inner}) (not {not_outer}) false) :rule subproof :discharge ({tag}.pi.i {tag}.pi.j))\n\
         (step {tag}.pi1 (cl (not {eq_inner}) (not {not_outer})) :rule resolution :premises ({tag}.pi0 {nf}))\n\
         (step {tag}.piR (cl (not {eq_inner}) {eq_outer}) :rule resolution :premises ({tag}.pi1 {tag}.na))\n"
    ));
}

fn write_both_indices_case(
    output: &mut String,
    terms: &TranspositionTerms<'_>,
    diseq: (&str, &str),
) -> Option<()> {
    let TranspositionTerms {
        tag,
        premise,
        jo,
        ii,
        witness,
        eq_outer,
        eq_inner,
        nf,
        ..
    } = terms;
    let (contradiction, chained, flipped, flipped_conclusion) = match diseq {
        (lhs, rhs) if (lhs, rhs) == (*ii, *jo) => (
            format!("(= {ii} {jo})"),
            format!("{tag}.pp.i"),
            format!("{tag}.pp.j"),
            format!("(= {witness} {jo})"),
        ),
        (lhs, rhs) if (lhs, rhs) == (*jo, *ii) => (
            format!("(= {jo} {ii})"),
            format!("{tag}.pp.j"),
            format!("{tag}.pp.i"),
            format!("(= {witness} {ii})"),
        ),
        _ => return None,
    };
    output.push_str(&format!(
        "(anchor :step {tag}.pp0)\n\
         (assume {tag}.pp.i {eq_inner})\n\
         (assume {tag}.pp.j {eq_outer})\n\
         (step {tag}.pp.1 (cl {flipped_conclusion}) :rule symm :premises ({flipped}))\n\
         (step {tag}.pp.2 (cl {contradiction}) :rule trans :premises ({chained} {tag}.pp.1))\n\
         (step {tag}.pp.3 (cl) :rule resolution :premises ({premise} {tag}.pp.2))\n\
         (step {tag}.pp0 (cl (not {eq_inner}) (not {eq_outer}) false) :rule subproof :discharge ({tag}.pp.i {tag}.pp.j))\n\
         (step {tag}.ppR (cl (not {eq_inner}) (not {eq_outer})) :rule resolution :premises ({tag}.pp0 {nf}))\n"
    ));
    Some(())
}

fn write_closing(output: &mut String, terms: &TranspositionTerms<'_>) {
    let TranspositionTerms {
        tag,
        before,
        after,
        eq_inner,
        nf,
        ..
    } = terms;
    output.push_str(&format!(
        "(step {tag}.r1 (cl {eq_inner}) :rule resolution :premises ({tag}.nnR {tag}.pjR))\n\
         (step {tag}.r2 (cl (not {eq_inner})) :rule resolution :premises ({tag}.piR {tag}.ppR))\n\
         (step {tag}.bot (cl) :rule resolution :premises ({tag}.r1 {tag}.r2))\n\
         (step {tag}.sp0 (cl (not (not (= {before} {after}))) false) :rule subproof :discharge ({tag}.h))\n\
         (step {tag}.sp (cl (not (not (= {before} {after})))) :rule resolution :premises ({tag}.sp0 {nf}))\n\
         (step {tag}.nn3 (cl (not (not (not (= {before} {after})))) (= {before} {after})) :rule not_not)\n\
         (step {tag} (cl (= {before} {after})) :rule resolution :premises ({tag}.sp {tag}.nn3))\n"
    ));
}
