// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked Alethe lowering for n-ary array store permutations.

use super::*;

#[path = "store_permutation/transposition.rs"]
mod transposition;

use transposition::write_store_transposition;

type PrintedEntry = (String, String);
type DisequalityMap = HashMap<(String, String), (String, String, String)>;
type Segment = (String, String, String);

struct PrintedPermutation {
    literals: Vec<String>,
    base: String,
    left: Vec<PrintedEntry>,
    right: Vec<PrintedEntry>,
    left_text: String,
    right_text: String,
    disequalities: DisequalityMap,
    index_sort: String,
    row_position: usize,
}

impl AlethePrinter<'_> {
    /// Lower AY's internally checked n-ary STORE-PERMUTATION lemma to the
    /// array rules the pinned Carcara dialect actually implements.
    ///
    /// Carcara has no `store_permutation` rule, so this is a DERIVATION, not a
    /// rename. Two chains that write the same `(index, value)` multiset over one
    /// base differ only by a permutation of pairwise-distinct indices, and each
    /// permutation factors into adjacent transpositions. Every transposition is
    /// proved by refutation with Carcara's `arrays_ext`, `arrays_row`, and
    /// `arrays_idx` primitives, then lifted and composed with `cong` and `trans`.
    ///
    /// Returns `None` — an honest `hole` — whenever the printed clause is not
    /// exactly the schema this derivation proves. Every term is re-read from the
    /// clause and checked against its printed spelling, so a surface override
    /// cannot redirect the derivation to a different claim.
    pub(super) fn format_array_store_permutation(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        let printed = decode_printed_permutation(self, id, clause)?;
        let swaps = adjacent_transposition_schedule(&printed.left, &printed.right)?;
        // An identity permutation has no transposition to derive.
        if swaps.is_empty() {
            return None;
        }

        let mut output = String::new();
        output.push_str(&format!("(step {id}.nf (cl (not false)) :rule false)\n"));
        output.push_str(&format!("(anchor :step {id}.sp0)\n"));
        for (position, literal) in printed.literals.iter().enumerate() {
            output.push_str(&format!("(assume {id}.a{position} (not {literal}))\n"));
        }

        let segments = write_swap_segments(&mut output, id, &printed, &swaps)?;
        let chain_step = compose_segments(&mut output, id, &printed, &segments)?;
        write_clause_discharge(&mut output, self, id, clause, &printed, &chain_step)?;
        output.pop();
        Some(output)
    }
}

fn decode_printed_permutation(
    printer: &AlethePrinter<'_>,
    id: ProofId,
    clause: &[TermId],
) -> Option<PrintedPermutation> {
    let shape = crate::checker::array_store_permutation_printer_terms(printer.terms, clause)?;
    // The derivation inlines chains below an `arrays_ext` choice binder named
    // `x`; any free occurrence would be captured and must keep the honest hole.
    if term_mentions_symbol(printer.terms, shape.left_array, EXT_CHOICE_BINDER)
        || term_mentions_symbol(printer.terms, shape.right_array, EXT_CHOICE_BINDER)
    {
        return None;
    }

    let literals: Vec<String> = clause.iter().map(|&lit| printer.format_term(lit)).collect();
    let literals_are_unique = {
        let unique: HashSet<&String> = literals.iter().collect();
        unique.len() == literals.len()
    };
    if !literals_are_unique {
        return None;
    }
    let base = printer.format_term(shape.base);
    let format_entries = |entries: &[(TermId, TermId)]| -> Vec<PrintedEntry> {
        entries
            .iter()
            .map(|&(index, value)| (printer.format_term(index), printer.format_term(value)))
            .collect()
    };
    let left = format_entries(&shape.left);
    let right = format_entries(&shape.right);
    let indices_are_distinct = {
        let distinct: HashSet<&String> = left.iter().map(|(index, _)| index).collect();
        distinct.len() == left.len()
    };
    if !indices_are_distinct {
        return None;
    }

    let left_text = store_chain_text(&base, &left);
    let right_text = store_chain_text(&base, &right);
    if printer.format_term(shape.left_array) != left_text
        || printer.format_term(shape.right_array) != right_text
        || literals[shape.row_position] != format!("(= {left_text} {right_text})")
    {
        return None;
    }
    let disequalities =
        collect_printed_disequalities(printer, id, &literals, &shape.index_equalities)?;
    Some(PrintedPermutation {
        literals,
        base,
        left,
        right,
        left_text,
        right_text,
        disequalities,
        index_sort: shape.index_sort.to_string(),
        row_position: shape.row_position,
    })
}

fn collect_printed_disequalities(
    printer: &AlethePrinter<'_>,
    id: ProofId,
    literals: &[String],
    equalities: &[(TermId, usize, TermId, TermId)],
) -> Option<DisequalityMap> {
    let mut disequalities = HashMap::default();
    for &(_, position, lhs, rhs) in equalities {
        let (lhs, rhs) = (printer.format_term(lhs), printer.format_term(rhs));
        if literals[position] != format!("(= {lhs} {rhs})") {
            return None;
        }
        let key = if lhs <= rhs {
            (lhs.clone(), rhs.clone())
        } else {
            (rhs.clone(), lhs.clone())
        };
        disequalities.insert(key, (format!("{id}.a{position}"), lhs, rhs));
    }
    Some(disequalities)
}

fn write_swap_segments(
    output: &mut String,
    id: ProofId,
    printed: &PrintedPermutation,
    swaps: &[usize],
) -> Option<Vec<Segment>> {
    let mut current = printed.left.clone();
    let mut segments = Vec::new();
    for (nth, &at) in swaps.iter().enumerate() {
        let rest = store_chain_text(&printed.base, &current[at + 2..]);
        let outer = current[at].clone();
        let inner = current[at + 1].clone();
        let key = unordered_printed_pair(&outer.0, &inner.0);
        let (premise, diseq_lhs, diseq_rhs) = printed.disequalities.get(&key)?.clone();
        let tag = format!("{id}.k{nth}");
        let (mut before, mut after) = write_store_transposition(
            output,
            &tag,
            &rest,
            &outer,
            &inner,
            &printed.index_sort,
            &premise,
            (&diseq_lhs, &diseq_rhs),
            id,
        )?;
        let mut lifted = tag.clone();
        for depth in (0..at).rev() {
            let (index, value) = &current[depth];
            let next_before = format!("(store {before} {index} {value})");
            let next_after = format!("(store {after} {index} {value})");
            let step = format!("{tag}.l{depth}");
            output.push_str(&format!(
                "(step {step} (cl (= {next_before} {next_after})) \
                 :rule cong :premises ({lifted}))\n"
            ));
            lifted = step;
            before = next_before;
            after = next_after;
        }
        segments.push((lifted, before, after));
        current.swap(at, at + 1);
    }
    (current == printed.right).then_some(segments)
}

fn compose_segments(
    output: &mut String,
    id: ProofId,
    printed: &PrintedPermutation,
    segments: &[Segment],
) -> Option<String> {
    let mut chain_step = segments.first()?.0.clone();
    let mut chain_end = segments[0].2.clone();
    for (nth, (step, _, after)) in segments.iter().enumerate().skip(1) {
        let composed = format!("{id}.tr{nth}");
        output.push_str(&format!(
            "(step {composed} (cl (= {} {after})) \
             :rule trans :premises ({chain_step} {step}))\n",
            printed.left_text
        ));
        chain_step = composed;
        chain_end = after.clone();
    }
    (chain_end == printed.right_text && segments[0].1 == printed.left_text).then_some(chain_step)
}

fn write_clause_discharge(
    output: &mut String,
    printer: &AlethePrinter<'_>,
    id: ProofId,
    clause: &[TermId],
    printed: &PrintedPermutation,
    chain_step: &str,
) -> Option<()> {
    output.push_str(&format!(
        "(step {id}.bot (cl) :rule resolution :premises ({id}.a{} {chain_step}))\n",
        printed.row_position
    ));
    let doubled: Vec<String> = printed
        .literals
        .iter()
        .map(|literal| format!("(not (not {literal}))"))
        .collect();
    let discharge: Vec<String> = (0..printed.literals.len())
        .map(|position| format!("{id}.a{position}"))
        .collect();
    output.push_str(&format!(
        "(step {id}.sp0 (cl {} false) :rule subproof :discharge ({}))\n\
         (step {id}.sp (cl {}) :rule resolution :premises ({id}.sp0 {id}.nf))\n",
        doubled.join(" "),
        discharge.join(" "),
        doubled.join(" ")
    ));
    write_double_negation_steps(output, id, &printed.literals, &doubled);
    let conclusion = resolve_double_negations(output, id, &printed.literals, &doubled);
    if conclusion != id.to_string()
        || printer.format_clause(clause) != format!("(cl {})", printed.literals.join(" "))
    {
        return None;
    }
    Some(())
}

fn write_double_negation_steps(
    output: &mut String,
    id: ProofId,
    literals: &[String],
    doubled: &[String],
) {
    for (position, literal) in literals.iter().enumerate() {
        output.push_str(&format!(
            "(step {id}.d{position} (cl (not {}) {literal}) :rule not_not)\n",
            doubled[position]
        ));
    }
}

fn resolve_double_negations(
    output: &mut String,
    id: ProofId,
    literals: &[String],
    doubled: &[String],
) -> String {
    let mut previous = format!("{id}.sp");
    for position in 0..literals.len() {
        let mut resolvent: Vec<&str> = doubled[position + 1..].iter().map(String::as_str).collect();
        resolvent.extend(literals[..=position].iter().map(String::as_str));
        let step = if position + 1 == literals.len() {
            id.to_string()
        } else {
            format!("{id}.c{position}")
        };
        output.push_str(&format!(
            "(step {step} (cl {}) :rule resolution :premises ({previous} {id}.d{position}))\n",
            resolvent.join(" ")
        ));
        previous = step;
    }
    previous
}

fn unordered_printed_pair(left: &str, right: &str) -> (String, String) {
    if left <= right {
        (left.to_string(), right.to_string())
    } else {
        (right.to_string(), left.to_string())
    }
}

fn store_chain_text(base: &str, entries: &[PrintedEntry]) -> String {
    let mut text = base.to_string();
    for (index, value) in entries.iter().rev() {
        text = format!("(store {text} {index} {value})");
    }
    text
}

fn adjacent_transposition_schedule(
    left: &[PrintedEntry],
    right: &[PrintedEntry],
) -> Option<Vec<usize>> {
    if left.len() != right.len() {
        return None;
    }
    let mut current = left.to_vec();
    let mut swaps = Vec::new();
    for (target, wanted) in right.iter().enumerate() {
        let found = (target..current.len()).find(|&at| &current[at] == wanted)?;
        for at in (target..found).rev() {
            swaps.push(at);
            current.swap(at, at + 1);
        }
    }
    (current == right).then_some(swaps)
}
