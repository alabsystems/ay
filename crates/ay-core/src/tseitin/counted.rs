// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Caller-metered Tseitin construction (Tseitin, 1968), not a solver decision.
//!
//! Logical units price source visits, payload bytes, edges, emitted literals,
//! and geometric copies; they are not a CPU-instruction bound. Native stores
//! are priced in full for dense indexes. Theory atoms remain obligations.
//! Binary distinct uses an explicit distinct_elim/equiv/resolution derivation,
//! never an xor annotation or a missing (root-assumption) proof annotation.
//! Native nested sorts retain the existing CountedTermBuilder depth-256 copy
//! envelope; CNF numbering retains the signed-i32 SAT literal representation.
//! Neither limit is a new query-size, effort, or wall-clock allowance.

use crate::original_query::{CountedAdmission, CountedAdmissionError};
use crate::proof::AletheRule;
use crate::term::{
    Constant, CountedBuiltin, CountedTermBuilder, CountedTermError, Symbol, TermData, TermId,
    TermStore,
};
use crate::Sort;

mod api;
mod bridge;
mod encode;
mod materialize;
mod memory;
#[cfg(test)]
mod tests;
mod typing;
mod walk;

/// Version of the encoder's deterministic logical-work accounting.
///
/// Units price source visits, payload bytes and edges, emitted literals,
/// lookups, and geometric allocation/copy work. They are not CPU instructions
/// or a wall-time bound. Synthetic terms additionally use the counted term
/// builder's documented units, all debited from the same original owner.
pub const COUNTED_CNF_WORK_VERSION: u32 = 1;

/// Encoding or lookup refusal; none of these variants is a solver verdict.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error {
    /// The retained original resource owner has refused further work.
    #[error(transparent)]
    Stopped(#[from] CountedAdmissionError),
    /// The source or its native representation is outside the supported subset.
    #[error("unsupported counted CNF source representation")]
    Unsupported,
    /// A source signature, local identity, or requested literal is invalid.
    #[error("invalid counted CNF source identity or signature")]
    Invalid,
}
type Result<T> = std::result::Result<T, Error>;

impl From<CountedTermError> for Error {
    fn from(value: CountedTermError) -> Self {
        match value {
            CountedTermError::Stopped(error) => Self::Stopped(error),
            CountedTermError::Unsupported => Self::Unsupported,
            CountedTermError::InvalidInput | CountedTermError::ReadOnlySnapshot => Self::Invalid,
        }
    }
}

/// Exact source literal, before any CNF Not-alias normalization.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceLit {
    /// Exact Boolean identity in the encoder's retained term store.
    pub term: TermId,
    /// True denotes the term itself; false denotes a raw Not of that term.
    /// Nested negations are retained, not collapsed into a signed SAT alias.
    pub positive: bool,
}
impl SourceLit {
    fn positive(term: TermId) -> Self {
        Self {
            term,
            positive: true,
        }
    }
    fn negated(self) -> Self {
        Self {
            positive: !self.positive,
            ..self
        }
    }
}

/// One planned native proof inference, requiring independent checker replay.
///
/// Premises are backward indexes into the same ledger. Resolution pivots are
/// explicit original/synthetic term identities, not a CNF hash or a guess.
#[derive(Debug)]
pub struct Step {
    rule: AletheRule,
    source: TermId,
    clause: Vec<SourceLit>,
    premises: Option<[usize; 2]>,
    pivot: Option<TermId>,
}
/// The source of a CNF row, distinct from successful proof-checker admission.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Justification {
    /// Activation of an input root. A consumer must authenticate it against
    /// the actual original assertions; it is not a premiseless theorem.
    Root(TermId),
    /// Index into the exact proof-step ledger. Replay that inference and all
    /// its referenced premises before treating this row as checked evidence.
    Step(usize),
}
/// Immutable Boolean CNF clause together with its source justification.
#[derive(Debug)]
pub struct Row {
    literals: Vec<i32>,
    justification: Justification,
}
/// Source-preserving terms used by a binary distinct-elimination proof chain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DistinctBridge {
    /// Original binary `(distinct a b)` term, with unchanged operand order.
    pub source: TermId,
    /// Raw typed equality `(= a b)`; non-Boolean operands remain a theory atom.
    pub equality: TermId,
    /// Exact raw negation `(not (= a b))` used in proof clauses.
    pub negation: TermId,
    /// Raw equivalence of `source` and `negation`, derived by distinct_elim.
    pub equivalence: TermId,
}

/// Immutable, caller-owned CNF and proof plan tied to one retained term store.
///
/// No conversion to the legacy premiseless-only ledger is provided: doing so
/// would erase the distinct bridge's authority. A proof consumer must replay
/// `steps`, preserve exact source literals, and honor `term_literals` aliases.
/// SAT of these clauses alone does NOT discharge `theory_atoms`.
pub struct CountedCnf<'terms> {
    terms: &'terms TermStore,
    data: Data,
    prepared: materialize::Prepared,
    owner: CountedAdmission,
}

impl<'terms> CountedCnf<'terms> {
    /// Encode fully typed roots without solving or discharging theory atoms.
    /// The mutable phase adds only raw typed synthetic proof terms. Failure
    /// may retain those additions but never changes existing source entries.
    /// All caller-owned output disposal remains the caller's responsibility;
    /// `finish` offers a terminal fence after destroying this encoder's output.
    pub fn encode(
        terms: &'terms mut TermStore,
        roots: &[TermId],
        owner: &CountedAdmission,
    ) -> Result<Self> {
        owner.admit(1, 0)?;
        let outcome = prepare(terms, roots, owner);
        // Both successful scratch and every failed partial ledger have been
        // destroyed before this original-owner publication/refusal fence.
        owner.check()?;
        let (data, prepared) = outcome?;
        Ok(Self {
            terms,
            data,
            prepared,
            owner: owner.clone(),
        })
    }

    /// Poll the retained original resource owner without a new allowance.
    /// This checks resource admission, not the formula or the proof ledger.
    pub fn check(&self) -> Result<()> {
        self.owner.check().map_err(Error::from)
    }

    /// Destroy the owned CNF/maps and then poll the original resource owner.
    /// The borrowed term store and any data copied by a consumer remain that
    /// caller's responsibility; this method does not validate a solver result.
    pub fn finish(self) -> Result<()> {
        let owner = self.owner.clone();
        drop(self);
        owner.check()?;
        Ok(())
    }
}

struct Data {
    rows: Vec<Row>,
    steps: Vec<Step>,
    term_literals: Vec<Option<i32>>,
    theory_atoms: Vec<TermId>,
    bridges: Vec<DistinctBridge>,
    roots: Vec<TermId>,
    num_vars: u32,
}

struct Encoder<'terms> {
    terms: &'terms TermStore,
    data: Data,
    owner: CountedAdmission,
}

fn prepare(
    terms: &mut TermStore,
    roots: &[TermId],
    owner: &CountedAdmission,
) -> Result<(Data, materialize::Prepared)> {
    let original = walk::read(terms, roots, owner)?;
    let bridges = bridge::build(terms, &original, owner)?;
    let mut encoder = Encoder {
        terms,
        data: Data {
            term_literals: memory::filled(terms.len(), None, owner)?,
            rows: Vec::new(),
            steps: Vec::new(),
            theory_atoms: Vec::new(),
            roots: memory::copy(roots, owner)?,
            bridges,
            num_vars: 0,
        },
        owner: owner.clone(),
    };
    encode::run(&mut encoder, &original)?;
    drop(original);
    let Encoder { data, .. } = encoder;
    let prepared = materialize::prepare(terms, &data, owner)?;
    owner.check()?;
    Ok((data, prepared))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    Value,
    Atom,
    Variable,
    Constant(bool),
    Not,
    And,
    Or,
    Implies,
    Xor,
    Eq,
    Ite,
    Distinct,
}

struct Source {
    order: Vec<TermId>,
    kinds: Vec<Kind>,
}
