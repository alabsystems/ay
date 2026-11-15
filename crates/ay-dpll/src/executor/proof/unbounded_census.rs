// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #unbounded-population. What was on the OTHER SIDE of a bound when one of
//! the two "unbounded" decline mechanisms fired.
//!
//! `authored-source-root-unbounded` and `authored-surface-override-plan-
//! unbounded` together are the third-largest evidence class, and both say the
//! same one word: a plan or a rendering exceeded a bound. The sibling class
//! (`assume-family-trust-closure`) was diagnosed by taking a count AT the
//! decline site, and the count refuted the campaign's thesis for it: the budget
//! everyone blamed ran out during input load with nothing behind it, and
//! lifting it produced a bigger hole rather than evidence. So before either of
//! these bounds is touched, the same question is asked here at the site:
//! WHICH bound, on WHAT size, and what would the work be if the bound were not
//! there.
//!
//! Write-only. Nothing reads these numbers to decide a verdict, mint a
//! certificate, or authorize an export; the decline that carries them is
//! recorded exactly as it was before.

mod parsed_shape;
mod source_root;

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{TermId, TermStore};

use crate::executor::proof_repair::proof_trust_surgery_surface_audit::SurfaceSourceRefusal;
use crate::executor::proof_trust_surgery_provenance::CanonicalWorkRefusal;

pub(in crate::executor) use parsed_shape::parsed_root_shape;

/// The census the CLI discloses beside one of the two "unbounded" declines.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnboundedCensus {
    /// `authored-source-root-unbounded`: a PARSED root refused the per-root
    /// surface bound at the assembly gate.
    SourceRoot(SourceRootCensus),
    /// `authored-surface-override-plan-unbounded`: the override plan declined
    /// on one of its six exits.
    OverridePlan(OverridePlanCensus),
}

/// The true syntactic shape of one parsed root, measured WITHOUT any bound.
///
/// The source estimator stops at the first bound it trips, so the number it
/// leaves behind is where the bound is, not how big the root is. This walk
/// finishes. It is linear in the parsed AST, which is already in memory, so
/// the only cap is a saturating counter.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ParsedRootShape {
    /// AST nodes: terms, sorts, and annotation s-expressions, counted the way
    /// the estimator counts them.
    pub nodes: u64,
    /// Deepest node.
    pub depth: u32,
    /// The estimator's own byte measure summed over the whole tree.
    pub bytes: u64,
    /// `let` binding count — every one is a shared subterm the canonical DAG
    /// stores once and the syntactic tree spells once too.
    pub let_bindings: u32,
    /// Deepest `let` nesting on any path: a let CHAIN, which is the shape that
    /// makes a per-occurrence expansion exponential.
    pub let_depth: u32,
    /// Quantifier binders (`forall`/`exists`/`lambda`).
    pub binders: u32,
    /// Constructors the estimator does not price.
    pub unpriced: u32,
}

/// What the parsed roots looked like when the per-root bound refused one.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct SourceRootCensus {
    /// Parsed roots on the stack.
    pub roots: u32,
    /// Of those, refused by the build pass's traversal bound
    /// (`SurfaceWorkModel::Traversal`).
    pub refused_roots: u32,
    /// Which bound the FIRST refused root tripped, in stack order — the same
    /// order the decline's `.any()` inspects.
    pub refusal: Option<SurfaceSourceRefusal>,
    /// The first refused root, measured without the bound.
    pub first_refused: ParsedRootShape,
    /// The largest refused root by node count, measured without the bound.
    pub largest_refused: ParsedRootShape,
    /// The CANONICAL term the first refused root elaborated to, as a DAG and
    /// as its per-occurrence expansion. The parsed tree is what the author
    /// wrote; this is what AY holds. If `unique_nodes` is far below the parsed
    /// node count, sharing is the lever; if not, the root is simply large.
    ///
    /// Read from the pre-split authored stack named by
    /// [`Self::first_canonical_source`], NOT from `ctx.assertions` — see
    /// `Executor::authored_canonical_roots`. All-zero whenever that source is
    /// `unavailable`, which is not a measurement of a 0-node root.
    pub first_canonical: CanonicalRootShape,
    /// What the canonical root IS at its top: `false`, `true`, another
    /// constant, a variable, an application, `not`, `ite`, or a binder. A
    /// 170K-node authored assertion that elaborates to `false` was refuted by
    /// the elaborator, not by any lane a proof pass could render.
    ///
    /// `unavailable` when no pre-split stack could be positionally matched to
    /// the parsed one.
    pub first_canonical_kind: &'static str,
    /// WHICH pre-split stack [`Self::first_canonical`] came from: `epoch`,
    /// `provenance`, or `unavailable`.
    ///
    /// Recorded because the first version of this census silently read the
    /// SOLVE-TIME window and reported its first conjunct as the root. A number
    /// whose provenance is not on the line cannot be audited, and this one had
    /// to be withdrawn once already.
    pub first_canonical_source: &'static str,
    /// Roots on the pre-split authored stack actually used, `0` when none was.
    pub authored_roots: u32,
    /// Formulas in the SOLVE-TIME window (`ctx.assertions`) at the decline.
    /// Greater than `roots` exactly when an in-place pass — `FlattenAnd` above
    /// all — split authored conjunctions apart, which is the discrepancy that
    /// made reading that stack positionally unsound.
    pub solve_window_roots: u32,
    /// Sum of the traversal work of the roots that WERE bounded — the
    /// envelope the rest of the stack would have cost anyway.
    pub bounded_roots_work: u64,
}

/// Which of `prepare_surface_overrides`'s exits declined.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OverridePlanExit {
    /// `MAX_OVERRIDE_SOURCE_SCAN` or `MAX_OVERRIDE_PAIRS` during pair
    /// collection.
    ScanCeiling,
    /// More pair specs than `MAX_OVERRIDE_PAIRS` after retention.
    PairCeiling,
    /// `surface_override_roots_have_bounded_work` refused the canonical roots.
    CanonicalRootsUnbounded,
    /// The shared source-work envelope refused the `InputSyntaxOverridePairs`
    /// charge.
    EnvelopeRefused,
    /// A per-pair collector refused (parsed surface or canonical work).
    CollectorRefused,
    /// The collected override map exceeded its count or byte bound.
    OverrideMapUnbounded,
}

impl OverridePlanExit {
    /// The fixed name this exit carries on the disclosure line.
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::ScanCeiling => "scan-ceiling",
            Self::PairCeiling => "pair-ceiling",
            Self::CanonicalRootsUnbounded => "canonical-roots-unbounded",
            Self::EnvelopeRefused => "envelope-refused",
            Self::CollectorRefused => "collector-refused",
            Self::OverrideMapUnbounded => "override-map-unbounded",
        }
    }
}

/// The true shape of one canonical root, measured as a DAG and as the tree the
/// per-occurrence walk would expand it to.
///
/// `canonical_term_work` charges a shared child at every occurrence because
/// the recursive consumers it guards copy bytes at every occurrence. That is
/// correct for what those consumers do and it is exactly the accounting that
/// turns a `let` chain of stores into an exponential. Both numbers are kept so
/// a reader can see whether the root is BIG or merely SHARED — the remedies
/// are opposite (a bigger budget cannot fix the second; a DAG-aware renderer
/// can).
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct CanonicalRootShape {
    /// Distinct term ids reachable from the root.
    pub unique_nodes: u64,
    /// Nodes the per-occurrence walk would visit, saturating.
    pub expanded_nodes: u64,
    /// Longest root-to-leaf path.
    pub depth: u32,
    /// Binders (`forall`/`exists`) and `let`s reachable from the root — the
    /// shapes `canonical_term_work` refuses at any size.
    pub binders: u32,
}

/// What the override plan was looking at when it declined.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct OverridePlanCensus {
    /// Which of the six exits declined, `None` when the plan succeeded.
    pub exit: Option<OverridePlanExit>,
    /// Problem assertions the plan scanned.
    pub problem_assertions: u32,
    /// Original problem assertions the plan scanned.
    pub original_problem_assertions: u32,
    /// Parsed roots available to pair against.
    pub parsed_assertions: u32,
    /// Whether proof source provenance was installed for this query.
    pub has_provenance: bool,
    /// Source-scan work consumed while collecting pairs.
    pub source_scan_work: u64,
    /// Pair specs surviving retention.
    pub pair_specs: u32,
    /// Pair roots `surface_override_collection_work` refused because a binder
    /// or `let` lies below the unwrapped root — a SHAPE veto, not a size.
    pub canonical_roots_refused_shape: u32,
    /// Pair roots refused on visits, depth, or bytes — a SIZE refusal.
    pub canonical_roots_refused_size: u32,
    /// Pair roots refused on an unpriceable symbol.
    pub canonical_roots_refused_symbol: u32,
    /// The first canonical refusal, in pair order.
    pub canonical_first_refusal: Option<CanonicalWorkRefusal>,
    /// Sum of the priced roots' work, saturating.
    pub canonical_work: u64,
    /// The pair root with the largest expanded size, measured without a bound.
    pub largest_canonical: CanonicalRootShape,
    /// Envelope remaining before the `InputSyntaxOverridePairs` spend.
    pub envelope_remaining: u64,
    /// The single-pass charge the spend wanted, `None` when a pair's parsed
    /// root was itself unbounded.
    pub envelope_charge: Option<u64>,
    /// Index of the pair whose collector refused, when one did.
    pub collector_refused_pair: Option<u32>,
    /// Overrides collected before the map bound refused.
    pub overrides: u32,
    /// Bytes of override spellings collected before that bound refused.
    pub override_bytes: u64,
}

/// A fixed-vocabulary name for a term's top constructor, for the census line.
#[must_use]
pub(in crate::executor) fn term_kind(terms: &TermStore, term: TermId) -> &'static str {
    use ay_core::Constant;
    match terms.get(term) {
        TermData::Const(Constant::Bool(false)) => "false",
        TermData::Const(Constant::Bool(true)) => "true",
        TermData::Const(_) => "const",
        TermData::Var(..) => "var",
        TermData::App(..) => "app",
        TermData::Not(_) => "not",
        TermData::Ite(..) => "ite",
        TermData::Let(..) => "let",
        TermData::Forall(..) | TermData::Exists(..) => "binder",
        _ => "other",
    }
}

/// Bucket a canonical-work refusal the way the census reports it.
#[must_use]
pub(in crate::executor) const fn canonical_refusal_is_shape(refusal: CanonicalWorkRefusal) -> bool {
    matches!(refusal, CanonicalWorkRefusal::Binder)
}

/// Bucket a canonical-work refusal the way the census reports it.
#[must_use]
pub(in crate::executor) const fn canonical_refusal_is_symbol(
    refusal: CanonicalWorkRefusal,
) -> bool {
    matches!(refusal, CanonicalWorkRefusal::Symbol)
}

/// The root `surface_override_collection_work` actually prices, and the
/// traversal multiplicity it charges — the collector unwraps one `not` shell
/// over a `forall` before descending, so the bound and this census do too.
#[must_use]
pub(in crate::executor) fn override_collection_root(
    terms: &TermStore,
    canonical: TermId,
) -> (TermId, usize) {
    match terms.get(canonical) {
        TermData::Forall(bindings, body, _) | TermData::Exists(bindings, body, _) => {
            (*body, bindings.len().saturating_add(2))
        }
        TermData::Not(inner) => match terms.get(*inner) {
            TermData::Forall(bindings, body, _) => (*body, bindings.len().saturating_add(3)),
            _ => (canonical, 2),
        },
        _ => (canonical, 2),
    }
}

/// Shared memo for [`canonical_root_shape`] across the roots of one plan, so
/// a DAG shared by thousands of roots is priced once, not once per root.
#[derive(Default)]
pub(in crate::executor) struct CanonicalShapeMemo {
    memo: HashMap<TermId, (u64, u32, u32)>,
}

impl CanonicalShapeMemo {
    pub(in crate::executor) fn shape(
        &mut self,
        terms: &TermStore,
        root: TermId,
    ) -> CanonicalRootShape {
        let mut stack: Vec<(TermId, bool)> = vec![(root, false)];
        while let Some((term, children_done)) = stack.pop() {
            if self.memo.contains_key(&term) {
                continue;
            }
            let is_binder = matches!(
                terms.get(term),
                TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..)
            );
            if !children_done {
                stack.push((term, true));
                for child in terms.children(term) {
                    if !self.memo.contains_key(&child) {
                        stack.push((child, false));
                    }
                }
                continue;
            }
            let mut expanded = 1u64;
            let mut height = 0u32;
            let mut binders = u32::from(is_binder);
            for child in terms.children(term) {
                let (e, h, b) = self.memo.get(&child).copied().unwrap_or((1, 0, 0));
                expanded = expanded.saturating_add(e);
                height = height.max(h.saturating_add(1));
                binders = binders.saturating_add(b);
            }
            self.memo.insert(term, (expanded, height, binders));
        }
        let (expanded, height, binders) = self.memo.get(&root).copied().unwrap_or((1, 0, 0));
        CanonicalRootShape {
            unique_nodes: reachable_unique_nodes(terms, root),
            expanded_nodes: expanded,
            depth: height,
            binders,
        }
    }
}

/// Distinct term ids reachable from `root` — THIS root's DAG, not the memo's
/// accumulated view across every root of the plan. Linear in that DAG.
fn reachable_unique_nodes(terms: &TermStore, root: TermId) -> u64 {
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        stack.extend(terms.children(term));
    }
    seen.len() as u64
}

/// Price every pair root the way the plan's bound does and record what it saw.
pub(in crate::executor) fn census_canonical_roots(
    terms: &TermStore,
    census: &mut OverridePlanCensus,
    roots: impl IntoIterator<Item = TermId>,
) {
    use crate::executor::proof_trust_surgery_provenance::canonical_term_work_refusal;
    let mut memo = CanonicalShapeMemo::default();
    for canonical in roots {
        let (root, traversals) = override_collection_root(terms, canonical);
        match canonical_term_work_refusal(terms, root) {
            Ok(work) => {
                census.canonical_work = census
                    .canonical_work
                    .saturating_add((work.max(1) as u64).saturating_mul(traversals as u64));
            }
            Err(refusal) if census.canonical_first_refusal.is_none() => {
                census.canonical_first_refusal = Some(refusal);
                bucket_canonical_refusal(census, refusal);
            }
            Err(refusal) => bucket_canonical_refusal(census, refusal),
        }
        let shape = memo.shape(terms, root);
        if shape.expanded_nodes > census.largest_canonical.expanded_nodes {
            census.largest_canonical = shape;
        }
    }
}

fn bucket_canonical_refusal(census: &mut OverridePlanCensus, refusal: CanonicalWorkRefusal) {
    if canonical_refusal_is_shape(refusal) {
        census.canonical_roots_refused_shape =
            census.canonical_roots_refused_shape.saturating_add(1);
    } else if canonical_refusal_is_symbol(refusal) {
        census.canonical_roots_refused_symbol =
            census.canonical_roots_refused_symbol.saturating_add(1);
    } else {
        census.canonical_roots_refused_size = census.canonical_roots_refused_size.saturating_add(1);
    }
}
