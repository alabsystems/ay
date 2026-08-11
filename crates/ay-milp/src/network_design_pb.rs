// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact projection of small capacitated network blocks onto an integral master.
//!
//! This module recognizes a standard fixed-charge/network-design extended
//! formulation.  Apart from an optional continuous objective singleton, every
//! continuous column is a nonnegative arc `x_e` with an exact variable upper
//! bound
//!
//! ```text
//! 0 <= x_e <= sum_j u_ej z_ej,
//! z_ej bounded, nonnegative, and integral, u_ej > 0,
//! ```
//!
//! and occurs in one or two node-balance rows with incidence coefficient `+1`
//! or `-1`.  Integral columns may also occur as affine supplies in those
//! balances.  A one-sided lower (upper) balance is normalized to an equality by
//! an implicit unbounded outgoing (incoming) arc to an exterior node.  For each
//! small connected balance-row component and every nonempty node subset `S`
//! (including the full set), summing the balances gives
//!
//! ```text
//! -capacity(delta-(S)) <= rhs(S) - demand(S) <= capacity(delta+(S)).
//! ```
//!
//! Each finite side is emitted into a bounded-integral master.  A side crossed
//! by an implicit unbounded slack arc is deliberately omitted.  These are the
//! directed capacitated-transshipment (Hoffman) conditions, hence are necessary
//! and sufficient for a continuous arc completion.  The implicit endpoint of a
//! one-row arc is an unrestricted exterior node; including the full subset is
//! load-bearing because it retains the capacities of those one-ended arcs.
//!
//! Explicit cut enumeration is exponential.  A component larger than the
//! conservative enumeration cutoff is retained in the master with its flows
//! declared integral, but only after a complete TU certificate by construction:
//! pure directed node-arc incidence, integral fixed supplies/side coefficients,
//! integral affine capacities, zero flow costs, and finite exactly encodable
//! flow domains.  For each fixed integral design, the resulting capacitated
//! transshipment polytope is integral, so this restriction is existence- and
//! objective-preserving.  Anything outside that certificate declines.
//!
//! The output is still a [`Model`], not a bespoke PB object.  The existing
//! bounded-integer translator can therefore choose and validate its own exact
//! Boolean encoding.  All recognition and projection arithmetic reads the
//! authoritative rational side stores, and every derived rational that is not
//! exactly representable as `f64` is written back to the output side store.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::time::Instant;

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::model::{exact, Col, ColKind, Model, Row};

/// Enumeration is exponential only in the number of balance rows in one
/// connected block.  Larger integral transshipment blocks use the separately
/// certified retained-flow formulation instead of enumerating subsets.
const MAX_COMPONENT_NODES: usize = 16;

/// Independent aggregate cap across components.  Two inequalities are emitted
/// per nonempty subset.
const MAX_HOFFMAN_ROWS: usize = 131_072;

/// Separately cap the dominant enumeration work: subset/arc incidence scans.
const MAX_HOFFMAN_ARC_SCANS: usize = 20_000_000;

/// Prefer the compact TU-certified retained-flow formulation before explicit
/// subset enumeration becomes a poor input to the embedded PB route.  The
/// explicit projection can contain at most one capacity term per inspected
/// subset/arc pair, so this is a conservative proxy for its eventual term
/// count.  Failure to meet the stronger integral-TU certificate falls back to
/// the complete Hoffman projection; it never makes an otherwise supported
/// fractional network decline.
///
/// This also covers dense fixed-charge routing models with a modest number of
/// balance nodes.  Enumerating all subsets of a 15-node, 240-arc component
/// performs 7,864,080 scans and produces a multi-million-term master, while
/// retaining the same arcs needs only their original balance and VUB rows.
const COMPACT_MASTER_HOFFMAN_ARC_SCANS: usize = 250_000;

/// A medium compact network gets its singleton-node and full-component
/// Hoffman rows before lazy separation starts.  These are the cheapest standard
/// network-design cuts: unlike the unconstrained design master they already
/// price each node's incident capacity, while retaining only `O(|V||A|)`
/// construction work instead of exhaustive `O(2^|V||A|)` projection.
///
/// Tiny components stay fully lazy (their first exact min-cut is cheaper than a
/// seed pool), and large/dense components keep the same bounded decline posture.
const MIN_LAZY_SEED_COMPONENT_NODES: usize = 8;
const MAX_LAZY_SEED_COMPONENT_NODES: usize = 64;
const MAX_LAZY_SEED_ARC_SCANS: usize = 250_000;

/// Bound the exact census before any exponential work begins.
const MAX_EXACT_TERMS: usize = 1 << 20;

/// Independent preflight for radix state created by the retained-flow master.
const MAX_RETAINED_FLOW_BITS: usize = 1 << 20;

/// Exact completion uses Edmonds--Karp on each already-small balance
/// component.  This independent cap keeps a one-node component with an
/// enormous number of parallel exterior arcs from turning witness recovery
/// into unbounded work.
const MAX_COMPLETION_ARCS_PER_COMPONENT: usize = 4_096;

/// Aggregate residual-edge inspections across every component in one lift.
const MAX_COMPLETION_EDGE_SCANS: usize = 20_000_000;

/// The direct block-symmetry candidate producer is optional front-end work.
/// Keep it well below the PB admission envelope so many tiny network components
/// cannot consume the caller's solve slice before the generic fallback runs.
const MAX_BLOCK_SYMMETRY_COMPONENTS: usize = 256;
const MAX_BLOCK_SYMMETRY_CANDIDATES: usize = 64;
const MAX_BLOCK_SYMMETRY_COLUMNS_PER_BLOCK: usize = 8_192;
const MAX_BLOCK_SYMMETRY_WORK: usize = 100_000;

/// A typed, fail-closed reason that this exact route does not own a model.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(crate) enum NetworkDesignDecline {
    #[error("network projection deadline reached")]
    Deadline,
    #[error("invalid model")]
    InvalidModel,
    #[error("network projection exact-term cap exceeded")]
    TooManyTerms,
    #[error("expected at most one continuous objective column, found {found}")]
    ObjectiveSingletonCount { found: usize },
    #[error("network projection found no continuous flow columns")]
    NoFlowColumns,
    #[error("continuous objective column {column} occurs in {occurrences} rows")]
    ObjectiveNotSingleton { column: usize, occurrences: usize },
    #[error("objective singleton column {column} is not defined by an exact equality")]
    ObjectiveDefinitionNotEquality { column: usize },
    #[error("objective singleton row {row} contains another continuous column")]
    ObjectiveDefinitionHasContinuousPeer { row: usize },
    #[error("integral master column {column} does not have two finite bounds")]
    UnboundedMasterColumn { column: usize },
    #[error("continuous arc column {column} is not declared [0,+inf)")]
    FlowDomain { column: usize },
    #[error("row {row} containing a continuous arc is neither a balance nor a VUB")]
    UnsupportedFlowRow { row: usize },
    #[error("balance row {row} has unsupported ranged bounds")]
    UnsupportedBalanceBounds { row: usize },
    #[error("balance row {row} has a non-incidence arc coefficient")]
    NonIncidenceCoefficient { row: usize },
    #[error("VUB row {row} is not exactly x <= u*z with u>0")]
    InvalidVub { row: usize },
    #[error("VUB controller column {column} is not bounded nonnegative integral")]
    InvalidControllerDomain { column: usize },
    #[error("arc column {column} has {count} VUB rows instead of one")]
    FlowVubCount { column: usize, count: usize },
    #[error("arc column {column} occurs in {count} balance rows instead of one or two")]
    FlowBalanceDegree { column: usize, count: usize },
    #[error("two-row arc column {column} does not have opposite incidence signs")]
    FlowIncidenceSigns { column: usize },
    #[error("network component has {nodes} balance rows; cap is {cap}")]
    ComponentTooLarge { nodes: usize, cap: usize },
    #[error("Hoffman projection would emit {rows} rows; cap is {cap}")]
    TooManyHoffmanRows { rows: usize, cap: usize },
    #[error("Hoffman projection would inspect {scans} subset/arc pairs; cap is {cap}")]
    TooManyHoffmanArcScans { scans: usize, cap: usize },
    #[error("derived exact coefficient cannot be represented by a finite nonzero f64 proxy")]
    CoefficientAdvice,
    #[error("derived exact row bound cannot be represented by a finite f64 proxy")]
    BoundAdvice,
    #[error("derived exact objective value cannot be represented by a finite f64 proxy")]
    ObjectiveAdvice,
    #[error("large network component has nonintegral supply data in row {row}")]
    NonIntegralRetainedSupply { row: usize },
    #[error("large network component has nonintegral capacity data for arc {column}")]
    NonIntegralRetainedCapacity { column: usize },
    #[error("large network component arc {column} has no exactly encodable finite domain")]
    RetainedFlowDomain { column: usize },
    #[error("retained-flow radix would use {bits} bits; cap is {cap}")]
    TooManyRetainedFlowBits { bits: usize, cap: usize },
}

/// A fail-closed reason that an integral projected point could not be lifted.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(crate) enum NetworkDesignCompletionError {
    #[error("network completion deadline reached")]
    Deadline,
    #[error("projected master point is not exactly feasible")]
    InvalidMasterPoint,
    #[error("original model does not match the projection")]
    SourceMismatch,
    #[error("projection contains an inconsistent network map")]
    InvalidProjection,
    #[error("arc column {column} has a negative fixed capacity")]
    NegativeCapacity { column: usize },
    #[error("network component has {arcs} arcs; completion cap is {cap}")]
    TooManyCompletionArcs { arcs: usize, cap: usize },
    #[error("exact completion residual-edge scan cap exceeded")]
    CompletionWorkLimit,
    #[error("projected point has no exact network-flow completion")]
    Infeasible,
    #[error("completed point failed exact original-model verification")]
    VerificationFailed,
}

/// Result of checking one integral design-master point against the eliminated
/// network blocks.
pub(crate) enum NetworkDesignSeparation {
    /// Every block has an exact flow completion.  The returned point is in the
    /// original model's column order and has passed the original exact checker.
    Feasible(Vec<BigRational>),
    /// The point violates this exact Hoffman row.  The row is not trusted on
    /// construction: [`NetworkDesignProjection::install_cut`] reconstructs it
    /// from the retained subset/direction license before mutating the master.
    Violated(NetworkDesignCut),
}

/// Opaque structural license for one lazily separated Hoffman inequality.
pub(crate) struct NetworkDesignCut {
    component: usize,
    selected_balances: Vec<usize>,
    direction: HoffmanDirection,
    terms: Vec<(usize, BigRational)>,
    rhs: BigRational,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum HoffmanDirection {
    Incoming,
    Outgoing,
}

/// One recognized connected balance-row block, in original-model indices.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProjectedNetworkComponent {
    pub(crate) balance_rows: Vec<usize>,
    pub(crate) flow_columns: Vec<usize>,
    /// `true` means the complete TU-certified network rows and integralized
    /// flow coordinates remain in the master instead of Hoffman elimination.
    pub(crate) retained_flows: bool,
}

/// Exact affine recovery of the removed continuous objective singleton from a
/// master point.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ObjectiveLift {
    original_column: usize,
    constant: BigRational,
    /// Master-model column indices.
    terms: Vec<(u32, BigRational)>,
}

impl ObjectiveLift {
    fn value_at(&self, master_values: &[BigRational]) -> Option<BigRational> {
        let mut value = self.constant.clone();
        for &(column, ref coefficient) in &self.terms {
            value += coefficient * master_values.get(column as usize)?;
        }
        Some(value)
    }
}

/// Exact network projection and the maps needed by a later PB adapter.
pub(crate) struct NetworkDesignProjection {
    pub(crate) master: Model,
    pub(crate) master_to_original: Vec<Col>,
    pub(crate) original_to_master: Vec<Option<Col>>,
    pub(crate) components: Vec<ProjectedNetworkComponent>,
    pub(crate) hoffman_rows: usize,
    objective_lift: Option<ObjectiveLift>,
    balances: Vec<Balance>,
    flows: Vec<Flow>,
}

/// Exact, index-normalized description of one recognized network block.
///
/// Original row/column identities are replaced by positions in the component's
/// ordered balance, flow, and master-column vectors. Equality therefore
/// licenses a concrete candidate bijection without relying on a model name.
/// The later PB automorphism oracle remains the authority for the complete
/// projected master, including global rows not represented here.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct NetworkBlockDescriptor {
    retained_flows: bool,
    columns: Vec<NetworkBlockColumnDescriptor>,
    balances: Vec<NetworkBlockBalanceDescriptor>,
    flows: Vec<NetworkBlockFlowDescriptor>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct NetworkBlockColumnDescriptor {
    kind: u8,
    lower: BigRational,
    upper: BigRational,
    objective: BigRational,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct NetworkBlockBalanceDescriptor {
    rhs: BigRational,
    exterior_slack: u8,
    discrete: Vec<(u32, BigRational)>,
    flows: Vec<(u32, i8)>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct NetworkBlockFlowDescriptor {
    capacities: Vec<(u32, BigRational)>,
    balances: Vec<(u32, i8)>,
}

/// Construction posture for the exact network representation.
///
/// `Eager` preserves the original bounded route: small components are
/// projected with every Hoffman row and large integral components retain their
/// TU flow formulation.  `Lazy` keeps only the integral design master and
/// separates Hoffman rows from exact min-cuts as PB candidates arrive.  The
/// latter avoids both exponential cut enumeration and radix-encoding the flow
/// variables.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ProjectionMode {
    Eager,
    Lazy,
}

impl NetworkDesignProjection {
    /// Derive a compact adjacent-swap generating set for repeated exact network
    /// blocks in the projected master.
    ///
    /// Each returned map is a zero-based master-column involution. Descriptor
    /// equality proves that the mapped columns have the same exact local
    /// network roles, domains, and objective coefficients. It intentionally
    /// does not claim that global master rows are invariant: the PB layer must
    /// independently translate and exactly verify every candidate against the
    /// complete constraint multiset and objective before adding a lex leader.
    ///
    /// Adjacent swaps generate the full permutation group for a family of
    /// interchangeable blocks while adding only `blocks - 1` lex leaders.
    /// Deadline or resource exhaustion discards the complete optional set so a
    /// caller can enter its generic fallback without trusting partial census.
    pub(crate) fn adjacent_block_swap_candidates(
        &self,
        deadline: Option<Instant>,
    ) -> Vec<BTreeMap<u32, u32>> {
        let Some((groups, mut work)) = self.described_block_groups(deadline) else {
            return Vec::new();
        };

        let mut candidates = Vec::new();
        for blocks in groups.values() {
            for adjacent in blocks.windows(2) {
                if candidates.len() >= MAX_BLOCK_SYMMETRY_CANDIDATES
                    || charge_block_symmetry_work(
                        &mut work,
                        adjacent[0].len().saturating_add(adjacent[1].len()),
                        deadline,
                    )
                    .is_none()
                {
                    return Vec::new();
                }
                match block_swap_permutation(&adjacent[0], &adjacent[1], deadline) {
                    Some(candidate) => candidates.push(candidate),
                    None if block_symmetry_expired(deadline) => return Vec::new(),
                    None => {}
                }
            }
        }
        if block_symmetry_expired(deadline) {
            Vec::new()
        } else {
            candidates
        }
    }

    /// Return complete ordered families of exact descriptor-equal network
    /// blocks in zero-based projected-master column space.
    ///
    /// This exposes the same atomic, resource-bounded census used to construct
    /// [`Self::adjacent_block_swap_candidates`]. A family is ordered first by
    /// projected component order and each block's columns are ordered by the
    /// descriptor's local coordinates. Descriptor equality covers exact local
    /// roles, domains, and objective coefficients only; a caller must still
    /// verify the proposed partition against every row and the complete
    /// objective of its translated PB instance.
    pub(crate) fn ordered_interchangeable_block_families(
        &self,
        deadline: Option<Instant>,
    ) -> Vec<Vec<Vec<u32>>> {
        let Some((groups, _)) = self.described_block_groups(deadline) else {
            return Vec::new();
        };
        if block_symmetry_expired(deadline) {
            return Vec::new();
        }
        groups
            .into_values()
            .filter(|blocks| blocks.len() >= 2)
            .collect()
    }

    /// Atomically describe every projected network component and group exact
    /// equals. The returned work counter lets the adjacent-swap consumer keep
    /// its historical candidate-construction budget unchanged.
    fn described_block_groups(
        &self,
        deadline: Option<Instant>,
    ) -> Option<(BTreeMap<NetworkBlockDescriptor, Vec<Vec<u32>>>, usize)> {
        if self.components.len() > MAX_BLOCK_SYMMETRY_COMPONENTS || block_symmetry_expired(deadline)
        {
            return None;
        }
        let mut work = 0usize;
        charge_block_symmetry_work(
            &mut work,
            self.balances.len().saturating_add(self.flows.len()),
            deadline,
        )?;

        // These source-index lookups are shared by every component. Rebuilding
        // them inside `describe_network_block` made many-tiny-component models
        // quadratic before the optional route could decline.
        let mut balance_by_original = BTreeMap::new();
        for (index, balance) in self.balances.iter().enumerate() {
            if index & 0x3f == 0 && block_symmetry_expired(deadline) {
                return None;
            }
            if balance_by_original
                .insert(balance.original_row, index)
                .is_some()
            {
                return None;
            }
        }
        let mut flow_by_original = BTreeMap::new();
        for (index, flow) in self.flows.iter().enumerate() {
            if index & 0x3f == 0 && block_symmetry_expired(deadline) {
                return None;
            }
            if flow_by_original
                .insert(flow.original_column, index)
                .is_some()
            {
                return None;
            }
        }

        let mut groups: BTreeMap<NetworkBlockDescriptor, Vec<Vec<u32>>> = BTreeMap::new();
        for (index, component) in self.components.iter().enumerate() {
            if index & 0x1f == 0 && block_symmetry_expired(deadline) {
                return None;
            }
            let (descriptor, columns) = self.describe_network_block(
                component,
                &balance_by_original,
                &flow_by_original,
                &mut work,
                deadline,
            )?;
            groups.entry(descriptor).or_default().push(columns);
            if block_symmetry_expired(deadline) {
                return None;
            }
        }

        (!block_symmetry_expired(deadline)).then_some((groups, work))
    }

    fn describe_network_block(
        &self,
        component: &ProjectedNetworkComponent,
        balance_by_original: &BTreeMap<usize, usize>,
        flow_by_original: &BTreeMap<usize, usize>,
        work: &mut usize,
        deadline: Option<Instant>,
    ) -> Option<(NetworkBlockDescriptor, Vec<u32>)> {
        charge_block_symmetry_work(
            work,
            component
                .balance_rows
                .len()
                .saturating_add(component.flow_columns.len()),
            deadline,
        )?;

        let balance_indices = component
            .balance_rows
            .iter()
            .enumerate()
            .map(|(index, row)| {
                if index & 0x3f == 0 && block_symmetry_expired(deadline) {
                    None
                } else {
                    balance_by_original.get(row).copied()
                }
            })
            .collect::<Option<Vec<_>>>()?;
        let component_flows = component
            .flow_columns
            .iter()
            .enumerate()
            .map(|(work_index, column)| {
                if work_index & 0x3f == 0 && block_symmetry_expired(deadline) {
                    None
                } else {
                    flow_by_original
                        .get(column)
                        .and_then(|&index| self.flows.get(index))
                }
            })
            .collect::<Option<Vec<_>>>()?;

        let mut original_columns = BTreeSet::new();
        for (index, &balance) in balance_indices.iter().enumerate() {
            if index & 0x1f == 0 && block_symmetry_expired(deadline) {
                return None;
            }
            charge_block_symmetry_work(work, self.balances.get(balance)?.discrete.len(), deadline)?;
            for (term_index, &(column, _)) in self.balances[balance].discrete.iter().enumerate() {
                if term_index & 0x3f == 0 && block_symmetry_expired(deadline) {
                    return None;
                }
                original_columns.insert(column);
                if original_columns.len() > MAX_BLOCK_SYMMETRY_COLUMNS_PER_BLOCK {
                    return None;
                }
            }
        }
        for (index, flow) in component_flows.iter().enumerate() {
            if index & 0x1f == 0 && block_symmetry_expired(deadline) {
                return None;
            }
            charge_block_symmetry_work(work, flow.vub.capacity_terms.len(), deadline)?;
            for (term_index, &(column, _)) in flow.vub.capacity_terms.iter().enumerate() {
                if term_index & 0x3f == 0 && block_symmetry_expired(deadline) {
                    return None;
                }
                original_columns.insert(column);
                if original_columns.len() > MAX_BLOCK_SYMMETRY_COLUMNS_PER_BLOCK {
                    return None;
                }
            }
        }
        if component.retained_flows {
            charge_block_symmetry_work(work, component.flow_columns.len(), deadline)?;
            for (index, &column) in component.flow_columns.iter().enumerate() {
                if index & 0x3f == 0 && block_symmetry_expired(deadline) {
                    return None;
                }
                original_columns.insert(column);
                if original_columns.len() > MAX_BLOCK_SYMMETRY_COLUMNS_PER_BLOCK {
                    return None;
                }
            }
        }
        if original_columns.is_empty() {
            return None;
        }
        let original_columns: Vec<usize> = original_columns.into_iter().collect();
        charge_block_symmetry_work(work, original_columns.len().saturating_mul(3), deadline)?;
        let local_column: BTreeMap<usize, u32> = original_columns
            .iter()
            .enumerate()
            .map(|(local, &original)| {
                if local & 0x3f == 0 && block_symmetry_expired(deadline) {
                    None
                } else {
                    Some((original, u32::try_from(local).ok()?))
                }
            })
            .collect::<Option<_>>()?;
        let master_columns: Vec<u32> = original_columns
            .iter()
            .enumerate()
            .map(|(index, &original)| {
                if index & 0x3f == 0 && block_symmetry_expired(deadline) {
                    None
                } else {
                    self.original_to_master
                        .get(original)?
                        .map(|column| column.0)
                }
            })
            .collect::<Option<_>>()?;

        let mut columns = Vec::with_capacity(master_columns.len());
        for (index, &column) in master_columns.iter().enumerate() {
            if index & 0x3f == 0 && block_symmetry_expired(deadline) {
                return None;
            }
            let column = Col(column);
            let kind = match self.master.col_kind(column) {
                ColKind::Binary => 0,
                ColKind::Integer => 1,
                ColKind::Continuous => return None,
            };
            let (lower, upper) = self.master.col_bounds(column);
            columns.push(NetworkBlockColumnDescriptor {
                kind,
                lower: exact(lower)?,
                upper: exact(upper)?,
                objective: self
                    .master
                    .obj_coeff_exact_at(column.0, self.master.obj_coeff(column)),
            });
        }

        let local_balance: BTreeMap<usize, u32> = balance_indices
            .iter()
            .enumerate()
            .map(|(local, &global)| {
                if local & 0x3f == 0 && block_symmetry_expired(deadline) {
                    None
                } else {
                    Some((global, u32::try_from(local).ok()?))
                }
            })
            .collect::<Option<_>>()?;
        let local_flow: BTreeMap<usize, u32> = component
            .flow_columns
            .iter()
            .enumerate()
            .map(|(local, &original)| {
                if local & 0x3f == 0 && block_symmetry_expired(deadline) {
                    None
                } else {
                    Some((original, u32::try_from(local).ok()?))
                }
            })
            .collect::<Option<_>>()?;

        let balances = balance_indices
            .iter()
            .map(|&index| {
                if block_symmetry_expired(deadline) {
                    return None;
                }
                let balance = self.balances.get(index)?;
                charge_block_symmetry_work(
                    work,
                    balance.discrete.len().saturating_add(balance.flows.len()),
                    deadline,
                )?;
                let mut discrete = balance
                    .discrete
                    .iter()
                    .enumerate()
                    .map(|(term_index, &(column, ref coefficient))| {
                        if term_index & 0x3f == 0 && block_symmetry_expired(deadline) {
                            None
                        } else {
                            Some((*local_column.get(&column)?, coefficient.clone()))
                        }
                    })
                    .collect::<Option<Vec<_>>>()?;
                discrete.sort();
                if block_symmetry_expired(deadline) {
                    return None;
                }
                let mut flows = balance
                    .flows
                    .iter()
                    .enumerate()
                    .map(|(term_index, &(column, sign))| {
                        if term_index & 0x3f == 0 && block_symmetry_expired(deadline) {
                            None
                        } else {
                            Some((*local_flow.get(&column)?, sign))
                        }
                    })
                    .collect::<Option<Vec<_>>>()?;
                flows.sort_unstable();
                if block_symmetry_expired(deadline) {
                    return None;
                }
                Some(NetworkBlockBalanceDescriptor {
                    rhs: balance.rhs.clone(),
                    exterior_slack: match balance.exterior_slack {
                        None => 0,
                        Some(ExteriorSlack::Incoming) => 1,
                        Some(ExteriorSlack::Outgoing) => 2,
                    },
                    discrete,
                    flows,
                })
            })
            .collect::<Option<Vec<_>>>()?;
        let flows = component_flows
            .iter()
            .map(|flow| {
                if block_symmetry_expired(deadline) {
                    return None;
                }
                charge_block_symmetry_work(
                    work,
                    flow.vub
                        .capacity_terms
                        .len()
                        .saturating_add(flow.balances.len()),
                    deadline,
                )?;
                let mut capacities = flow
                    .vub
                    .capacity_terms
                    .iter()
                    .enumerate()
                    .map(|(term_index, &(column, ref coefficient))| {
                        if term_index & 0x3f == 0 && block_symmetry_expired(deadline) {
                            None
                        } else {
                            Some((*local_column.get(&column)?, coefficient.clone()))
                        }
                    })
                    .collect::<Option<Vec<_>>>()?;
                capacities.sort();
                if block_symmetry_expired(deadline) {
                    return None;
                }
                let mut balances = flow
                    .balances
                    .iter()
                    .enumerate()
                    .map(|(term_index, &(balance, sign))| {
                        if term_index & 0x3f == 0 && block_symmetry_expired(deadline) {
                            None
                        } else {
                            Some((*local_balance.get(&balance)?, sign))
                        }
                    })
                    .collect::<Option<Vec<_>>>()?;
                balances.sort_unstable();
                if block_symmetry_expired(deadline) {
                    return None;
                }
                Some(NetworkBlockFlowDescriptor {
                    capacities,
                    balances,
                })
            })
            .collect::<Option<Vec<_>>>()?;

        Some((
            NetworkBlockDescriptor {
                retained_flows: component.retained_flows,
                columns,
                balances,
                flows,
            },
            master_columns,
        ))
    }

    /// Lift the integral master coordinates and the eliminated objective
    /// singleton.  Network-flow coordinates remain `None`; [`Self::complete_exact`]
    /// fills them with a checked exact rational transshipment.
    pub(crate) fn lift_partial(
        &self,
        master_values: &[BigRational],
    ) -> Option<Vec<Option<BigRational>>> {
        if master_values.len() != self.master.num_cols() {
            return None;
        }
        let mut original = vec![None; self.original_to_master.len()];
        for (master, &source) in self.master_to_original.iter().enumerate() {
            original[source.index()] = Some(master_values[master].clone());
        }
        if let Some(objective_lift) = &self.objective_lift {
            original[objective_lift.original_column] =
                Some(objective_lift.value_at(master_values)?);
        }
        Some(original)
    }

    /// Exactly complete a checked integral master point with all removed flow
    /// coordinates, then recheck the complete point against `original`.
    ///
    /// `original` must be the model used to build this projection.  Every
    /// component is solved as a rational capacitated transshipment problem;
    /// one-ended arcs meet at an exterior node whose required balance is
    /// derived from the constrained nodes.  No rounded LP solution is trusted.
    pub(crate) fn complete_exact(
        &self,
        original: &Model,
        master_values: &[BigRational],
        deadline: Option<Instant>,
    ) -> Result<Vec<BigRational>, NetworkDesignCompletionError> {
        if expired(deadline) {
            return Err(NetworkDesignCompletionError::Deadline);
        }
        if master_values.len() != self.master.num_cols() {
            return Err(NetworkDesignCompletionError::InvalidMasterPoint);
        }
        self.master
            .check_point(master_values)
            .map_err(|_| NetworkDesignCompletionError::InvalidMasterPoint)?;
        if original.num_cols() != self.original_to_master.len() {
            return Err(NetworkDesignCompletionError::SourceMismatch);
        }
        let partial = self
            .lift_partial(master_values)
            .ok_or(NetworkDesignCompletionError::InvalidProjection)?;
        let mut original_values: Vec<BigRational> = partial
            .into_iter()
            .map(|value| value.unwrap_or_else(BigRational::zero))
            .collect();

        let balance_by_original: BTreeMap<usize, usize> = self
            .balances
            .iter()
            .enumerate()
            .map(|(index, balance)| (balance.original_row, index))
            .collect();
        let flow_by_original: BTreeMap<usize, usize> = self
            .flows
            .iter()
            .enumerate()
            .map(|(index, flow)| (flow.original_column, index))
            .collect();
        let mut edge_scans = 0usize;

        for component in &self.components {
            if expired(deadline) {
                return Err(NetworkDesignCompletionError::Deadline);
            }
            if component.retained_flows {
                continue;
            }
            let implicit_arcs = component
                .balance_rows
                .iter()
                .filter(|row| {
                    balance_by_original
                        .get(row)
                        .is_some_and(|&index| self.balances[index].exterior_slack.is_some())
                })
                .count();
            let completion_arcs = component
                .flow_columns
                .len()
                .checked_add(implicit_arcs)
                .ok_or(NetworkDesignCompletionError::CompletionWorkLimit)?;
            if completion_arcs > MAX_COMPLETION_ARCS_PER_COMPONENT {
                return Err(NetworkDesignCompletionError::TooManyCompletionArcs {
                    arcs: completion_arcs,
                    cap: MAX_COMPLETION_ARCS_PER_COMPONENT,
                });
            }
            let component_balances: Vec<usize> = component
                .balance_rows
                .iter()
                .map(|row| {
                    balance_by_original
                        .get(row)
                        .copied()
                        .ok_or(NetworkDesignCompletionError::InvalidProjection)
                })
                .collect::<Result<_, _>>()?;
            let local_node: BTreeMap<usize, usize> = component_balances
                .iter()
                .enumerate()
                .map(|(local, &global)| (global, local))
                .collect();
            let exterior = component_balances.len();
            let mut required = vec![BigRational::zero(); exterior + 1];
            for (local, &balance_index) in component_balances.iter().enumerate() {
                let balance = &self.balances[balance_index];
                let mut value = balance.rhs.clone();
                for &(column, ref coefficient) in &balance.discrete {
                    let master_column = self
                        .original_to_master
                        .get(column)
                        .and_then(|column| *column)
                        .ok_or(NetworkDesignCompletionError::InvalidProjection)?;
                    value -= coefficient * &master_values[master_column.index()];
                }
                required[local] = value;
            }
            required[exterior] = -required[..exterior].iter().cloned().sum::<BigRational>();

            let mut arcs = Vec::with_capacity(completion_arcs);
            let mut finite_capacity_sum = BigRational::zero();
            for &original_column in &component.flow_columns {
                let flow_index = flow_by_original
                    .get(&original_column)
                    .copied()
                    .ok_or(NetworkDesignCompletionError::InvalidProjection)?;
                let flow = &self.flows[flow_index];
                let mut capacity = BigRational::zero();
                for &(controller, ref weight) in &flow.vub.capacity_terms {
                    let master_controller = self
                        .original_to_master
                        .get(controller)
                        .and_then(|column| *column)
                        .ok_or(NetworkDesignCompletionError::InvalidProjection)?;
                    capacity += weight * &master_values[master_controller.index()];
                }
                if capacity.is_negative() {
                    return Err(NetworkDesignCompletionError::NegativeCapacity {
                        column: original_column,
                    });
                }
                finite_capacity_sum += &capacity;
                let (from, to) = flow_endpoints(flow, &local_node, exterior)?;
                arcs.push(CompletionArc {
                    original_column: Some(original_column),
                    from,
                    to,
                    capacity,
                });
            }

            // Replace each semantically unbounded implicit slack by a bound
            // that is provably nonbinding for this fixed master point.  At a
            // node, `slack = net_flow - required` (or its negation), so no
            // feasible slack can exceed the total finite capacity plus that
            // node's absolute requirement.
            let slack_capacity =
                finite_capacity_sum + required.iter().map(BigRational::abs).sum::<BigRational>();
            for (local, &balance_index) in component_balances.iter().enumerate() {
                let endpoints = match self.balances[balance_index].exterior_slack {
                    Some(ExteriorSlack::Incoming) => Some((exterior, local)),
                    Some(ExteriorSlack::Outgoing) => Some((local, exterior)),
                    None => None,
                };
                if let Some((from, to)) = endpoints {
                    arcs.push(CompletionArc {
                        original_column: None,
                        from,
                        to,
                        capacity: slack_capacity.clone(),
                    });
                }
            }

            let values = exact_transshipment(required, &arcs, deadline, &mut edge_scans)?;
            for (arc, value) in arcs.iter().zip(values) {
                if let Some(original_column) = arc.original_column {
                    original_values[original_column] = value;
                }
            }
        }

        if expired(deadline) {
            return Err(NetworkDesignCompletionError::Deadline);
        }
        original
            .check_point(&original_values)
            .map_err(|_| NetworkDesignCompletionError::VerificationFailed)?;
        if self.master.objective_value_at(master_values)
            != original.objective_value_at(&original_values)
        {
            return Err(NetworkDesignCompletionError::VerificationFailed);
        }
        if expired(deadline) {
            return Err(NetworkDesignCompletionError::Deadline);
        }
        Ok(original_values)
    }

    /// Check a compact design-master point by exact max flow.  An infeasible
    /// flow block returns a violated Hoffman inequality licensed by the
    /// residual min-cut; a feasible point is lifted and checked exactly against
    /// the original model.
    pub(crate) fn separate_exact(
        &self,
        original: &Model,
        master_values: &[BigRational],
        deadline: Option<Instant>,
    ) -> Result<NetworkDesignSeparation, NetworkDesignCompletionError> {
        if expired(deadline) {
            return Err(NetworkDesignCompletionError::Deadline);
        }
        if master_values.len() != self.master.num_cols()
            || self
                .components
                .iter()
                .any(|component| component.retained_flows)
        {
            return Err(NetworkDesignCompletionError::InvalidMasterPoint);
        }
        self.master
            .check_point(master_values)
            .map_err(|_| NetworkDesignCompletionError::InvalidMasterPoint)?;
        if original.num_cols() != self.original_to_master.len() {
            return Err(NetworkDesignCompletionError::SourceMismatch);
        }
        let partial = self
            .lift_partial(master_values)
            .ok_or(NetworkDesignCompletionError::InvalidProjection)?;
        let mut original_values: Vec<BigRational> = partial
            .into_iter()
            .map(|value| value.unwrap_or_else(BigRational::zero))
            .collect();

        let balance_by_original: BTreeMap<usize, usize> = self
            .balances
            .iter()
            .enumerate()
            .map(|(index, balance)| (balance.original_row, index))
            .collect();
        let flow_by_original: BTreeMap<usize, usize> = self
            .flows
            .iter()
            .enumerate()
            .map(|(index, flow)| (flow.original_column, index))
            .collect();
        let mut edge_scans = 0usize;

        for (component_index, component) in self.components.iter().enumerate() {
            if expired(deadline) {
                return Err(NetworkDesignCompletionError::Deadline);
            }
            let implicit_arcs = component
                .balance_rows
                .iter()
                .filter(|row| {
                    balance_by_original
                        .get(row)
                        .is_some_and(|&index| self.balances[index].exterior_slack.is_some())
                })
                .count();
            let completion_arcs = component
                .flow_columns
                .len()
                .checked_add(implicit_arcs)
                .ok_or(NetworkDesignCompletionError::CompletionWorkLimit)?;
            if completion_arcs > MAX_COMPLETION_ARCS_PER_COMPONENT {
                return Err(NetworkDesignCompletionError::TooManyCompletionArcs {
                    arcs: completion_arcs,
                    cap: MAX_COMPLETION_ARCS_PER_COMPONENT,
                });
            }
            let component_balances: Vec<usize> = component
                .balance_rows
                .iter()
                .map(|row| {
                    balance_by_original
                        .get(row)
                        .copied()
                        .ok_or(NetworkDesignCompletionError::InvalidProjection)
                })
                .collect::<Result<_, _>>()?;
            let local_node: BTreeMap<usize, usize> = component_balances
                .iter()
                .enumerate()
                .map(|(local, &global)| (global, local))
                .collect();
            let exterior = component_balances.len();
            let mut required = vec![BigRational::zero(); exterior + 1];
            for (local, &balance_index) in component_balances.iter().enumerate() {
                let balance = &self.balances[balance_index];
                let mut value = balance.rhs.clone();
                for &(column, ref coefficient) in &balance.discrete {
                    let master_column = self
                        .original_to_master
                        .get(column)
                        .and_then(|column| *column)
                        .ok_or(NetworkDesignCompletionError::InvalidProjection)?;
                    value -= coefficient * &master_values[master_column.index()];
                }
                required[local] = value;
            }
            required[exterior] = -required[..exterior].iter().cloned().sum::<BigRational>();

            let mut arcs = Vec::with_capacity(completion_arcs);
            let mut finite_capacity_sum = BigRational::zero();
            for &original_column in &component.flow_columns {
                let flow_index = flow_by_original
                    .get(&original_column)
                    .copied()
                    .ok_or(NetworkDesignCompletionError::InvalidProjection)?;
                let flow = &self.flows[flow_index];
                let mut capacity = BigRational::zero();
                for &(controller, ref weight) in &flow.vub.capacity_terms {
                    let master_controller = self
                        .original_to_master
                        .get(controller)
                        .and_then(|column| *column)
                        .ok_or(NetworkDesignCompletionError::InvalidProjection)?;
                    capacity += weight * &master_values[master_controller.index()];
                }
                if capacity.is_negative() {
                    return Err(NetworkDesignCompletionError::NegativeCapacity {
                        column: original_column,
                    });
                }
                finite_capacity_sum += &capacity;
                let (from, to) = flow_endpoints(flow, &local_node, exterior)?;
                arcs.push(CompletionArc {
                    original_column: Some(original_column),
                    from,
                    to,
                    capacity,
                });
            }

            let slack_capacity =
                finite_capacity_sum + required.iter().map(BigRational::abs).sum::<BigRational>();
            for (local, &balance_index) in component_balances.iter().enumerate() {
                let endpoints = match self.balances[balance_index].exterior_slack {
                    Some(ExteriorSlack::Incoming) => Some((exterior, local)),
                    Some(ExteriorSlack::Outgoing) => Some((local, exterior)),
                    None => None,
                };
                if let Some((from, to)) = endpoints {
                    arcs.push(CompletionArc {
                        original_column: None,
                        from,
                        to,
                        capacity: slack_capacity.clone(),
                    });
                }
            }

            match exact_transshipment_with_cut(required, &arcs, deadline, &mut edge_scans)? {
                TransshipmentOutcome::Feasible(values) => {
                    for (arc, value) in arcs.iter().zip(values) {
                        if let Some(original_column) = arc.original_column {
                            original_values[original_column] = value;
                        }
                    }
                }
                TransshipmentOutcome::Infeasible { reachable } => {
                    if reachable.len() != exterior + 1 {
                        return Err(NetworkDesignCompletionError::InvalidProjection);
                    }
                    let (direction, selected_balances) = if !reachable[exterior] {
                        (
                            HoffmanDirection::Outgoing,
                            component_balances
                                .iter()
                                .enumerate()
                                .filter_map(|(local, &global)| reachable[local].then_some(global))
                                .collect::<Vec<_>>(),
                        )
                    } else {
                        (
                            HoffmanDirection::Incoming,
                            component_balances
                                .iter()
                                .enumerate()
                                .filter_map(|(local, &global)| {
                                    (!reachable[local]).then_some(global)
                                })
                                .collect::<Vec<_>>(),
                        )
                    };
                    if selected_balances.is_empty() {
                        return Err(NetworkDesignCompletionError::InvalidProjection);
                    }
                    let (terms, rhs) = build_hoffman_cut(
                        &self.balances,
                        &self.flows,
                        component,
                        &selected_balances,
                        direction,
                    )?;
                    let lhs =
                        evaluate_original_terms(&terms, &self.original_to_master, master_values)?;
                    if lhs >= rhs {
                        return Err(NetworkDesignCompletionError::InvalidProjection);
                    }
                    return Ok(NetworkDesignSeparation::Violated(NetworkDesignCut {
                        component: component_index,
                        selected_balances,
                        direction,
                        terms,
                        rhs,
                    }));
                }
            }
        }

        if expired(deadline) {
            return Err(NetworkDesignCompletionError::Deadline);
        }
        original
            .check_point(&original_values)
            .map_err(|_| NetworkDesignCompletionError::VerificationFailed)?;
        if self.master.objective_value_at(master_values)
            != original.objective_value_at(&original_values)
        {
            return Err(NetworkDesignCompletionError::VerificationFailed);
        }
        Ok(NetworkDesignSeparation::Feasible(original_values))
    }

    /// Reconstruct and install a previously separated Hoffman row.  Mutation
    /// happens only after the structural license and current violation have
    /// both been checked exactly.
    pub(crate) fn install_cut(
        &mut self,
        cut: NetworkDesignCut,
        violating_point: &[BigRational],
        deadline: Option<Instant>,
    ) -> Result<(), NetworkDesignCompletionError> {
        if expired(deadline) {
            return Err(NetworkDesignCompletionError::Deadline);
        }
        if violating_point.len() != self.master.num_cols() {
            return Err(NetworkDesignCompletionError::InvalidMasterPoint);
        }
        let component = self
            .components
            .get(cut.component)
            .ok_or(NetworkDesignCompletionError::InvalidProjection)?;
        let component_balances: BTreeSet<usize> = component
            .balance_rows
            .iter()
            .map(|row| {
                self.balances
                    .iter()
                    .position(|balance| balance.original_row == *row)
                    .ok_or(NetworkDesignCompletionError::InvalidProjection)
            })
            .collect::<Result<_, _>>()?;
        let selected: BTreeSet<usize> = cut.selected_balances.iter().copied().collect();
        if selected.len() != cut.selected_balances.len()
            || selected.is_empty()
            || !selected.is_subset(&component_balances)
        {
            return Err(NetworkDesignCompletionError::InvalidProjection);
        }
        let (terms, rhs) = build_hoffman_cut(
            &self.balances,
            &self.flows,
            component,
            &cut.selected_balances,
            cut.direction,
        )?;
        if terms != cut.terms || rhs != cut.rhs {
            return Err(NetworkDesignCompletionError::InvalidProjection);
        }
        let lhs = evaluate_original_terms(&terms, &self.original_to_master, violating_point)?;
        if lhs >= rhs {
            return Err(NetworkDesignCompletionError::InvalidMasterPoint);
        }
        let next_hoffman_rows = self
            .hoffman_rows
            .checked_add(1)
            .ok_or(NetworkDesignCompletionError::CompletionWorkLimit)?;
        add_exact_row(
            &mut self.master,
            &self.original_to_master,
            &terms,
            Some(&rhs),
            None,
        )
        .map_err(|_| NetworkDesignCompletionError::InvalidProjection)?;
        self.hoffman_rows = next_hoffman_rows;
        Ok(())
    }
}

#[derive(Debug, Clone)]
struct ExactRow {
    terms: Vec<(usize, BigRational)>,
    lb: Option<BigRational>,
    ub: Option<BigRational>,
}

#[derive(Debug, Clone)]
struct Balance {
    original_row: usize,
    rhs: BigRational,
    discrete: Vec<(usize, BigRational)>,
    flows: Vec<(usize, i8)>,
    exterior_slack: Option<ExteriorSlack>,
}

/// Direction of the implicit nonnegative, unbounded arc that converts a
/// one-sided balance to an equality.  Signs follow `inflow - outflow`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExteriorSlack {
    Incoming,
    Outgoing,
}

#[derive(Debug, Clone)]
struct Vub {
    original_row: usize,
    /// Exact positive affine capacity terms `(integral controller, weight)`.
    capacity_terms: Vec<(usize, BigRational)>,
}

#[derive(Debug, Clone)]
struct Flow {
    original_column: usize,
    vub: Vub,
    /// `(balance index, incidence sign)`.
    balances: Vec<(usize, i8)>,
}

#[derive(Debug, Clone)]
struct CompletionArc {
    /// `None` denotes an implicit one-sided-balance slack arc.
    original_column: Option<usize>,
    from: usize,
    to: usize,
    capacity: BigRational,
}

#[derive(Debug, Clone)]
struct ResidualEdge {
    to: usize,
    reverse: usize,
    capacity: BigRational,
}

enum TransshipmentOutcome {
    Feasible(Vec<BigRational>),
    /// Residual nodes reachable from the auxiliary source.  The vector covers
    /// only the transshipment nodes (including the component exterior), not the
    /// auxiliary source/sink themselves.
    Infeasible {
        reachable: Vec<bool>,
    },
}

fn evaluate_original_terms(
    terms: &[(usize, BigRational)],
    original_to_master: &[Option<Col>],
    master_values: &[BigRational],
) -> Result<BigRational, NetworkDesignCompletionError> {
    let mut value = BigRational::zero();
    for &(original, ref coefficient) in terms {
        let master = original_to_master
            .get(original)
            .and_then(|column| *column)
            .ok_or(NetworkDesignCompletionError::InvalidProjection)?;
        value += coefficient
            * master_values
                .get(master.index())
                .ok_or(NetworkDesignCompletionError::InvalidMasterPoint)?;
    }
    Ok(value)
}

/// Reconstruct one directed Hoffman side from its node subset.  The returned
/// row is always in canonical original-column order and has the form
/// `terms >= rhs`.
fn build_hoffman_cut(
    balances: &[Balance],
    flows: &[Flow],
    component: &ProjectedNetworkComponent,
    selected_balances: &[usize],
    direction: HoffmanDirection,
) -> Result<(Vec<(usize, BigRational)>, BigRational), NetworkDesignCompletionError> {
    let selected: BTreeSet<usize> = selected_balances.iter().copied().collect();
    if selected.is_empty() || selected.len() != selected_balances.len() {
        return Err(NetworkDesignCompletionError::InvalidProjection);
    }
    let component_balance_indices: BTreeSet<usize> = component
        .balance_rows
        .iter()
        .map(|row| {
            balances
                .iter()
                .position(|balance| balance.original_row == *row)
                .ok_or(NetworkDesignCompletionError::InvalidProjection)
        })
        .collect::<Result<_, _>>()?;
    if !selected.is_subset(&component_balance_indices) {
        return Err(NetworkDesignCompletionError::InvalidProjection);
    }

    let forbidden_slack = match direction {
        HoffmanDirection::Incoming => ExteriorSlack::Incoming,
        HoffmanDirection::Outgoing => ExteriorSlack::Outgoing,
    };
    if selected
        .iter()
        .any(|&balance| balances[balance].exterior_slack == Some(forbidden_slack))
    {
        // This side has a genuinely unbounded exterior arc and therefore
        // cannot yield a finite valid Hoffman inequality.
        return Err(NetworkDesignCompletionError::InvalidProjection);
    }

    let mut rhs = BigRational::zero();
    let mut terms = BTreeMap::new();
    for &balance_index in &selected {
        let balance = balances
            .get(balance_index)
            .ok_or(NetworkDesignCompletionError::InvalidProjection)?;
        rhs += &balance.rhs;
        for &(column, ref coefficient) in &balance.discrete {
            let coefficient = match direction {
                HoffmanDirection::Incoming => coefficient.clone(),
                HoffmanDirection::Outgoing => -coefficient,
            };
            add_term(&mut terms, column, coefficient);
        }
    }

    let component_flows: BTreeSet<usize> = component.flow_columns.iter().copied().collect();
    for flow in flows
        .iter()
        .filter(|flow| component_flows.contains(&flow.original_column))
    {
        let sign: i8 = flow
            .balances
            .iter()
            .filter(|(node, _)| selected.contains(node))
            .map(|(_, sign)| *sign)
            .sum();
        let crosses_selected_side = match direction {
            HoffmanDirection::Incoming => sign == 1,
            HoffmanDirection::Outgoing => sign == -1,
        };
        if crosses_selected_side {
            for &(controller, ref capacity) in &flow.vub.capacity_terms {
                add_term(&mut terms, controller, capacity.clone());
            }
        } else if !matches!(sign, -1 | 0 | 1) {
            return Err(NetworkDesignCompletionError::InvalidProjection);
        }
    }

    if direction == HoffmanDirection::Outgoing {
        rhs = -rhs;
    }
    Ok((terms.into_iter().collect(), rhs))
}

fn flow_endpoints(
    flow: &Flow,
    local_node: &BTreeMap<usize, usize>,
    exterior: usize,
) -> Result<(usize, usize), NetworkDesignCompletionError> {
    if let [(node, sign)] = flow.balances.as_slice() {
        let node = *local_node
            .get(node)
            .ok_or(NetworkDesignCompletionError::InvalidProjection)?;
        return match *sign {
            1 => Ok((exterior, node)),
            -1 => Ok((node, exterior)),
            _ => Err(NetworkDesignCompletionError::InvalidProjection),
        };
    }
    if let [(left, left_sign), (right, right_sign)] = flow.balances.as_slice() {
        if *left_sign != -*right_sign || !matches!(*left_sign, -1 | 1) {
            return Err(NetworkDesignCompletionError::InvalidProjection);
        }
        let left = *local_node
            .get(left)
            .ok_or(NetworkDesignCompletionError::InvalidProjection)?;
        let right = *local_node
            .get(right)
            .ok_or(NetworkDesignCompletionError::InvalidProjection)?;
        return if *left_sign == -1 {
            Ok((left, right))
        } else {
            Ok((right, left))
        };
    }
    Err(NetworkDesignCompletionError::InvalidProjection)
}

/// Find `0 <= x <= capacity` with `inflow - outflow == required` at every
/// node.  Edmonds--Karp is polynomial in graph size independently of rational
/// magnitudes and operates directly on exact residual capacities.
fn exact_transshipment(
    required: Vec<BigRational>,
    arcs: &[CompletionArc],
    deadline: Option<Instant>,
    edge_scans: &mut usize,
) -> Result<Vec<BigRational>, NetworkDesignCompletionError> {
    match exact_transshipment_with_cut(required, arcs, deadline, edge_scans)? {
        TransshipmentOutcome::Feasible(values) => Ok(values),
        TransshipmentOutcome::Infeasible { .. } => Err(NetworkDesignCompletionError::Infeasible),
    }
}

fn exact_transshipment_with_cut(
    required: Vec<BigRational>,
    arcs: &[CompletionArc],
    deadline: Option<Instant>,
    edge_scans: &mut usize,
) -> Result<TransshipmentOutcome, NetworkDesignCompletionError> {
    let node_count = required.len();
    let source = node_count;
    let sink = node_count + 1;
    let mut graph = vec![Vec::<ResidualEdge>::new(); node_count + 2];
    let mut original_edges = Vec::with_capacity(arcs.len());
    for arc in arcs {
        if arc.from >= node_count || arc.to >= node_count || arc.capacity.is_negative() {
            return Err(NetworkDesignCompletionError::InvalidProjection);
        }
        let edge = add_residual_edge(&mut graph, arc.from, arc.to, arc.capacity.clone());
        original_edges.push((arc.from, edge, arc.capacity.clone()));
    }

    let mut target = BigRational::zero();
    for (node, value) in required.iter().enumerate() {
        if value.is_positive() {
            add_residual_edge(&mut graph, node, sink, value.clone());
            target += value;
        } else if value.is_negative() {
            add_residual_edge(&mut graph, source, node, -value);
        }
    }
    if !required.iter().cloned().sum::<BigRational>().is_zero() {
        return Err(NetworkDesignCompletionError::InvalidProjection);
    }

    let mut sent = BigRational::zero();
    while sent < target {
        if expired(deadline) {
            return Err(NetworkDesignCompletionError::Deadline);
        }
        let mut previous = vec![None::<(usize, usize)>; graph.len()];
        let mut queue = VecDeque::new();
        previous[source] = Some((source, usize::MAX));
        queue.push_back(source);
        'search: while let Some(node) = queue.pop_front() {
            for (edge_index, edge) in graph[node].iter().enumerate() {
                *edge_scans = (*edge_scans)
                    .checked_add(1)
                    .ok_or(NetworkDesignCompletionError::CompletionWorkLimit)?;
                if *edge_scans > MAX_COMPLETION_EDGE_SCANS {
                    return Err(NetworkDesignCompletionError::CompletionWorkLimit);
                }
                if *edge_scans & 0x3ff == 0 && expired(deadline) {
                    return Err(NetworkDesignCompletionError::Deadline);
                }
                if edge.capacity.is_positive() && previous[edge.to].is_none() {
                    previous[edge.to] = Some((node, edge_index));
                    if edge.to == sink {
                        break 'search;
                    }
                    queue.push_back(edge.to);
                }
            }
        }
        if previous[sink].is_none() {
            return Ok(TransshipmentOutcome::Infeasible {
                reachable: previous[..node_count].iter().map(Option::is_some).collect(),
            });
        }

        let mut augment = None::<BigRational>;
        let mut node = sink;
        while node != source {
            let (parent, edge) =
                previous[node].ok_or(NetworkDesignCompletionError::InvalidProjection)?;
            let residual = &graph[parent][edge].capacity;
            if augment.as_ref().is_none_or(|current| residual < current) {
                augment = Some(residual.clone());
            }
            node = parent;
        }
        let augment = augment
            .filter(|value| value.is_positive())
            .ok_or(NetworkDesignCompletionError::InvalidProjection)?;
        let mut node = sink;
        while node != source {
            let (parent, edge) =
                previous[node].ok_or(NetworkDesignCompletionError::InvalidProjection)?;
            let reverse = graph[parent][edge].reverse;
            graph[parent][edge].capacity -= &augment;
            graph[node][reverse].capacity += &augment;
            node = parent;
        }
        sent += augment;
    }
    if sent != target {
        return Err(NetworkDesignCompletionError::InvalidProjection);
    }

    Ok(TransshipmentOutcome::Feasible(
        original_edges
            .into_iter()
            .map(|(from, edge, capacity)| capacity - &graph[from][edge].capacity)
            .collect(),
    ))
}

fn add_residual_edge(
    graph: &mut [Vec<ResidualEdge>],
    from: usize,
    to: usize,
    capacity: BigRational,
) -> usize {
    let forward = graph[from].len();
    let reverse = graph[to].len();
    graph[from].push(ResidualEdge {
        to,
        reverse,
        capacity,
    });
    graph[to].push(ResidualEdge {
        to: from,
        reverse: forward,
        capacity: BigRational::zero(),
    });
    forward
}

/// Recognize and exactly project a bounded-integral-master/network-flow model.
pub(crate) fn project_network_design(
    model: &Model,
    deadline: Option<Instant>,
) -> Result<NetworkDesignProjection, NetworkDesignDecline> {
    project_network_design_with_mode(model, deadline, ProjectionMode::Eager)
}

/// Recognize the same exact network-design class, but retain only the bounded
/// integral design master.  Network feasibility is enforced later by
/// [`NetworkDesignProjection::separate_exact`].
pub(crate) fn project_network_design_lazy(
    model: &Model,
    deadline: Option<Instant>,
) -> Result<NetworkDesignProjection, NetworkDesignDecline> {
    project_network_design_with_mode(model, deadline, ProjectionMode::Lazy)
}

fn project_network_design_with_mode(
    model: &Model,
    deadline: Option<Instant>,
    mode: ProjectionMode,
) -> Result<NetworkDesignProjection, NetworkDesignDecline> {
    if expired(deadline) {
        return Err(NetworkDesignDecline::Deadline);
    }
    // Cheap column-only ownership test first.  This recognizer sits on the
    // ordinary production fallback path, so a pure-integer or unrelated mixed
    // model must not pay for a full exact-rational matrix census before the
    // route can see that it does not own the shape.
    let mut integral_columns = Vec::new();
    let mut continuous_columns = Vec::new();
    let mut continuous_objective = Vec::new();
    for column in 0..model.num_cols() {
        if column & 0x3ff == 0 && expired(deadline) {
            return Err(NetworkDesignDecline::Deadline);
        }
        let col = Col(column as u32);
        match model.col_kind(col) {
            ColKind::Binary | ColKind::Integer => {
                let (lb, ub) = model.col_bounds(col);
                if !lb.is_finite() || !ub.is_finite() {
                    return Err(NetworkDesignDecline::UnboundedMasterColumn { column });
                }
                integral_columns.push(column);
            }
            ColKind::Continuous => {
                continuous_columns.push(column);
                let advice = model.obj_coeff(col);
                if !model.obj_coeff_exact_at(column as u32, advice).is_zero() {
                    continuous_objective.push(column);
                }
            }
        }
    }
    if continuous_objective.len() > 1 {
        return Err(NetworkDesignDecline::ObjectiveSingletonCount {
            found: continuous_objective.len(),
        });
    }
    let objective_column = continuous_objective.first().copied();
    let flow_columns: Vec<usize> = continuous_columns
        .into_iter()
        .filter(|column| Some(*column) != objective_column)
        .collect();
    if flow_columns.is_empty() {
        return Err(NetworkDesignDecline::NoFlowColumns);
    }
    for &column in &flow_columns {
        let (lb, ub) = model.col_bounds(Col(column as u32));
        if exact(lb).as_ref().is_none_or(|value| !value.is_zero()) || ub != f64::INFINITY {
            return Err(NetworkDesignDecline::FlowDomain { column });
        }
    }

    model
        .validate()
        .map_err(|_| NetworkDesignDecline::InvalidModel)?;
    let rows = exact_rows(model, deadline)?;

    let (objective_row, objective_expression) = if let Some(objective_column) = objective_column {
        let occurrences: Vec<usize> = rows
            .iter()
            .enumerate()
            .filter_map(|(row, exact_row)| {
                exact_row
                    .terms
                    .iter()
                    .any(|&(column, _)| column == objective_column)
                    .then_some(row)
            })
            .collect();
        if occurrences.len() != 1 {
            return Err(NetworkDesignDecline::ObjectiveNotSingleton {
                column: objective_column,
                occurrences: occurrences.len(),
            });
        }
        let objective_row = occurrences[0];
        let definition = &rows[objective_row];
        let rhs = definition
            .lb
            .as_ref()
            .zip(definition.ub.as_ref())
            .filter(|(lb, ub)| lb == ub)
            .map(|(lb, _)| lb.clone())
            .ok_or(NetworkDesignDecline::ObjectiveDefinitionNotEquality {
                column: objective_column,
            })?;
        if definition.terms.iter().any(|&(column, _)| {
            column != objective_column
                && matches!(model.col_kind(Col(column as u32)), ColKind::Continuous)
        }) {
            return Err(NetworkDesignDecline::ObjectiveDefinitionHasContinuousPeer {
                row: objective_row,
            });
        }
        let objective_pivot = definition
            .terms
            .iter()
            .find(|&&(column, _)| column == objective_column)
            .map(|(_, coefficient)| coefficient.clone())
            .filter(|coefficient| !coefficient.is_zero())
            .ok_or(NetworkDesignDecline::ObjectiveDefinitionNotEquality {
                column: objective_column,
            })?;
        let mut expression = ExactAffine::from_constant(&rhs / &objective_pivot);
        for (column, coefficient) in &definition.terms {
            if *column != objective_column {
                expression.add(*column, -coefficient / &objective_pivot);
            }
        }
        (Some(objective_row), Some(expression))
    } else {
        (None, None)
    };

    let flow_set: BTreeSet<usize> = flow_columns.iter().copied().collect();

    let mut balances = Vec::new();
    let mut master_rows = Vec::new();
    let mut vub_for_flow: Vec<Vec<Vub>> = vec![Vec::new(); model.num_cols()];
    for (row_index, row) in rows.iter().enumerate() {
        if Some(row_index) == objective_row {
            continue;
        }
        if row_index & 0x3f == 0 && expired(deadline) {
            return Err(NetworkDesignDecline::Deadline);
        }
        let flow_terms: Vec<(usize, BigRational)> = row
            .terms
            .iter()
            .filter(|(column, _)| flow_set.contains(column))
            .cloned()
            .collect();
        if flow_terms.is_empty() {
            if row.terms.iter().any(|&(column, _)| {
                matches!(model.col_kind(Col(column as u32)), ColKind::Continuous)
            }) {
                return Err(NetworkDesignDecline::UnsupportedFlowRow { row: row_index });
            }
            master_rows.push(row_index);
            continue;
        }

        if let Some(vub) = recognize_vub(model, row_index, row, &flow_terms)? {
            vub_for_flow[flow_terms[0].0].push(vub);
            continue;
        }
        let (rhs, exterior_slack) = normalize_balance_bounds(row_index, row)?;
        let mut flow_incidence = Vec::with_capacity(flow_terms.len());
        for (column, coefficient) in flow_terms {
            let sign = if coefficient == BigRational::one() {
                1
            } else if coefficient == -BigRational::one() {
                -1
            } else {
                return Err(NetworkDesignDecline::NonIncidenceCoefficient { row: row_index });
            };
            flow_incidence.push((column, sign));
        }
        let discrete = row
            .terms
            .iter()
            .filter(|(column, _)| !flow_set.contains(column))
            .cloned()
            .collect();
        balances.push(Balance {
            original_row: row_index,
            rhs,
            discrete,
            flows: flow_incidence,
            exterior_slack,
        });
    }

    let mut flow_balances: Vec<Vec<(usize, i8)>> = vec![Vec::new(); model.num_cols()];
    for (balance_index, balance) in balances.iter().enumerate() {
        for &(flow, sign) in &balance.flows {
            flow_balances[flow].push((balance_index, sign));
        }
    }
    let mut flows = Vec::with_capacity(flow_columns.len());
    for &column in &flow_columns {
        let vubs = &vub_for_flow[column];
        if vubs.len() != 1 {
            return Err(NetworkDesignDecline::FlowVubCount {
                column,
                count: vubs.len(),
            });
        }
        let incidence = &flow_balances[column];
        if !(1..=2).contains(&incidence.len()) {
            return Err(NetworkDesignDecline::FlowBalanceDegree {
                column,
                count: incidence.len(),
            });
        }
        if incidence.len() == 2 && incidence[0].1 == incidence[1].1 {
            return Err(NetworkDesignDecline::FlowIncidenceSigns { column });
        }
        flows.push(Flow {
            original_column: column,
            vub: vubs[0].clone(),
            balances: incidence.clone(),
        });
    }

    let mut components = connected_components(&balances, &flows, deadline)?;
    let mut retained_flow_bounds = BTreeMap::new();
    let mut retained_flow_bits = 0usize;
    let mut projected_rows = 0usize;
    let mut projected_arc_scans = 0usize;
    for component in &mut components {
        if mode == ProjectionMode::Lazy {
            continue;
        }
        let subsets = 1usize
            .checked_shl(component.balance_rows.len() as u32)
            .and_then(|value| value.checked_sub(1));
        let component_arc_scans = subsets
            .and_then(|count| count.checked_mul(component.flow_columns.len()))
            .unwrap_or(usize::MAX);
        let should_try_retained = component.balance_rows.len() > MAX_COMPONENT_NODES
            || component_arc_scans > COMPACT_MASTER_HOFFMAN_ARC_SCANS;
        let retained_bounds = should_try_retained
            .then(|| certify_retained_component(model, &balances, &flows, component, deadline))
            .transpose();
        let retained_bounds = match retained_bounds {
            Ok(Some(bounds)) => Some(bounds),
            Ok(None) => None,
            Err(NetworkDesignDecline::Deadline) => return Err(NetworkDesignDecline::Deadline),
            Err(NetworkDesignDecline::InvalidModel) => {
                return Err(NetworkDesignDecline::InvalidModel)
            }
            // A nonintegral supply/capacity or an inexactly encodable retained
            // domain invalidates only the stronger TU/integer restriction.
            // The rational Hoffman projection remains exact and is attempted
            // below whenever its independent hard caps permit it.
            Err(_) if component.balance_rows.len() <= MAX_COMPONENT_NODES => None,
            Err(reason) => return Err(reason),
        };
        if let Some(bounds) = retained_bounds {
            for (column, upper) in bounds {
                retained_flow_bits = retained_flow_bits
                    .checked_add(integer_radix_bits(&upper))
                    .ok_or(NetworkDesignDecline::TooManyRetainedFlowBits {
                        bits: usize::MAX,
                        cap: MAX_RETAINED_FLOW_BITS,
                    })?;
                if retained_flow_bits > MAX_RETAINED_FLOW_BITS {
                    return Err(NetworkDesignDecline::TooManyRetainedFlowBits {
                        bits: retained_flow_bits,
                        cap: MAX_RETAINED_FLOW_BITS,
                    });
                }
                retained_flow_bounds.insert(column, upper);
            }
            component.retained_flows = true;
            continue;
        }
        let subsets = subsets.ok_or(NetworkDesignDecline::ComponentTooLarge {
            nodes: component.balance_rows.len(),
            cap: MAX_COMPONENT_NODES,
        })?;
        projected_rows = projected_rows
            .checked_add(subsets.saturating_mul(2))
            .ok_or(NetworkDesignDecline::TooManyHoffmanRows {
                rows: usize::MAX,
                cap: MAX_HOFFMAN_ROWS,
            })?;
        if projected_rows > MAX_HOFFMAN_ROWS {
            return Err(NetworkDesignDecline::TooManyHoffmanRows {
                rows: projected_rows,
                cap: MAX_HOFFMAN_ROWS,
            });
        }
        projected_arc_scans = projected_arc_scans
            .checked_add(subsets.saturating_mul(component.flow_columns.len()))
            .ok_or(NetworkDesignDecline::TooManyHoffmanArcScans {
                scans: usize::MAX,
                cap: MAX_HOFFMAN_ARC_SCANS,
            })?;
        if projected_arc_scans > MAX_HOFFMAN_ARC_SCANS {
            return Err(NetworkDesignDecline::TooManyHoffmanArcScans {
                scans: projected_arc_scans,
                cap: MAX_HOFFMAN_ARC_SCANS,
            });
        }
    }

    let (mut master, master_to_original, original_to_master) =
        build_master_columns(model, &integral_columns, &retained_flow_bounds)?;
    for &row in &master_rows {
        add_exact_row(
            &mut master,
            &original_to_master,
            &rows[row].terms,
            rows[row].lb.as_ref(),
            rows[row].ub.as_ref(),
        )?;
    }

    // A TU-certified retained component keeps its exact original balance and
    // capacity rows.  Pure-master rows were already copied above.
    let flow_by_original: BTreeMap<usize, &Flow> = flows
        .iter()
        .map(|flow| (flow.original_column, flow))
        .collect();
    let mut retained_rows = BTreeSet::new();
    for component in components
        .iter()
        .filter(|component| component.retained_flows)
    {
        retained_rows.extend(component.balance_rows.iter().copied());
        for column in &component.flow_columns {
            let flow = flow_by_original
                .get(column)
                .ok_or(NetworkDesignDecline::InvalidModel)?;
            retained_rows.insert(flow.vub.original_row);
        }
    }
    for row in retained_rows {
        add_exact_row(
            &mut master,
            &original_to_master,
            &rows[row].terms,
            rows[row].lb.as_ref(),
            rows[row].ub.as_ref(),
        )?;
    }

    // Preserve a finite declared box on the eliminated objective singleton.
    if let (Some(objective_column), Some(objective_expression)) =
        (objective_column, objective_expression.as_ref())
    {
        let (objective_lb, objective_ub) = model.col_bounds(Col(objective_column as u32));
        if (objective_lb.is_infinite() && objective_lb != f64::NEG_INFINITY)
            || (objective_ub.is_infinite() && objective_ub != f64::INFINITY)
        {
            return Err(NetworkDesignDecline::InvalidModel);
        }
        if let Some(lower) = exact(objective_lb) {
            add_affine_lower(
                &mut master,
                &original_to_master,
                objective_expression,
                &lower,
            )?;
        }
        if let Some(upper) = exact(objective_ub) {
            add_affine_upper(
                &mut master,
                &original_to_master,
                objective_expression,
                &upper,
            )?;
        }
    }

    let hoffman_rows = match mode {
        ProjectionMode::Eager => emit_hoffman_rows(
            &mut master,
            &original_to_master,
            &balances,
            &flows,
            &components,
            deadline,
        )?,
        ProjectionMode::Lazy => emit_lazy_seed_hoffman_rows(
            &mut master,
            &original_to_master,
            &balances,
            &flows,
            &components,
            deadline,
        )?,
    };
    install_projected_objective(
        &mut master,
        model,
        &original_to_master,
        objective_column,
        objective_expression.as_ref(),
    )?;

    let objective_lift = match (objective_column, objective_expression) {
        (Some(original_column), Some(expression)) => Some(ObjectiveLift {
            original_column,
            constant: expression.constant,
            terms: expression
                .terms
                .into_iter()
                .map(|(original, coefficient)| {
                    original_to_master[original]
                        .map(|master| (master.0, coefficient))
                        .ok_or(NetworkDesignDecline::InvalidModel)
                })
                .collect::<Result<_, _>>()?,
        }),
        (None, None) => None,
        _ => return Err(NetworkDesignDecline::InvalidModel),
    };

    Ok(NetworkDesignProjection {
        master,
        master_to_original,
        original_to_master,
        components,
        hoffman_rows,
        objective_lift,
        balances,
        flows,
    })
}

fn expired(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|limit| Instant::now() >= limit)
}

fn block_symmetry_expired(deadline: Option<Instant>) -> bool {
    expired(deadline)
}

fn charge_block_symmetry_work(
    work: &mut usize,
    amount: usize,
    deadline: Option<Instant>,
) -> Option<()> {
    if block_symmetry_expired(deadline) {
        return None;
    }
    let next = work.checked_add(amount)?;
    if next > MAX_BLOCK_SYMMETRY_WORK {
        return None;
    }
    *work = next;
    Some(())
}

fn block_swap_permutation(
    left: &[u32],
    right: &[u32],
    deadline: Option<Instant>,
) -> Option<BTreeMap<u32, u32>> {
    if left.is_empty() || left.len() != right.len() {
        return None;
    }
    let mut permutation = BTreeMap::new();
    for (index, (&left, &right)) in left.iter().zip(right).enumerate() {
        if index & 0x3f == 0 && block_symmetry_expired(deadline) {
            return None;
        }
        if left == right {
            continue;
        }
        for (source, target) in [(left, right), (right, left)] {
            if permutation
                .insert(source, target)
                .is_some_and(|previous| previous != target)
            {
                return None;
            }
        }
    }
    let domain: BTreeSet<u32> = permutation.keys().copied().collect();
    let image: BTreeSet<u32> = permutation.values().copied().collect();
    (!permutation.is_empty() && domain == image && image.len() == permutation.len())
        .then_some(permutation)
}

fn integer_radix_bits(value: &BigInt) -> usize {
    let mut remaining = value.clone();
    let mut bits = 0usize;
    while remaining.is_positive() {
        remaining >>= 1usize;
        bits += 1;
    }
    bits
}

fn exact_rows(
    model: &Model,
    deadline: Option<Instant>,
) -> Result<Vec<ExactRow>, NetworkDesignDecline> {
    let mut total_terms = 0usize;
    let mut rows = Vec::with_capacity(model.num_rows());
    for row_index in 0..model.num_rows() {
        if row_index & 0x3f == 0 && expired(deadline) {
            return Err(NetworkDesignDecline::Deadline);
        }
        let (stored, lb, ub) = model.row(Row(row_index as u32));
        if (lb.is_infinite() && lb != f64::NEG_INFINITY)
            || (ub.is_infinite() && ub != f64::INFINITY)
        {
            return Err(NetworkDesignDecline::InvalidModel);
        }
        total_terms = total_terms
            .checked_add(stored.len())
            .ok_or(NetworkDesignDecline::TooManyTerms)?;
        if total_terms > MAX_EXACT_TERMS {
            return Err(NetworkDesignDecline::TooManyTerms);
        }
        let mut terms = Vec::with_capacity(stored.len());
        for (term_index, &(column, advice)) in stored.iter().enumerate() {
            if term_index & 0x3ff == 0 && expired(deadline) {
                return Err(NetworkDesignDecline::Deadline);
            }
            let coefficient = model.row_coeff_exact(row_index, column, advice);
            if !coefficient.is_zero() {
                terms.push((column as usize, coefficient));
            }
        }
        rows.push(ExactRow {
            terms,
            lb: model.row_lb_exact(row_index, lb),
            ub: model.row_ub_exact(row_index, ub),
        });
    }
    Ok(rows)
}

fn bounded_nonnegative_integral(model: &Model, column: usize) -> bool {
    let col = Col(column as u32);
    if !model.col_kind(col).is_integral() {
        return false;
    }
    let (lb, ub) = model.col_bounds(col);
    let (Some(lb), Some(ub)) = (exact(lb), exact(ub)) else {
        return false;
    };
    let lo = lb.numer().div_ceil(lb.denom());
    let hi = ub.numer().div_floor(ub.denom());
    lo >= BigInt::zero() && lo <= hi
}

fn recognize_vub(
    model: &Model,
    row_index: usize,
    row: &ExactRow,
    flow_terms: &[(usize, BigRational)],
) -> Result<Option<Vub>, NetworkDesignDecline> {
    if flow_terms.len() != 1 || row.terms.len() < 2 {
        return Ok(None);
    }
    let (orientation, rhs) = match (&row.lb, &row.ub) {
        (None, Some(upper)) => (BigRational::one(), upper.clone()),
        (Some(lower), None) => (-BigRational::one(), -lower),
        _ => return Ok(None),
    };
    if !rhs.is_zero() {
        return Ok(None);
    }
    let flow = flow_terms[0].0;
    let flow_coefficient = &orientation * &flow_terms[0].1;
    if !flow_coefficient.is_positive() {
        return Ok(None);
    }
    let mut capacity_terms = Vec::with_capacity(row.terms.len() - 1);
    for (controller, stored_controller) in row.terms.iter().filter(|&&(column, _)| column != flow) {
        let controller_coefficient = &orientation * stored_controller;
        // This is not a capacity row, but it may still be a valid one-sided
        // balance with an affine integral supply.  Let the balance recognizer
        // make that exact interpretation instead of guessing.
        if !controller_coefficient.is_negative() {
            return Ok(None);
        }
        if !bounded_nonnegative_integral(model, *controller) {
            return Err(NetworkDesignDecline::InvalidControllerDomain {
                column: *controller,
            });
        }
        let capacity = -controller_coefficient / &flow_coefficient;
        if !capacity.is_positive() {
            return Err(NetworkDesignDecline::InvalidVub { row: row_index });
        }
        capacity_terms.push((*controller, capacity));
    }
    if capacity_terms.is_empty() {
        return Ok(None);
    }
    Ok(Some(Vub {
        original_row: row_index,
        capacity_terms,
    }))
}

fn normalize_balance_bounds(
    row_index: usize,
    row: &ExactRow,
) -> Result<(BigRational, Option<ExteriorSlack>), NetworkDesignDecline> {
    match (&row.lb, &row.ub) {
        (Some(lower), Some(upper)) if lower == upper => Ok((lower.clone(), None)),
        (Some(lower), None) => Ok((lower.clone(), Some(ExteriorSlack::Outgoing))),
        (None, Some(upper)) => Ok((upper.clone(), Some(ExteriorSlack::Incoming))),
        (Some(_), Some(_)) => {
            Err(NetworkDesignDecline::UnsupportedBalanceBounds { row: row_index })
        }
        (None, None) => Err(NetworkDesignDecline::UnsupportedFlowRow { row: row_index }),
    }
}

fn connected_components(
    balances: &[Balance],
    flows: &[Flow],
    deadline: Option<Instant>,
) -> Result<Vec<ProjectedNetworkComponent>, NetworkDesignDecline> {
    if balances.is_empty() {
        let column = flows.first().map_or(0, |flow| flow.original_column);
        return Err(NetworkDesignDecline::FlowBalanceDegree { column, count: 0 });
    }
    let mut parent: Vec<usize> = (0..balances.len()).collect();
    for (work, flow) in flows.iter().enumerate() {
        if work & 0x3ff == 0 && expired(deadline) {
            return Err(NetworkDesignDecline::Deadline);
        }
        if flow.balances.len() == 2 {
            union(&mut parent, flow.balances[0].0, flow.balances[1].0);
        }
    }
    let mut roots = Vec::with_capacity(balances.len());
    let mut by_root: BTreeMap<usize, ProjectedNetworkComponent> = BTreeMap::new();
    for node in 0..balances.len() {
        if node & 0x3ff == 0 && expired(deadline) {
            return Err(NetworkDesignDecline::Deadline);
        }
        let root = find(&mut parent, node);
        roots.push(root);
        by_root
            .entry(root)
            .or_insert_with(|| ProjectedNetworkComponent {
                balance_rows: Vec::new(),
                flow_columns: Vec::new(),
                retained_flows: false,
            })
            .balance_rows
            .push(balances[node].original_row);
    }
    // Assign arcs in one pass.  Scanning every arc once per connected
    // component is quadratic on a valid model made of many independent
    // one-node networks and can overrun the route's deadline before the first
    // PB call.  Every two-ended arc was unioned above; checking the cached roots
    // here also keeps a malformed component map fail-closed.
    for (work, flow) in flows.iter().enumerate() {
        if work & 0x3ff == 0 && expired(deadline) {
            return Err(NetworkDesignDecline::Deadline);
        }
        let (&(first, _), rest) = flow
            .balances
            .split_first()
            .ok_or(NetworkDesignDecline::InvalidModel)?;
        let root = *roots.get(first).ok_or(NetworkDesignDecline::InvalidModel)?;
        if rest
            .iter()
            .any(|&(node, _)| roots.get(node).copied() != Some(root))
        {
            return Err(NetworkDesignDecline::InvalidModel);
        }
        by_root
            .get_mut(&root)
            .ok_or(NetworkDesignDecline::InvalidModel)?
            .flow_columns
            .push(flow.original_column);
    }
    Ok(by_root.into_values().collect())
}

fn find(parent: &mut [usize], mut node: usize) -> usize {
    while parent[node] != node {
        parent[node] = parent[parent[node]];
        node = parent[node];
    }
    node
}

fn union(parent: &mut [usize], left: usize, right: usize) {
    let left = find(parent, left);
    let right = find(parent, right);
    if left != right {
        let (small, large) = if left < right {
            (left, right)
        } else {
            (right, left)
        };
        parent[large] = small;
    }
}

/// Certify the exact retained-flow formulation for a component that is too
/// large for explicit Hoffman enumeration.  Once the bounded integral master
/// is fixed, the remaining matrix consists only of directed node-arc
/// incidence, unit-bound slack arcs, and variable upper bounds.  Integral
/// supplies and capacities therefore give a totally-unimodular
/// transshipment polytope: continuous feasibility implies integral flow
/// feasibility at the same design and objective value.
fn certify_retained_component(
    model: &Model,
    balances: &[Balance],
    flows: &[Flow],
    component: &ProjectedNetworkComponent,
    deadline: Option<Instant>,
) -> Result<Vec<(usize, BigInt)>, NetworkDesignDecline> {
    let balance_by_original: BTreeMap<usize, &Balance> = balances
        .iter()
        .map(|balance| (balance.original_row, balance))
        .collect();
    let flow_by_original: BTreeMap<usize, &Flow> = flows
        .iter()
        .map(|flow| (flow.original_column, flow))
        .collect();
    let component_balance_indices: BTreeSet<usize> = component
        .balance_rows
        .iter()
        .map(|row| {
            balances
                .iter()
                .position(|balance| balance.original_row == *row)
                .ok_or(NetworkDesignDecline::InvalidModel)
        })
        .collect::<Result<_, _>>()?;

    for (work, row) in component.balance_rows.iter().enumerate() {
        if work & 0x3f == 0 && expired(deadline) {
            return Err(NetworkDesignDecline::Deadline);
        }
        let balance = balance_by_original
            .get(row)
            .ok_or(NetworkDesignDecline::InvalidModel)?;
        if !balance.rhs.is_integer()
            || balance.discrete.iter().any(|(column, coefficient)| {
                !coefficient.is_integer() || !model.col_kind(Col(*column as u32)).is_integral()
            })
        {
            return Err(NetworkDesignDecline::NonIntegralRetainedSupply { row: *row });
        }
        if balance
            .flows
            .iter()
            .any(|(column, _)| !component.flow_columns.contains(column))
        {
            return Err(NetworkDesignDecline::InvalidModel);
        }
    }

    let mut bounds = Vec::with_capacity(component.flow_columns.len());
    for (work, &column) in component.flow_columns.iter().enumerate() {
        if work & 0x3f == 0 && expired(deadline) {
            return Err(NetworkDesignDecline::Deadline);
        }
        let flow = flow_by_original
            .get(&column)
            .ok_or(NetworkDesignDecline::InvalidModel)?;
        if !model
            .obj_coeff_exact_at(column as u32, model.obj_coeff(Col(column as u32)))
            .is_zero()
            || flow
                .balances
                .iter()
                .any(|(balance, _)| !component_balance_indices.contains(balance))
        {
            return Err(NetworkDesignDecline::NonIntegralRetainedCapacity { column });
        }

        let mut upper = BigInt::zero();
        for &(controller, ref capacity) in &flow.vub.capacity_terms {
            if !capacity.is_integer() || !capacity.is_positive() {
                return Err(NetworkDesignDecline::NonIntegralRetainedCapacity { column });
            }
            let controller_col = Col(controller as u32);
            if !model.col_kind(controller_col).is_integral() {
                return Err(NetworkDesignDecline::NonIntegralRetainedCapacity { column });
            }
            let (lb, ub) = model.col_bounds(controller_col);
            let (Some(lb), Some(ub)) = (exact(lb), exact(ub)) else {
                return Err(NetworkDesignDecline::RetainedFlowDomain { column });
            };
            let lo = lb.numer().div_ceil(lb.denom());
            let hi = ub.numer().div_floor(ub.denom());
            if lo.is_negative() || lo > hi {
                return Err(NetworkDesignDecline::RetainedFlowDomain { column });
            }
            let weight = capacity.to_integer();
            upper += weight * hi;
        }
        if upper.is_negative() {
            return Err(NetworkDesignDecline::RetainedFlowDomain { column });
        }
        bounds.push((column, upper));
    }
    Ok(bounds)
}

fn build_master_columns(
    model: &Model,
    integral_columns: &[usize],
    retained_flow_bounds: &BTreeMap<usize, BigInt>,
) -> Result<(Model, Vec<Col>, Vec<Option<Col>>), NetworkDesignDecline> {
    let mut master = Model::new();
    master.inherit_ft_adoption_solve_latch(model);
    let mut master_to_original =
        Vec::with_capacity(integral_columns.len() + retained_flow_bounds.len());
    let mut original_to_master = vec![None; model.num_cols()];
    for &original in integral_columns {
        let source = Col(original as u32);
        let (lb, ub) = model.col_bounds(source);
        let target = match model.col_kind(source) {
            ColKind::Binary => {
                let target = master.add_binary_col();
                master.set_col_bounds(target, lb, ub);
                target
            }
            ColKind::Integer => master.add_int_col(lb, ub),
            ColKind::Continuous => return Err(NetworkDesignDecline::InvalidModel),
        };
        original_to_master[original] = Some(target);
        master_to_original.push(source);
    }
    for (&original, upper) in retained_flow_bounds {
        let upper_rational = BigRational::from_integer(upper.clone());
        let upper_advice = upper
            .to_f64()
            .filter(|value| value.is_finite())
            .filter(|value| exact(*value).as_ref() == Some(&upper_rational))
            .ok_or(NetworkDesignDecline::RetainedFlowDomain { column: original })?;
        let target = master.add_int_col(0.0, upper_advice);
        original_to_master[original] = Some(target);
        master_to_original.push(Col(original as u32));
    }
    Ok((master, master_to_original, original_to_master))
}

fn emit_hoffman_rows(
    master: &mut Model,
    original_to_master: &[Option<Col>],
    balances: &[Balance],
    flows: &[Flow],
    components: &[ProjectedNetworkComponent],
    deadline: Option<Instant>,
) -> Result<usize, NetworkDesignDecline> {
    let balance_by_original: BTreeMap<usize, usize> = balances
        .iter()
        .enumerate()
        .map(|(index, balance)| (balance.original_row, index))
        .collect();
    let flow_by_original: BTreeMap<usize, usize> = flows
        .iter()
        .enumerate()
        .map(|(index, flow)| (flow.original_column, index))
        .collect();

    let mut work = 0usize;
    let mut emitted = 0usize;
    for component in components {
        if component.retained_flows {
            continue;
        }
        let nodes: Vec<usize> = component
            .balance_rows
            .iter()
            .map(|row| balance_by_original[row])
            .collect();
        let component_flows: Vec<&Flow> = component
            .flow_columns
            .iter()
            .map(|column| &flows[flow_by_original[column]])
            .collect();
        let subset_end = 1usize << nodes.len();
        for mask in 1usize..subset_end {
            work += 1;
            if work & 0x3f == 0 && expired(deadline) {
                return Err(NetworkDesignDecline::Deadline);
            }
            let selected: BTreeSet<usize> = nodes
                .iter()
                .enumerate()
                .filter_map(|(bit, &node)| (mask & (1usize << bit) != 0).then_some(node))
                .collect();
            emitted += emit_hoffman_subset_rows(
                master,
                original_to_master,
                balances,
                &component_flows,
                &selected,
                deadline,
            )?;
        }
    }
    Ok(emitted)
}

/// Install the polynomial-size root cut pool used by lazy decomposition.
/// Every row goes through the same constructor as the exhaustive projection;
/// this changes only when a valid Hoffman row is installed, never its algebra.
fn emit_lazy_seed_hoffman_rows(
    master: &mut Model,
    original_to_master: &[Option<Col>],
    balances: &[Balance],
    flows: &[Flow],
    components: &[ProjectedNetworkComponent],
    deadline: Option<Instant>,
) -> Result<usize, NetworkDesignDecline> {
    let balance_by_original: BTreeMap<usize, usize> = balances
        .iter()
        .enumerate()
        .map(|(index, balance)| (balance.original_row, index))
        .collect();
    let flow_by_original: BTreeMap<usize, usize> = flows
        .iter()
        .enumerate()
        .map(|(index, flow)| (flow.original_column, index))
        .collect();

    let mut admitted_scans = 0usize;
    let mut emitted = 0usize;
    for component in components {
        if expired(deadline) {
            return Err(NetworkDesignDecline::Deadline);
        }
        let node_count = component.balance_rows.len();
        if !(MIN_LAZY_SEED_COMPONENT_NODES..=MAX_LAZY_SEED_COMPONENT_NODES).contains(&node_count) {
            continue;
        }
        let component_scans = node_count
            .checked_add(1)
            .and_then(|subsets| subsets.checked_mul(component.flow_columns.len()))
            .unwrap_or(usize::MAX);
        let Some(next_scans) = admitted_scans.checked_add(component_scans) else {
            continue;
        };
        if next_scans > MAX_LAZY_SEED_ARC_SCANS {
            continue;
        }
        admitted_scans = next_scans;

        let nodes = component
            .balance_rows
            .iter()
            .map(|row| {
                balance_by_original
                    .get(row)
                    .copied()
                    .ok_or(NetworkDesignDecline::InvalidModel)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let component_flows = component
            .flow_columns
            .iter()
            .map(|column| {
                flow_by_original
                    .get(column)
                    .map(|&index| &flows[index])
                    .ok_or(NetworkDesignDecline::InvalidModel)
            })
            .collect::<Result<Vec<_>, _>>()?;

        for &node in &nodes {
            if expired(deadline) {
                return Err(NetworkDesignDecline::Deadline);
            }
            emitted += emit_hoffman_subset_rows(
                master,
                original_to_master,
                balances,
                &component_flows,
                &BTreeSet::from([node]),
                deadline,
            )?;
        }
        emitted += emit_hoffman_subset_rows(
            master,
            original_to_master,
            balances,
            &component_flows,
            &nodes.into_iter().collect(),
            deadline,
        )?;
    }
    Ok(emitted)
}

/// Emit the two finite directed Hoffman sides for one nonempty node subset.
/// `rhs - demand == sum(sign_e*x_e)`; positive-sign capacities bound it above,
/// negative-sign capacities bound it below.  A side crossed by a semantically
/// unbounded implicit exterior slack is omitted.
fn emit_hoffman_subset_rows(
    master: &mut Model,
    original_to_master: &[Option<Col>],
    balances: &[Balance],
    component_flows: &[&Flow],
    selected: &BTreeSet<usize>,
    deadline: Option<Instant>,
) -> Result<usize, NetworkDesignDecline> {
    if selected.is_empty() {
        return Err(NetworkDesignDecline::InvalidModel);
    }
    let mut rhs = BigRational::zero();
    let mut demand = BTreeMap::new();
    for &node in selected {
        let balance = balances
            .get(node)
            .ok_or(NetworkDesignDecline::InvalidModel)?;
        rhs += &balance.rhs;
        for &(column, ref coefficient) in &balance.discrete {
            add_term(&mut demand, column, coefficient.clone());
        }
    }
    let upper_unbounded = selected
        .iter()
        .any(|&node| balances[node].exterior_slack == Some(ExteriorSlack::Incoming));
    let lower_unbounded = selected
        .iter()
        .any(|&node| balances[node].exterior_slack == Some(ExteriorSlack::Outgoing));

    let mut upper = demand.clone();
    let mut lower = demand
        .iter()
        .map(|(&column, coefficient)| (column, -coefficient))
        .collect::<BTreeMap<_, _>>();
    for (flow_index, flow) in component_flows.iter().enumerate() {
        if flow_index & 0x3ff == 0 && expired(deadline) {
            return Err(NetworkDesignDecline::Deadline);
        }
        let sign: i8 = flow
            .balances
            .iter()
            .filter(|(node, _)| selected.contains(node))
            .map(|(_, sign)| *sign)
            .sum();
        match sign {
            1 => {
                for &(controller, ref capacity) in &flow.vub.capacity_terms {
                    add_term(&mut upper, controller, capacity.clone());
                }
            }
            -1 => {
                for &(controller, ref capacity) in &flow.vub.capacity_terms {
                    add_term(&mut lower, controller, capacity.clone());
                }
            }
            0 => {}
            _ => return Err(NetworkDesignDecline::InvalidModel),
        }
    }

    let mut emitted = 0usize;
    if !upper_unbounded {
        add_exact_row(
            master,
            original_to_master,
            &upper.into_iter().collect::<Vec<_>>(),
            Some(&rhs),
            None,
        )?;
        emitted += 1;
    }
    if !lower_unbounded {
        add_exact_row(
            master,
            original_to_master,
            &lower.into_iter().collect::<Vec<_>>(),
            Some(&-rhs),
            None,
        )?;
        emitted += 1;
    }
    Ok(emitted)
}

#[derive(Debug, Clone)]
struct ExactAffine {
    constant: BigRational,
    terms: BTreeMap<usize, BigRational>,
}

impl ExactAffine {
    fn from_constant(constant: BigRational) -> Self {
        Self {
            constant,
            terms: BTreeMap::new(),
        }
    }

    fn add(&mut self, column: usize, coefficient: BigRational) {
        add_term(&mut self.terms, column, coefficient);
    }
}

fn add_term(terms: &mut BTreeMap<usize, BigRational>, column: usize, coefficient: BigRational) {
    if coefficient.is_zero() {
        return;
    }
    let remove = {
        let entry = terms.entry(column).or_insert_with(BigRational::zero);
        *entry += coefficient;
        entry.is_zero()
    };
    if remove {
        terms.remove(&column);
    }
}

fn add_affine_lower(
    model: &mut Model,
    map: &[Option<Col>],
    expression: &ExactAffine,
    lower: &BigRational,
) -> Result<(), NetworkDesignDecline> {
    add_exact_row(
        model,
        map,
        &expression
            .terms
            .iter()
            .map(|(&column, coefficient)| (column, coefficient.clone()))
            .collect::<Vec<_>>(),
        Some(&(lower - &expression.constant)),
        None,
    )
    .map(|_| ())
}

fn add_affine_upper(
    model: &mut Model,
    map: &[Option<Col>],
    expression: &ExactAffine,
    upper: &BigRational,
) -> Result<(), NetworkDesignDecline> {
    add_exact_row(
        model,
        map,
        &expression
            .terms
            .iter()
            .map(|(&column, coefficient)| (column, -coefficient))
            .collect::<Vec<_>>(),
        Some(&(&expression.constant - upper)),
        None,
    )
    .map(|_| ())
}

fn install_projected_objective(
    master: &mut Model,
    original: &Model,
    original_to_master: &[Option<Col>],
    objective_column: Option<usize>,
    objective_expression: Option<&ExactAffine>,
) -> Result<(), NetworkDesignDecline> {
    let mut coefficients = BTreeMap::new();
    for source in 0..original.num_cols() {
        let Some(master_column) = original_to_master[source].map(Col::index) else {
            continue;
        };
        let coefficient =
            original.obj_coeff_exact_at(source as u32, original.obj_coeff(Col(source as u32)));
        if !coefficient.is_zero() {
            coefficients.insert(master_column, coefficient);
        }
    }
    let mut exact_offset = original.obj_offset_exact();
    match (objective_column, objective_expression) {
        (Some(column), Some(expression)) => {
            let objective_scale =
                original.obj_coeff_exact_at(column as u32, original.obj_coeff(Col(column as u32)));
            for (&source, coefficient) in &expression.terms {
                let master_column = original_to_master[source]
                    .map(Col::index)
                    .ok_or(NetworkDesignDecline::InvalidModel)?;
                add_term(
                    &mut coefficients,
                    master_column,
                    &objective_scale * coefficient,
                );
            }
            exact_offset += &objective_scale * &expression.constant;
        }
        (None, None) => {}
        _ => return Err(NetworkDesignDecline::InvalidModel),
    }
    let mut stored = Vec::with_capacity(coefficients.len());
    let mut overrides = Vec::new();
    for (column, coefficient) in coefficients {
        if coefficient.is_zero() {
            continue;
        }
        let advice =
            coefficient_advice(&coefficient).ok_or(NetworkDesignDecline::ObjectiveAdvice)?;
        let col = Col(column as u32);
        stored.push((col, advice));
        if exact(advice).as_ref() != Some(&coefficient) {
            overrides.push((col.0, coefficient));
        }
    }
    if !original.has_objective() {
        if !stored.is_empty() || !exact_offset.is_zero() {
            return Err(NetworkDesignDecline::InvalidModel);
        }
        return Ok(());
    }
    master.set_objective(&stored, original.sense());
    let offset_advice = exact_offset
        .to_f64()
        .filter(|value| value.is_finite())
        .ok_or(NetworkDesignDecline::ObjectiveAdvice)?;
    master.set_objective_offset(offset_advice);
    for (column, coefficient) in overrides {
        master.record_inexact_obj_coeff(column, coefficient);
    }
    if exact(offset_advice).as_ref() != Some(&exact_offset) {
        master.record_inexact_obj_offset(exact_offset);
    }
    Ok(())
}

fn add_exact_row(
    model: &mut Model,
    map: &[Option<Col>],
    original_terms: &[(usize, BigRational)],
    lb: Option<&BigRational>,
    ub: Option<&BigRational>,
) -> Result<Row, NetworkDesignDecline> {
    let mut merged = BTreeMap::new();
    for &(column, ref coefficient) in original_terms {
        add_term(&mut merged, column, coefficient.clone());
    }
    let mut stored = Vec::with_capacity(merged.len());
    let mut overrides = Vec::new();
    for (original, coefficient) in merged {
        let column = map
            .get(original)
            .and_then(|column| *column)
            .ok_or(NetworkDesignDecline::InvalidModel)?;
        let advice =
            coefficient_advice(&coefficient).ok_or(NetworkDesignDecline::CoefficientAdvice)?;
        stored.push((column, advice));
        if exact(advice).as_ref() != Some(&coefficient) {
            overrides.push((column.0, coefficient));
        }
    }
    let lb_advice = match lb {
        Some(value) => value
            .to_f64()
            .filter(|value| value.is_finite())
            .ok_or(NetworkDesignDecline::BoundAdvice)?,
        None => f64::NEG_INFINITY,
    };
    let ub_advice = match ub {
        Some(value) => value
            .to_f64()
            .filter(|value| value.is_finite())
            .ok_or(NetworkDesignDecline::BoundAdvice)?,
        None => f64::INFINITY,
    };
    let row = model.add_row(lb_advice, ub_advice, &stored);
    for (column, coefficient) in overrides {
        model.record_inexact_row_coeff(row, column, coefficient);
    }
    if let Some(value) = lb {
        if exact(lb_advice).as_ref() != Some(value) {
            model.record_inexact_row_bound(row, true, value.clone());
        }
    }
    if let Some(value) = ub {
        if exact(ub_advice).as_ref() != Some(value) {
            model.record_inexact_row_bound(row, false, value.clone());
        }
    }
    Ok(row)
}

fn coefficient_advice(value: &BigRational) -> Option<f64> {
    if value.is_zero() {
        return Some(0.0);
    }
    value
        .to_f64()
        .filter(|advice| advice.is_finite() && *advice != 0.0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Sense;

    fn br(value: i64) -> BigRational {
        BigRational::from_integer(value.into())
    }

    fn repeated_single_node_blocks(
        block_count: usize,
        columns_per_block: usize,
        wide_columns_per_block: usize,
        perturb_last_block: bool,
    ) -> Model {
        let mut model = Model::new();
        let mut flows = vec![Vec::with_capacity(columns_per_block); block_count];
        for _role in 0..columns_per_block {
            for block in &mut flows {
                block.push(model.add_col(0.0, f64::INFINITY));
            }
        }
        let mut controllers = vec![Vec::with_capacity(columns_per_block); block_count];
        for role in 0..columns_per_block {
            for block in &mut controllers {
                let controller = if role < wide_columns_per_block {
                    model.add_int_col(0.0, 2.0)
                } else {
                    model.add_binary_col()
                };
                block.push(controller);
            }
        }

        for block_flows in &flows {
            let terms = block_flows
                .iter()
                .copied()
                .map(|flow| (flow, 1.0))
                .collect::<Vec<_>>();
            model.add_row(1.0, 1.0, &terms);
        }
        for block in 0..block_count {
            for role in 0..columns_per_block {
                model.add_row(
                    f64::NEG_INFINITY,
                    0.0,
                    &[(flows[block][role], 1.0), (controllers[block][role], -1.0)],
                );
            }
        }
        let objective = (0..block_count)
            .flat_map(|block| {
                let controllers = &controllers;
                (0..columns_per_block).map(move |role| {
                    let perturb = if perturb_last_block && block + 1 == block_count && role == 0 {
                        1.0
                    } else {
                        0.0
                    };
                    (controllers[block][role], role as f64 + 1.0 + perturb)
                })
            })
            .collect::<Vec<_>>();
        model.set_objective(&objective, Sense::Minimize);
        model
    }

    #[test]
    fn rout_shaped_blocks_yield_four_adjacent_sixty_six_bit_swaps() {
        let model = repeated_single_node_blocks(5, 63, 3, false);
        let projection = project_network_design(&model, None).expect("five network blocks");
        assert_eq!(projection.components.len(), 5);
        assert_eq!(projection.master.num_cols(), 5 * 63);

        let families = projection.ordered_interchangeable_block_families(None);
        assert_eq!(families.len(), 1);
        assert_eq!(families[0].len(), 5);
        assert!(families[0].iter().all(|block| block.len() == 63));

        let candidates = projection.adjacent_block_swap_candidates(None);
        assert_eq!(candidates.len(), 4);
        assert!(candidates.iter().all(|candidate| candidate.len() == 2 * 63));

        let plan = crate::pb_translate::translate(&projection.master, None)
            .expect("bounded network master translates exactly");
        assert_eq!(plan.num_vars, 5 * 66);
        let blocks = plan
            .lift_model_column_blocks_to_pb(&families[0])
            .expect("complete ordered network blocks lift through radix bits");
        assert_eq!(blocks.len(), 5);
        assert!(blocks.iter().all(|block| block.len() == 66));
        assert_eq!(
            blocks.iter().flatten().copied().collect::<BTreeSet<_>>(),
            (1..=5 * 66).collect()
        );
        let lifted = candidates
            .iter()
            .map(|candidate| {
                plan.lift_model_column_permutation_to_pb(candidate)
                    .expect("adjacent master block swap lifts through radix bits")
            })
            .collect::<Vec<_>>();
        assert_eq!(lifted.len(), 4);
        assert!(lifted.iter().all(|candidate| candidate.len() == 2 * 66));
    }

    #[test]
    fn nonmatching_network_blocks_do_not_yield_a_swap_candidate() {
        let model = repeated_single_node_blocks(2, 4, 1, true);
        let projection = project_network_design(&model, None).expect("two network blocks");
        assert_eq!(projection.components.len(), 2);
        assert!(projection
            .ordered_interchangeable_block_families(None)
            .is_empty());
        assert!(projection.adjacent_block_swap_candidates(None).is_empty());
    }

    #[test]
    fn many_tiny_components_decline_block_candidates_at_the_component_cap() {
        let block_count = MAX_BLOCK_SYMMETRY_COMPONENTS + 1;
        let model = repeated_single_node_blocks(block_count, 1, 0, false);
        let projection = project_network_design(&model, None).expect("many tiny network blocks");
        assert_eq!(projection.components.len(), block_count);
        assert!(projection
            .ordered_interchangeable_block_families(None)
            .is_empty());
        assert!(projection.adjacent_block_swap_candidates(None).is_empty());
    }

    #[test]
    fn expired_deadline_declines_block_candidates_atomically() {
        let model = repeated_single_node_blocks(5, 4, 1, false);
        let projection = project_network_design(&model, None).expect("five network blocks");
        assert!(projection
            .ordered_interchangeable_block_families(Some(Instant::now()))
            .is_empty());
        assert!(projection
            .adjacent_block_swap_candidates(Some(Instant::now()))
            .is_empty());
    }

    struct TinyFixture {
        model: Model,
        binary: [Col; 3],
        load: Col,
        objective: Col,
        flows: [Col; 3],
        capacities: [i64; 3],
        rhs: [i64; 2],
    }

    /// Two balance nodes and an implicit exterior node:
    /// exterior --e0--> n0 --e1--> n1 --e2--> exterior.
    fn tiny_fixture(capacities: [i64; 3], rhs: [i64; 2]) -> TinyFixture {
        let mut model = Model::new();
        let e0 = model.add_col(0.0, f64::INFINITY);
        let e1 = model.add_col(0.0, f64::INFINITY);
        let e2 = model.add_col(0.0, f64::INFINITY);
        let objective = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let y0 = model.add_binary_col();
        let y1 = model.add_binary_col();
        let y2 = model.add_binary_col();
        let load = model.add_int_col(0.0, 2.0);

        // Objective singleton: w + 3*y0 - 2*y2 + load = 19.
        model.add_row(
            19.0,
            19.0,
            &[(objective, 1.0), (y0, 3.0), (y2, -2.0), (load, 1.0)],
        );
        model.set_objective(&[(objective, 1.0)], Sense::Minimize);

        // A pure-master row exercises verbatim row transfer.
        model.add_row(f64::NEG_INFINITY, 2.0, &[(y0, 1.0), (y1, 1.0), (y2, 1.0)]);
        model.add_row(
            rhs[0] as f64,
            rhs[0] as f64,
            &[(e0, 1.0), (e1, -1.0), (load, 1.0)],
        );
        model.add_row(
            rhs[1] as f64,
            rhs[1] as f64,
            &[(e1, 1.0), (e2, -1.0), (load, -1.0)],
        );
        for ((flow, controller), capacity) in
            [(e0, y0), (e1, y1), (e2, y2)].into_iter().zip(capacities)
        {
            model.add_row(
                f64::NEG_INFINITY,
                0.0,
                &[(flow, 1.0), (controller, -(capacity as f64))],
            );
        }
        TinyFixture {
            model,
            binary: [y0, y1, y2],
            load,
            objective,
            flows: [e0, e1, e2],
            capacities,
            rhs,
        }
    }

    fn master_point(_fixture: &TinyFixture, bits: usize, load: i64) -> Vec<BigRational> {
        let mut values = Vec::new();
        for bit in 0..3 {
            values.push(br(i64::from(bits & (1 << bit) != 0)));
        }
        values.push(br(load));
        assert_eq!(values.len(), 4);
        values
    }

    fn exact_completion(fixture: &TinyFixture, bits: usize, load: i64) -> Option<[i64; 3]> {
        let caps: [i64; 3] =
            std::array::from_fn(|arc| fixture.capacities[arc] * i64::from(bits & (1 << arc) != 0));
        for e0 in 0..=caps[0] {
            for e1 in 0..=caps[1] {
                for e2 in 0..=caps[2] {
                    if e0 - e1 + load == fixture.rhs[0] && e1 - e2 - load == fixture.rhs[1] {
                        return Some([e0, e1, e2]);
                    }
                }
            }
        }
        None
    }

    #[derive(Clone, Copy, Debug)]
    enum TestBalance {
        Equality,
        Lower,
        Upper,
    }

    fn add_test_balance(model: &mut Model, kind: TestBalance, rhs: i64, terms: &[(Col, f64)]) {
        let (lb, ub) = match kind {
            TestBalance::Equality => (rhs as f64, rhs as f64),
            TestBalance::Lower => (rhs as f64, f64::INFINITY),
            TestBalance::Upper => (f64::NEG_INFINITY, rhs as f64),
        };
        model.add_row(lb, ub, terms);
    }

    fn test_balance_holds(kind: TestBalance, lhs: i64, rhs: i64) -> bool {
        match kind {
            TestBalance::Equality => lhs == rhs,
            TestBalance::Lower => lhs >= rhs,
            TestBalance::Upper => lhs <= rhs,
        }
    }

    fn one_sided_fixture(
        capacities: [i64; 3],
        rhs: [i64; 2],
        kinds: [TestBalance; 2],
    ) -> (Model, [Col; 3], [Col; 3]) {
        let mut model = Model::new();
        let e0 = model.add_col(0.0, f64::INFINITY);
        let e1 = model.add_col(0.0, f64::INFINITY);
        let e2 = model.add_col(0.0, f64::INFINITY);
        let y0 = model.add_binary_col();
        let y1 = model.add_binary_col();
        let y2 = model.add_binary_col();
        model.set_objective(&[(y0, 1.0), (y1, 2.0), (y2, 3.0)], Sense::Minimize);
        add_test_balance(&mut model, kinds[0], rhs[0], &[(e0, 1.0), (e1, -1.0)]);
        add_test_balance(&mut model, kinds[1], rhs[1], &[(e1, 1.0), (e2, -1.0)]);
        for ((flow, controller), capacity) in
            [(e0, y0), (e1, y1), (e2, y2)].into_iter().zip(capacities)
        {
            model.add_row(
                f64::NEG_INFINITY,
                0.0,
                &[(flow, 1.0), (controller, -(capacity as f64))],
            );
        }
        (model, [e0, e1, e2], [y0, y1, y2])
    }

    fn one_sided_completion_exists(
        capacities: [i64; 3],
        rhs: [i64; 2],
        kinds: [TestBalance; 2],
        bits: usize,
    ) -> bool {
        let caps: [i64; 3] =
            std::array::from_fn(|arc| capacities[arc] * i64::from(bits & (1 << arc) != 0));
        for e0 in 0..=caps[0] {
            for e1 in 0..=caps[1] {
                for e2 in 0..=caps[2] {
                    if test_balance_holds(kinds[0], e0 - e1, rhs[0])
                        && test_balance_holds(kinds[1], e1 - e2, rhs[1])
                    {
                        return true;
                    }
                }
            }
        }
        false
    }

    #[test]
    fn hoffman_master_matches_exhaustive_exact_flow_enumeration() {
        // Several independently projected tiny networks; for each, exhaust all
        // 8 binary designs, all three general-integer values, and every integer
        // flow in the exact capacity box.  Incidence TU makes this enumeration
        // an exact rational-feasibility oracle for these integral fixtures.
        for capacities in [[1, 1, 1], [2, 1, 2], [2, 3, 1], [3, 2, 3]] {
            for rhs in [[0, 0], [1, -1], [2, 0], [-1, 1]] {
                let fixture = tiny_fixture(capacities, rhs);
                let projection =
                    project_network_design(&fixture.model, None).expect("network projection");
                assert_eq!(projection.components.len(), 1);
                assert_eq!(projection.components[0].balance_rows.len(), 2);
                assert_eq!(projection.hoffman_rows, 6); // 2*(2^2-1), full set included
                for bits in 0usize..8 {
                    for load in 0i64..=2 {
                        let master = master_point(&fixture, bits, load);
                        let projected_feasible = projection.master.check_point(&master).is_ok();
                        let pure_master_feasible = bits.count_ones() <= 2;
                        let completion = exact_completion(&fixture, bits, load);
                        assert_eq!(
                            projected_feasible,
                            pure_master_feasible && completion.is_some(),
                            "capacities={capacities:?} rhs={rhs:?} bits={bits:03b} load={load}"
                        );
                        if projected_feasible {
                            completion.expect("equivalent exact completion");
                            let original = projection
                                .complete_exact(&fixture.model, &master, None)
                                .expect("exact rational network completion");
                            fixture
                                .model
                                .check_point(&original)
                                .expect("reconstructed original point");
                            assert_eq!(
                                original[fixture.objective.index()],
                                br(19) - br(3) * &original[fixture.binary[0].index()]
                                    + br(2) * &original[fixture.binary[2].index()]
                                    - &original[fixture.load.index()]
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn lazy_mincut_matches_exhaustive_exact_flow_enumeration() {
        // Differentially validate both outcomes of lazy separation.  Every
        // feasible design must lift to an original point; every infeasible
        // design must produce a reconstructed row that rejects that exact
        // design after installation.
        for capacities in [[1, 1, 1], [2, 1, 2], [2, 3, 1], [3, 2, 3]] {
            for rhs in [[0, 0], [1, -1], [2, 0], [-1, 1]] {
                let fixture = tiny_fixture(capacities, rhs);
                for bits in 0usize..8 {
                    for load in 0i64..=2 {
                        let mut projection = project_network_design_lazy(&fixture.model, None)
                            .expect("lazy network projection");
                        assert_eq!(projection.hoffman_rows, 0);
                        assert!(!projection.components[0].retained_flows);
                        let master = master_point(&fixture, bits, load);
                        let pure_master_feasible = bits.count_ones() <= 2;
                        let completion = exact_completion(&fixture, bits, load);
                        if !pure_master_feasible {
                            assert!(projection.master.check_point(&master).is_err());
                            continue;
                        }
                        match projection
                            .separate_exact(&fixture.model, &master, None)
                            .expect("exact lazy separation")
                        {
                            NetworkDesignSeparation::Feasible(original) => {
                                assert!(completion.is_some(),
                                    "false feasible: capacities={capacities:?} rhs={rhs:?} bits={bits:03b} load={load}");
                                fixture
                                    .model
                                    .check_point(&original)
                                    .expect("lazy completion rechecks");
                            }
                            NetworkDesignSeparation::Violated(cut) => {
                                assert!(completion.is_none(),
                                    "false cut: capacities={capacities:?} rhs={rhs:?} bits={bits:03b} load={load}");
                                projection
                                    .install_cut(cut, &master, None)
                                    .expect("licensed violated cut installs");
                                assert!(projection.master.check_point(&master).is_err());
                                assert_eq!(projection.hoffman_rows, 1);
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn lazy_residual_cut_uses_the_correct_directed_hoffman_side() {
        for (incidence, rhs, expected_direction) in [
            (1.0, 1.0, HoffmanDirection::Incoming),
            (-1.0, -1.0, HoffmanDirection::Outgoing),
        ] {
            let mut model = Model::new();
            let flow = model.add_col(0.0, f64::INFINITY);
            let enabled = model.add_binary_col();
            model.add_row(rhs, rhs, &[(flow, incidence)]);
            model.add_row(f64::NEG_INFINITY, 0.0, &[(flow, 1.0), (enabled, -1.0)]);

            let mut projection =
                project_network_design_lazy(&model, None).expect("directed lazy projection");
            let disabled = [br(0)];
            let NetworkDesignSeparation::Violated(cut) = projection
                .separate_exact(&model, &disabled, None)
                .expect("disabled arc has an exact residual cut")
            else {
                panic!("disabled unit arc cannot complete")
            };
            assert_eq!(cut.direction, expected_direction);
            assert_eq!(cut.selected_balances.len(), 1);
            assert_eq!(cut.terms, vec![(enabled.index(), br(1))]);
            assert_eq!(cut.rhs, br(1));
            projection
                .install_cut(cut, &disabled, None)
                .expect("directed Hoffman row installs");
            assert!(projection.master.check_point(&disabled).is_err());
        }
    }

    #[test]
    fn disconnected_one_node_networks_keep_only_their_own_arcs() {
        let mut model = Model::new();
        let mut flows = Vec::new();
        for demand in 1..=3 {
            let flow = model.add_col(0.0, f64::INFINITY);
            let enabled = model.add_binary_col();
            model.add_row(demand as f64, demand as f64, &[(flow, 1.0)]);
            model.add_row(
                f64::NEG_INFINITY,
                0.0,
                &[(flow, 1.0), (enabled, -(demand as f64))],
            );
            flows.push(flow.index());
        }

        let projection =
            project_network_design_lazy(&model, None).expect("disconnected lazy projection");
        assert_eq!(projection.components.len(), 3);
        for (component, flow) in projection.components.iter().zip(flows) {
            assert_eq!(component.balance_rows.len(), 1);
            assert_eq!(component.flow_columns, vec![flow]);
        }
    }

    #[test]
    fn medium_lazy_network_seeds_singletons_and_full_component_only() {
        const NODES: usize = MIN_LAZY_SEED_COMPONENT_NODES;
        let mut model = Model::new();
        let flows = (0..NODES - 1)
            .map(|_| model.add_col(0.0, f64::INFINITY))
            .collect::<Vec<_>>();
        let enabled = (0..flows.len())
            .map(|_| model.add_binary_col())
            .collect::<Vec<_>>();
        for node in 0..NODES {
            let mut terms = Vec::with_capacity(2);
            if node > 0 {
                terms.push((flows[node - 1], 1.0));
            }
            if node + 1 < NODES {
                terms.push((flows[node], -1.0));
            }
            model.add_row(0.0, 0.0, &terms);
        }
        for (&flow, &controller) in flows.iter().zip(&enabled) {
            model.add_row(f64::NEG_INFINITY, 0.0, &[(flow, 1.0), (controller, -1.0)]);
        }

        let projection = project_network_design_lazy(&model, None).expect("seeded lazy projection");
        assert_eq!(projection.components.len(), 1);
        // Two directed sides for every singleton and for the full component;
        // no exponential intermediate subsets are materialized.
        assert_eq!(projection.hoffman_rows, 2 * (NODES + 1));
        assert_eq!(projection.master.num_rows(), 2 * (NODES + 1));
        let disabled = vec![br(0); enabled.len()];
        projection
            .master
            .check_point(&disabled)
            .expect("seed rows preserve the zero-flow design");
        assert!(matches!(
            projection
                .separate_exact(&model, &disabled, None)
                .expect("seeded point separates exactly"),
            NetworkDesignSeparation::Feasible(_)
        ));
    }

    #[test]
    fn one_sided_hoffman_master_matches_exhaustive_flow_enumeration() {
        // Exercise every equality/lower/upper pairing.  Integral incidence is
        // TU, so exhaustive integer flow enumeration is also an exact rational
        // feasibility oracle.  This catches both exterior-slack directions:
        // lower rows add an unbounded outgoing arc; upper rows add incoming.
        let kinds = [
            TestBalance::Equality,
            TestBalance::Lower,
            TestBalance::Upper,
        ];
        for first in kinds {
            for second in kinds {
                for capacities in [[1, 2, 1], [2, 1, 2]] {
                    for rhs in [[-1, 0], [0, 0], [1, -1], [1, 1]] {
                        let pair = [first, second];
                        let (model, _, _) = one_sided_fixture(capacities, rhs, pair);
                        let projection =
                            project_network_design(&model, None).expect("one-sided projection");
                        for bits in 0usize..8 {
                            let master = vec![
                                br(i64::from(bits & 1 != 0)),
                                br(i64::from(bits & 2 != 0)),
                                br(i64::from(bits & 4 != 0)),
                            ];
                            let expected = one_sided_completion_exists(capacities, rhs, pair, bits);
                            let projected = projection.master.check_point(&master).is_ok();
                            assert_eq!(
                                projected, expected,
                                "capacities={capacities:?} rhs={rhs:?} kinds={pair:?} bits={bits:03b}"
                            );
                            if projected {
                                let completed = projection
                                    .complete_exact(&model, &master, None)
                                    .expect("one-sided exact completion");
                                model
                                    .check_point(&completed)
                                    .expect("one-sided original point");
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn lazy_mincut_handles_every_one_sided_balance_orientation() {
        let kinds = [
            TestBalance::Equality,
            TestBalance::Lower,
            TestBalance::Upper,
        ];
        for first in kinds {
            for second in kinds {
                for capacities in [[1, 2, 1], [2, 1, 2]] {
                    for rhs in [[-1, 0], [0, 0], [1, -1], [1, 1]] {
                        let pair = [first, second];
                        let (model, _, _) = one_sided_fixture(capacities, rhs, pair);
                        for bits in 0usize..8 {
                            let mut projection = project_network_design_lazy(&model, None)
                                .expect("lazy one-sided projection");
                            let point = (0..3)
                                .map(|bit| br(i64::from(bits & (1 << bit) != 0)))
                                .collect::<Vec<_>>();
                            let expected = one_sided_completion_exists(capacities, rhs, pair, bits);
                            match projection
                                .separate_exact(&model, &point, None)
                                .expect("one-sided lazy separation")
                            {
                                NetworkDesignSeparation::Feasible(original) => {
                                    assert!(expected,
                                        "false feasible: kinds={pair:?} capacities={capacities:?} rhs={rhs:?} bits={bits:03b}");
                                    model.check_point(&original).expect("completion rechecks");
                                }
                                NetworkDesignSeparation::Violated(cut) => {
                                    assert!(!expected,
                                        "false cut: kinds={pair:?} capacities={capacities:?} rhs={rhs:?} bits={bits:03b}");
                                    projection
                                        .install_cut(cut, &point, None)
                                        .expect("one-sided cut installs");
                                    assert!(projection.master.check_point(&point).is_err());
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn fractional_supplies_capacities_and_exterior_arcs_complete_exactly() {
        // exterior --e0--> n0 --e1--> n1 --e2--> exterior.  Twelfths form
        // an exhaustive exact oracle: capacities are 10/12, 8/12, 6/12 and
        // node requirements are 4/12, 2/12.
        let mut model = Model::new();
        let e0 = model.add_col(0.0, f64::INFINITY);
        let e1 = model.add_col(0.0, f64::INFINITY);
        let e2 = model.add_col(0.0, f64::INFINITY);
        let objective = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let y0 = model.add_binary_col();
        let y1 = model.add_binary_col();
        let y2 = model.add_binary_col();
        model.add_row(0.0, 0.0, &[(objective, 1.0)]);
        model.set_objective(&[(objective, 1.0)], Sense::Minimize);

        let first = model.add_row(1.0 / 3.0, 1.0 / 3.0, &[(e0, 1.0), (e1, -1.0)]);
        let one_third = BigRational::new(1.into(), 3.into());
        model.record_inexact_row_bound(first, true, one_third.clone());
        model.record_inexact_row_bound(first, false, one_third);
        let second = model.add_row(1.0 / 6.0, 1.0 / 6.0, &[(e1, 1.0), (e2, -1.0)]);
        let one_sixth = BigRational::new(1.into(), 6.into());
        model.record_inexact_row_bound(second, true, one_sixth.clone());
        model.record_inexact_row_bound(second, false, one_sixth);
        for (flow, controller, numerator) in [(e0, y0, 5), (e1, y1, 4), (e2, y2, 3)] {
            let capacity = BigRational::new(numerator.into(), 6.into());
            let row = model.add_row(
                f64::NEG_INFINITY,
                0.0,
                &[
                    (flow, 1.0),
                    (controller, -capacity.to_f64().expect("small rational")),
                ],
            );
            model.record_inexact_row_coeff(row, controller.0, -capacity);
        }

        let projection = project_network_design(&model, None).expect("fractional projection");
        assert_eq!(projection.hoffman_rows, 6);
        for bits in 0usize..8 {
            let master = vec![
                br(i64::from(bits & 1 != 0)),
                br(i64::from(bits & 2 != 0)),
                br(i64::from(bits & 4 != 0)),
            ];
            let mut enumerated = false;
            // Spell the bit/capacity association out; the loop is deliberately
            // finite and exact, not a floating tolerance check.
            let caps = [
                10 * i64::from(bits & 1 != 0),
                8 * i64::from(bits & 2 != 0),
                6 * i64::from(bits & 4 != 0),
            ];
            'flows: for e0_value in 0..=caps[0] {
                for e1_value in 0..=caps[1] {
                    for e2_value in 0..=caps[2] {
                        if e0_value - e1_value == 4 && e1_value - e2_value == 2 {
                            enumerated = true;
                            break 'flows;
                        }
                    }
                }
            }
            let projected = projection.master.check_point(&master).is_ok();
            assert_eq!(projected, enumerated, "bits={bits:03b}");
            if projected {
                let completed = projection
                    .complete_exact(&model, &master, None)
                    .expect("fractional exact completion");
                model
                    .check_point(&completed)
                    .expect("fractional completed original point");
                assert_eq!(
                    &completed[e0.index()] - &completed[e1.index()],
                    br(1) / br(3)
                );
                assert_eq!(
                    &completed[e1.index()] - &completed[e2.index()],
                    br(1) / br(6)
                );
            }
        }
    }

    #[test]
    fn full_subset_keeps_one_ended_arc_capacity() {
        let mut model = Model::new();
        let incoming = model.add_col(0.0, f64::INFINITY);
        let objective = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let enabled = model.add_binary_col();
        model.add_row(0.0, 0.0, &[(objective, 1.0)]);
        model.set_objective(&[(objective, 1.0)], Sense::Minimize);
        model.add_row(1.0, 1.0, &[(incoming, 1.0)]);
        model.add_row(f64::NEG_INFINITY, 0.0, &[(incoming, 1.0), (enabled, -1.0)]);

        let projection = project_network_design(&model, None).expect("one-node network");
        assert_eq!(projection.hoffman_rows, 2);
        assert!(projection.master.check_point(&[br(0)]).is_err());
        assert!(projection.master.check_point(&[br(1)]).is_ok());
        let completed = projection
            .complete_exact(&model, &[br(1)], None)
            .expect("one-ended exact completion");
        assert_eq!(completed[incoming.index()], br(1));
        assert!(matches!(
            projection.complete_exact(&model, &[br(0)], None),
            Err(NetworkDesignCompletionError::InvalidMasterPoint)
        ));
        assert!(matches!(
            projection.complete_exact(&model, &[br(1)], Some(Instant::now())),
            Err(NetworkDesignCompletionError::Deadline)
        ));
    }

    #[test]
    fn bounded_general_integer_can_control_arc_capacity() {
        let mut model = Model::new();
        let incoming = model.add_col(0.0, f64::INFINITY);
        let objective = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let installations = model.add_int_col(0.0, 2.0);
        model.add_row(0.0, 0.0, &[(objective, 1.0)]);
        model.set_objective(&[(objective, 1.0)], Sense::Minimize);
        model.add_row(3.0, 3.0, &[(incoming, 1.0)]);
        model.add_row(
            f64::NEG_INFINITY,
            0.0,
            &[(incoming, 1.0), (installations, -2.0)],
        );

        let projection = project_network_design(&model, None).expect("integer VUB controller");
        assert_eq!(projection.hoffman_rows, 2);
        assert_eq!(projection.master.col_kind(Col(0)), ColKind::Integer);
        assert!(projection.master.check_point(&[br(0)]).is_err());
        assert!(projection.master.check_point(&[br(1)]).is_err());
        assert!(projection.master.check_point(&[br(2)]).is_ok());
        let completed = projection
            .complete_exact(&model, &[br(2)], None)
            .expect("general-integer capacity completion");
        assert_eq!(completed[incoming.index()], br(3));
    }

    #[test]
    fn integral_master_objective_needs_no_continuous_singleton() {
        let mut model = Model::new();
        let incoming = model.add_col(0.0, f64::INFINITY);
        let enabled = model.add_binary_col();
        model.add_row(1.0, 1.0, &[(incoming, 1.0)]);
        model.add_row(f64::NEG_INFINITY, 0.0, &[(incoming, 1.0), (enabled, -2.0)]);
        model.set_objective(&[(enabled, 5.0)], Sense::Maximize);
        model.set_objective_offset(1.0 / 3.0);
        model.record_inexact_obj_offset(BigRational::new(1.into(), 3.into()));

        let projection = project_network_design(&model, None).expect("master-only objective");
        assert!(projection.objective_lift.is_none());
        assert_eq!(projection.master.sense(), Sense::Maximize);
        assert_eq!(
            projection.master.objective_value_at(&[br(1)]),
            br(5) + BigRational::new(1.into(), 3.into())
        );
        let completed = projection
            .complete_exact(&model, &[br(1)], None)
            .expect("master-objective completion");
        assert_eq!(completed[incoming.index()], br(1));
        assert_eq!(
            model.objective_value_at(&completed),
            projection.master.objective_value_at(&[br(1)])
        );
    }

    #[test]
    fn affine_multi_controller_capacity_projects_exactly() {
        for demand in 0i64..=6 {
            let mut model = Model::new();
            let incoming = model.add_col(0.0, f64::INFINITY);
            let small = model.add_binary_col();
            let large = model.add_binary_col();
            model.add_row(demand as f64, demand as f64, &[(incoming, 1.0)]);
            model.add_row(
                f64::NEG_INFINITY,
                0.0,
                &[(incoming, 1.0), (small, -2.0), (large, -4.0)],
            );
            model.add_row(f64::NEG_INFINITY, 1.0, &[(small, 1.0), (large, 1.0)]);
            model.set_objective(&[(small, 1.0), (large, 2.0)], Sense::Minimize);

            let projection = project_network_design(&model, None).expect("multi-controller VUB");
            for bits in 0usize..4 {
                let master = vec![br(i64::from(bits & 1 != 0)), br(i64::from(bits & 2 != 0))];
                let expected = bits.count_ones() <= 1
                    && demand <= 2 * i64::from(bits & 1 != 0) + 4 * i64::from(bits & 2 != 0);
                assert_eq!(
                    projection.master.check_point(&master).is_ok(),
                    expected,
                    "demand={demand} bits={bits:02b}"
                );
                if expected {
                    let completed = projection
                        .complete_exact(&model, &master, None)
                        .expect("multi-controller completion");
                    assert_eq!(completed[incoming.index()], br(demand));
                }
            }
        }
    }

    #[test]
    fn exact_side_store_survives_objective_and_cut_projection() {
        let mut model = Model::new();
        let flow = model.add_col(0.0, f64::INFINITY);
        let objective = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let enabled = model.add_binary_col();
        let definition = model.add_row(0.1, 0.1, &[(objective, 1.0), (enabled, 0.1)]);
        model.record_inexact_row_bound(definition, true, BigRational::new(1.into(), 3.into()));
        model.record_inexact_row_bound(definition, false, BigRational::new(1.into(), 3.into()));
        model.record_inexact_row_coeff(definition, enabled.0, BigRational::new(1.into(), 7.into()));
        model.set_objective(&[(objective, 1.0)], Sense::Maximize);
        model.set_objective_offset(5.0 / 11.0);
        model.record_inexact_obj_offset(BigRational::new(5.into(), 11.into()));
        model.add_row(0.0, 0.0, &[(flow, 1.0)]);
        let vub = model.add_row(f64::NEG_INFINITY, 0.0, &[(flow, 1.0), (enabled, -0.1)]);
        model.record_inexact_row_coeff(vub, enabled.0, BigRational::new((-2).into(), 3.into()));

        let projection = project_network_design(&model, None).expect("side-store projection");
        let point = [br(1)];
        let partial = projection.lift_partial(&point).expect("lift");
        assert_eq!(
            partial[objective.index()],
            Some(BigRational::new(4.into(), 21.into()))
        );
        assert_eq!(
            projection.master.objective_value_at(&point),
            BigRational::new(4.into(), 21.into()) + BigRational::new(5.into(), 11.into())
        );
        assert_eq!(projection.master.sense(), Sense::Maximize);
        let completed = projection
            .complete_exact(&model, &point, None)
            .expect("side-store completion");
        assert_eq!(
            model.objective_value_at(&completed),
            projection.master.objective_value_at(&point)
        );
        // One-node full-set upper cut has exact capacity 2/3 on `enabled`.
        let cut = projection.master.num_rows() - 2;
        let (terms, lb, _) = projection.master.row(Row(cut as u32));
        let &(column, advice) = terms.first().expect("capacity term");
        assert_eq!(
            projection.master.row_coeff_exact(cut, column, advice),
            BigRational::new(2.into(), 3.into())
        );
        assert_eq!(projection.master.row_lb_exact(cut, lb), Some(br(0)));
    }

    #[test]
    fn malformed_networks_decline_fail_closed() {
        let mut fixture = tiny_fixture([1, 1, 1], [0, 0]);
        // Add a second VUB for one arc: no ambiguous capacity may be selected.
        fixture.model.add_row(
            f64::NEG_INFINITY,
            0.0,
            &[(fixture.flows[0], 1.0), (fixture.binary[0], -1.0)],
        );
        assert!(matches!(
            project_network_design(&fixture.model, None),
            Err(NetworkDesignDecline::FlowVubCount { .. })
        ));

        let mut fixture = tiny_fixture([1, 1, 1], [0, 0]);
        let bad = fixture.model.add_row(
            0.0,
            0.0,
            &[(fixture.flows[0], 2.0), (fixture.binary[0], 1.0)],
        );
        assert!(matches!(
            project_network_design(&fixture.model, None),
            Err(NetworkDesignDecline::NonIncidenceCoefficient { row }) if row == bad.index()
        ));
        assert!(matches!(
            project_network_design(&fixture.model, Some(Instant::now())),
            Err(NetworkDesignDecline::Deadline)
        ));

        // A finite range is not an unbounded exterior slack arc.  Treating it
        // as either a one-sided balance or a VUB would drop one exact side.
        let mut ranged = Model::new();
        let flow = ranged.add_col(0.0, f64::INFINITY);
        let enabled = ranged.add_binary_col();
        ranged.add_row(0.0, 1.0, &[(flow, 1.0)]);
        ranged.add_row(f64::NEG_INFINITY, 0.0, &[(flow, 1.0), (enabled, -1.0)]);
        assert!(matches!(
            project_network_design(&ranged, None),
            Err(NetworkDesignDecline::UnsupportedBalanceBounds { .. })
        ));

        // Continuous costs are accepted only through one exact singleton
        // definition.  Multiple costed continuous columns and a costed flow
        // appearing in network rows both decline rather than losing cost.
        let mut two_costs = Model::new();
        let first = two_costs.add_col(0.0, f64::INFINITY);
        let second = two_costs.add_col(0.0, f64::INFINITY);
        let controller = two_costs.add_binary_col();
        two_costs.add_row(0.0, 0.0, &[(first, 1.0), (second, -1.0)]);
        two_costs.add_row(f64::NEG_INFINITY, 0.0, &[(first, 1.0), (controller, -1.0)]);
        two_costs.add_row(f64::NEG_INFINITY, 0.0, &[(second, 1.0), (controller, -1.0)]);
        two_costs.set_objective(&[(first, 1.0), (second, 1.0)], Sense::Minimize);
        assert!(matches!(
            project_network_design(&two_costs, None),
            Err(NetworkDesignDecline::ObjectiveSingletonCount { found: 2 })
        ));

        // Its ONLY continuous column is the costed one, so the cheap
        // column-only ownership test decides first: after filtering the
        // objective singleton out, `flow_columns` is empty. This is a real,
        // distinct fail-closed case and is kept as one — but it can NOT stand
        // in for the objective-occurrence census, which is downstream of
        // `exact_rows` and therefore never reached from here.
        let mut no_flow = Model::new();
        let only = no_flow.add_col(0.0, f64::INFINITY);
        let controller = no_flow.add_binary_col();
        no_flow.add_row(1.0, 1.0, &[(only, 1.0)]);
        no_flow.add_row(f64::NEG_INFINITY, 0.0, &[(only, 1.0), (controller, -1.0)]);
        no_flow.set_objective(&[(only, 1.0)], Sense::Minimize);
        assert!(matches!(
            project_network_design(&no_flow, None),
            Err(NetworkDesignDecline::NoFlowColumns)
        ));

        // THE CENSUS GUARD. A second, UNCOSTED continuous column keeps
        // `flow_columns` non-empty so the projection reaches the exact rows,
        // where the costed column is found in TWO of them. Without this fixture
        // `ObjectiveNotSingleton` is reachable from no test in the suite — and
        // it is the guard that stops the network lane silently DROPPING an
        // objective cost term whose column is defined by more than one row,
        // which returns a wrong optimum with a straight face.
        let mut costed_flow = Model::new();
        let cost = costed_flow.add_col(0.0, f64::INFINITY);
        let flow = costed_flow.add_col(0.0, f64::INFINITY);
        let controller = costed_flow.add_binary_col();
        costed_flow.add_row(1.0, 1.0, &[(cost, 1.0)]);
        costed_flow.add_row(f64::NEG_INFINITY, 0.0, &[(cost, 1.0), (controller, -1.0)]);
        costed_flow.add_row(f64::NEG_INFINITY, 0.0, &[(flow, 1.0), (controller, -1.0)]);
        costed_flow.set_objective(&[(cost, 1.0)], Sense::Minimize);
        assert!(
            matches!(
                project_network_design(&costed_flow, None),
                Err(NetworkDesignDecline::ObjectiveNotSingleton {
                    column,
                    occurrences: 2
                }) if column == cost.index()
            ),
            "the objective-occurrence census must own this decline, not an \
             earlier column-shape test: {:?}",
            project_network_design(&costed_flow, None).err()
        );
    }

    #[test]
    fn oversized_integral_network_uses_tu_retained_flow_master() {
        let mut model = Model::new();
        let flows: Vec<Col> = (0..MAX_COMPONENT_NODES)
            .map(|_| model.add_col(0.0, f64::INFINITY))
            .collect();
        let objective = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let enabled = model.add_binary_col();
        model.add_row(0.0, 0.0, &[(objective, 1.0)]);
        model.set_objective(&[(objective, 1.0)], Sense::Minimize);
        for node in 0..=MAX_COMPONENT_NODES {
            let mut terms = Vec::with_capacity(2);
            if node > 0 {
                terms.push((flows[node - 1], 1.0));
            }
            if node < MAX_COMPONENT_NODES {
                terms.push((flows[node], -1.0));
            }
            model.add_row(0.0, 0.0, &terms);
        }
        for flow in flows {
            model.add_row(f64::NEG_INFINITY, 0.0, &[(flow, 1.0), (enabled, -1.0)]);
        }

        let projection = project_network_design(&model, None).expect("TU retained-flow master");
        assert_eq!(projection.components.len(), 1);
        assert!(projection.components[0].retained_flows);
        assert_eq!(projection.hoffman_rows, 0);
        assert_eq!(projection.master.num_cols(), 1 + MAX_COMPONENT_NODES);
        let point = vec![br(0); projection.master.num_cols()];
        projection
            .master
            .check_point(&point)
            .expect("retained zero-flow point");
        let completed = projection
            .complete_exact(&model, &point, None)
            .expect("retained-flow lift");
        model
            .check_point(&completed)
            .expect("retained original recheck");
    }

    #[test]
    fn dense_small_integral_network_prefers_compact_tu_master() {
        // Fourteen arcs over fifteen nodes already put exhaustive subset/arc
        // scans above the compact-master threshold, even though the component
        // remains below the hard 16-node Hoffman correctness cap.
        const NODES: usize = 15;
        let mut model = Model::new();
        let flows: Vec<Col> = (0..NODES - 1)
            .map(|_| model.add_col(0.0, f64::INFINITY))
            .collect();
        let objective = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let enabled = model.add_binary_col();
        model.add_row(0.0, 0.0, &[(objective, 1.0)]);
        model.set_objective(&[(objective, 1.0)], Sense::Minimize);
        for node in 0..NODES {
            let mut terms = Vec::with_capacity(2);
            if node > 0 {
                terms.push((flows[node - 1], 1.0));
            }
            if node + 1 < NODES {
                terms.push((flows[node], -1.0));
            }
            model.add_row(0.0, 0.0, &terms);
        }
        for flow in flows {
            model.add_row(f64::NEG_INFINITY, 0.0, &[(flow, 1.0), (enabled, -1.0)]);
        }

        let projection = project_network_design(&model, None).expect("compact TU master");
        assert_eq!(projection.components.len(), 1);
        assert!(projection.components[0].retained_flows);
        assert_eq!(projection.hoffman_rows, 0);
        assert_eq!(projection.master.num_cols(), 1 + (NODES - 1));
        let point = vec![br(0); projection.master.num_cols()];
        let completed = projection
            .complete_exact(&model, &point, None)
            .expect("retained-flow lift");
        model
            .check_point(&completed)
            .expect("completed original point");
    }

    #[test]
    fn oversized_network_without_integral_tu_data_declines() {
        let mut model = Model::new();
        let flows: Vec<Col> = (0..MAX_COMPONENT_NODES)
            .map(|_| model.add_col(0.0, f64::INFINITY))
            .collect();
        let enabled = model.add_binary_col();
        for node in 0..=MAX_COMPONENT_NODES {
            let mut terms = Vec::with_capacity(2);
            if node > 0 {
                terms.push((flows[node - 1], 1.0));
            }
            if node < MAX_COMPONENT_NODES {
                terms.push((flows[node], -1.0));
            }
            let row = model.add_row(0.0, 0.0, &terms);
            if node == 0 {
                let half = BigRational::new(1.into(), 2.into());
                model.record_inexact_row_bound(row, true, half.clone());
                model.record_inexact_row_bound(row, false, half);
            }
        }
        for flow in flows {
            model.add_row(f64::NEG_INFINITY, 0.0, &[(flow, 1.0), (enabled, -1.0)]);
        }
        model.set_objective(&[(enabled, 1.0)], Sense::Minimize);

        assert!(matches!(
            project_network_design(&model, None),
            Err(NetworkDesignDecline::NonIntegralRetainedSupply { .. })
        ));
    }
}
