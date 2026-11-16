// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Direct store-hit and fallthrough proposals with independently proved guards.
//! A chain is never split into fresh sparse-lowering allowances or suffix reads.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::term::TermStoreSnapshotStamp;
use ay_frontend::{Context, SourceContextStamp};
use num_traits::ToPrimitive;
use std::sync::Arc;

use super::facts::FactBase;
use super::read_range::{NegativeRange, RangeMiss};
use super::*;

#[derive(Clone, Copy)]
struct Address {
    base: Option<TermId>,
    offset: u128,
    width: u32,
}

#[derive(Clone, Copy)]
struct Store {
    inner: TermId,
    index: TermId,
    value: TermId,
}

#[derive(Clone, Copy)]
pub(super) struct ReadSkip {
    pub(super) index: TermId,
    /// Earlier class images are proposal advice, never skip authority.
    /// Emission explains both original-to-image paths before the read edge.
    pub(super) index_image: TermId,
    pub(super) point_image: TermId,
    /// The actual variable bases whose earlier equality must be proved.
    /// `None` means no base-alias premise; a range miss still requires its
    /// recorded earlier negative-range fact.
    pub(super) bases: Option<(TermId, TermId)>,
    /// An earlier authenticated negative modular-range fact, when required.
    pub(super) range: Option<RangeMiss>,
    /// Exact earlier negative-equality fact, emitted from its original
    /// authored/conjunctive proof. An index is advice, never an assumption.
    pub(super) disequality: Option<usize>,
}

#[derive(Clone, Copy)]
pub(super) enum ReadChainEnd {
    Value,
    Base(TermId),
}

pub(super) struct ReadChainWitness {
    pub(super) end: ReadChainEnd,
    pub(super) index: TermId,
    pub(super) skipped: Vec<ReadSkip>,
}

#[derive(Default)]
pub(super) struct ReadChainState {
    stamp: Option<(SourceContextStamp, TermStoreSnapshotStamp)>,
    arrays: DetHashMap<TermId, Arc<[Store]>>,
    addresses: DetHashMap<TermId, Option<Address>>,
    completed: DetHashSet<TermId>,
    pub(super) witnesses: Vec<ReadChainWitness>,
}

impl ReadChainState {
    pub(super) fn current(&self, context: &Context) -> bool {
        self.stamp.as_ref().is_some_and(|(source, terms)| {
            source == &context.source_context_stamp()
                && terms.is_append_only_prefix_of(&context.terms)
        })
    }

    /// An unused state may be unbound; a retired binding is never ignored.
    pub(super) fn current_or_unbound(&self, context: &Context) -> bool {
        self.current(context)
            || (self.stamp.is_none()
                && self.arrays.is_empty()
                && self.addresses.is_empty()
                && self.completed.is_empty()
                && self.witnesses.is_empty())
    }

    fn bind(&mut self, context: &Context) -> Option<()> {
        if self.stamp.is_none() {
            self.stamp = Some((
                context.source_context_stamp(),
                context.terms.snapshot_stamp(),
            ));
        }
        self.current(context).then_some(())
    }

    // Validate every store, including the suffix behind a hit. The immutable
    // descriptor is syntax, never a cached class relation or a proof.
    fn array(
        &mut self,
        terms: &TermStore,
        array: TermId,
        work: &mut SharedGroundWork,
    ) -> Option<Option<Arc<[Store]>>> {
        if let Some(chain) = self.arrays.get(&array) {
            return Some(Some(Arc::clone(chain)));
        }
        if self.arrays.len() >= MAX_NODES {
            return None;
        }
        let mut cursor = array;
        let mut pending = Vec::new();
        let sort = terms.entry_stamp(array).map(|_| terms.sort(array))?;
        let Sort::Array(shape) = sort else {
            return Some(None);
        };
        loop {
            work.spend(1)?;
            if terms.entry_stamp(cursor).is_none() || terms.sort(cursor) != sort {
                return Some(None);
            }
            if pending.len() >= MAX_NODES {
                return None;
            }
            let TermData::App(Symbol::Named(head), args) = terms.get(cursor) else {
                break;
            };
            if head != "store" {
                break;
            }
            let &[base, at, value] = args.as_slice() else {
                return Some(None);
            };
            if [base, at, value]
                .into_iter()
                .any(|term| terms.entry_stamp(term).is_none())
                || terms.sort(base) != sort
                || terms.sort(at) != &shape.index_sort
                || terms.sort(value) != &shape.element_sort
            {
                return Some(None);
            }
            pending.try_reserve(1).ok()?;
            pending.push(Store {
                inner: base,
                index: at,
                value,
            });
            cursor = base;
        }
        let chain: Arc<[Store]> = pending.into();
        self.arrays.try_reserve(1).ok()?;
        self.arrays.insert(array, Arc::clone(&chain));
        Some(Some(chain))
    }

    fn address(
        &mut self,
        terms: &TermStore,
        term: TermId,
        work: &mut SharedGroundWork,
    ) -> Option<Option<Address>> {
        if let Some(result) = self.addresses.get(&term) {
            return Some(*result);
        }
        if self.addresses.len() >= MAX_NODES {
            return None;
        }
        let result = read_address(terms, term, work)?;
        self.addresses.try_reserve(1).ok()?;
        self.addresses.insert(term, result);
        Some(result)
    }
}

type ClassAddresses = DetHashMap<usize, Vec<(TermId, Address)>>;

/// No interpretation of distinct classes: unequal offsets separate addresses
/// only when their actual bases are identical or already justified equal.
fn separated_bases(
    closure: &GroundClosure,
    address: Address,
    point: Address,
) -> Option<Option<(TermId, TermId)>> {
    if address.width != point.width || address.offset == point.offset {
        return None;
    }
    match (address.base, point.base) {
        (None, None) => Some(None),
        (Some(a), Some(b)) if a == b => Some(None),
        (Some(a), Some(b)) if closure.same_class(a, b) => Some(Some((a, b))),
        _ => None,
    }
}

struct Separation {
    bases: Option<(TermId, TermId)>,
    range: Option<RangeMiss>,
}

fn separated_with_ranges(
    closure: &GroundClosure,
    point: Option<Address>,
    address: Address,
    ranges: &[NegativeRange],
    work: &mut SharedGroundWork,
) -> Option<Option<Separation>> {
    if let Some(bases) = point.and_then(|point| separated_bases(closure, address, point)) {
        return Some(Some(Separation { bases, range: None }));
    }
    for &source in ranges {
        work.spend(1)?;
        if source.width != address.width {
            continue;
        }
        let (offset, bases) = match address.base {
            Some(base) if base == source.base => (address.offset, None),
            Some(base) if closure.same_class(base, source.base) => {
                (address.offset, Some((base, source.base)))
            }
            None => {
                let Some(start) = source.constant_base else {
                    continue;
                };
                let mask = u128::MAX >> (128 - source.width);
                (address.offset.wrapping_sub(start) & mask, None)
            }
            _ => continue,
        };
        if offset < source.length {
            return Some(Some(Separation {
                bases,
                range: Some(RangeMiss { source, offset }),
            }));
        }
    }
    Some(None)
}

impl ReadChainState {
    /// Inspect only this index's actual class, under the existing member cap.
    /// Syntax caches persist; class relations and candidate lists do not.
    fn index_addresses(
        &mut self,
        terms: &TermStore,
        closure: &GroundClosure,
        index: TermId,
        work: &mut SharedGroundWork,
        stop: &dyn Fn() -> bool,
    ) -> Option<Vec<(TermId, Address)>> {
        if closure.nodes().len() > MAX_NODES || stop() {
            return None;
        }
        closure.class(index)?;
        let mut result = Vec::new();
        for term in closure.members(index).take(slice::MAX_MEMBERS_PER_SITE) {
            work.spend(1)?;
            if stop() {
                return None;
            }
            terms.entry_stamp(term)?;
            if !terms
                .sort(term)
                .bitvec_width()
                .is_some_and(|w| (1..=128).contains(&w))
            {
                continue;
            }
            let Some(address) = self.address(terms, term, work)? else {
                continue;
            };
            result.try_reserve(1).ok()?;
            result.push((term, address));
        }
        Some(result)
    }
}

// Deliberately array-free: no fresh word stands in for an unvalidated opaque
// expression. The BB clauses retain these exact variable/literal source terms.
fn read_address(
    terms: &TermStore,
    term: TermId,
    work: &mut SharedGroundWork,
) -> Option<Option<Address>> {
    let Some(width) = terms
        .entry_stamp(term)
        .and_then(|_| terms.sort(term).bitvec_width())
        .filter(|width| (1..=128).contains(width))
    else {
        return Some(None);
    };
    let mask = u128::MAX >> (128 - width);
    let mut cursor = term;
    let mut offset = 0u128;
    loop {
        work.spend(1)?;
        if terms.entry_stamp(cursor).is_none() || terms.sort(cursor).bitvec_width() != Some(width) {
            return Some(None);
        }
        match terms.get(cursor) {
            TermData::Var(..) => {
                return Some(Some(Address {
                    base: Some(cursor),
                    offset,
                    width,
                }))
            }
            TermData::Const(Constant::BitVec { value, .. }) => {
                let Some(value) = value.to_u128() else {
                    return Some(None);
                };
                return Some(Some(Address {
                    base: None,
                    offset: offset.wrapping_add(value) & mask,
                    width,
                }));
            }
            TermData::App(Symbol::Named(head), args)
                if matches!(head.as_str(), "bvadd" | "bvsub") =>
            {
                let &[left, right] = args.as_slice() else {
                    return Some(None);
                };
                if [left, right].into_iter().any(|arg| {
                    terms.entry_stamp(arg).is_none()
                        || terms.sort(arg).bitvec_width() != Some(width)
                }) {
                    return Some(None);
                }
                let literal = |arg| match terms.get(arg) {
                    TermData::Const(Constant::BitVec { value, .. }) => value.to_u128(),
                    _ => None,
                };
                if let Some(value) = literal(right) {
                    offset = if head == "bvsub" {
                        offset.wrapping_sub(value)
                    } else {
                        offset.wrapping_add(value)
                    } & mask;
                    cursor = left;
                } else if head == "bvadd" {
                    let Some(value) = literal(left) else {
                        return Some(None);
                    };
                    offset = offset.wrapping_add(value) & mask;
                    cursor = right;
                } else {
                    return Some(None);
                }
            }
            _ => return Some(None),
        }
    }
}

/// Advice over one immutable earlier fact view; no partial index escapes a
/// canceled scan or a refused shared debit.
fn index_authored_disequalities(
    terms: &TermStore,
    facts: &FactBase,
    limit: usize,
    work: &mut SharedGroundWork,
    stop: &impl Fn() -> bool,
) -> Option<DetHashMap<(TermId, TermId), usize>> {
    if stop() {
        return None;
    }
    work.spend(facts.facts().len())?;
    let mut index = DetHashMap::default();
    index.try_reserve(facts.facts().len()).ok()?;
    for (position, fact) in facts.facts().iter().enumerate() {
        if stop() {
            return None;
        }
        if fact.edge_limit > limit {
            continue;
        }
        let TermData::Not(atom) = terms.get(fact.literal) else {
            continue;
        };
        let Some((left, right)) = decode_eq_local(terms, *atom) else {
            continue;
        };
        if terms.entry_stamp(left).is_none()
            || terms.entry_stamp(right).is_none()
            || terms.sort(left) != terms.sort(right)
        {
            continue;
        }
        let pair = if left <= right {
            (left, right)
        } else {
            (right, left)
        };
        index.entry(pair).or_insert(position);
    }
    Some(index)
}

impl Executor {
    pub(super) fn add_ground_read_chain_edges(
        &mut self,
        closure: &mut GroundClosure,
        state: &mut ReadChainState,
        facts: &FactBase,
        work: &mut SharedGroundWork,
    ) -> Option<()> {
        state.bind(&self.ctx)?;
        let stop = self.make_proof_assembly_should_stop();
        let ranges = self.ground_negative_ranges(facts, work)?;
        // Build class-to-newest-store maps once against one immutable closure
        // view. Merge only after every proposal is collected; no growing class
        // relation is ever reused as a cached hit/miss.
        let mut hits: DetHashMap<TermId, DetHashMap<usize, usize>> = DetHashMap::default();
        let mut class_addresses = ClassAddresses::default();
        // Lazily inspect existing facts only if the established offset/range
        // routes decline. Every scanned fact debits the SAME shared meter.
        let mut authored_disequalities: Option<DetHashMap<(TermId, TermId), usize>> = None;
        let mut pending = Vec::new();
        work.spend(closure.nodes().len())?;
        let mut reads = Vec::new();
        reads.try_reserve_exact(closure.nodes().len()).ok()?;
        reads.extend_from_slice(closure.nodes());
        for read in reads {
            if stop() {
                return None;
            }
            if state.completed.contains(&read) {
                continue;
            }
            let Some((array, key)) = select_parts_local(&self.ctx.terms, read) else {
                continue;
            };
            if store_parts_local(&self.ctx.terms, array).is_none() {
                continue;
            }
            let Sort::Array(shape) = self.ctx.terms.sort(array) else {
                continue;
            };
            if self.ctx.terms.sort(key) != &shape.index_sort
                || self.ctx.terms.sort(read) != &shape.element_sort
            {
                continue;
            }
            let Some(chain) = state.array(&self.ctx.terms, array, work)? else {
                continue;
            };
            if !hits.contains_key(&array) {
                work.spend(chain.len())?;
                let mut positions = DetHashMap::default();
                positions.try_reserve(chain.len()).ok()?;
                for (position, store) in chain.iter().enumerate() {
                    if stop() {
                        return None;
                    }
                    positions
                        .entry(closure.class(store.index)?)
                        .or_insert(position);
                }
                hits.try_reserve(1).ok()?;
                hits.insert(array, positions);
            }
            if chain.is_empty() {
                continue;
            }
            let hit = hits.get(&array)?.get(&closure.class(key)?).copied();
            let (position, at, value) = if let Some(position) = hit {
                let Store { index, value, .. } = chain[position];
                (position, index, Some(value))
            } else {
                (chain.len(), key, None)
            };
            if value.is_some_and(|value| closure.same_class(read, value)) {
                state.completed.try_reserve(1).ok()?;
                state.completed.insert(read);
                continue;
            }
            let point = state.address(&self.ctx.terms, at, work)?;
            let source_ranges = ranges.get(&at).map_or(&[][..], Vec::as_slice);
            if hit.is_some() {
                work.spend(position)?;
            }
            let mut guards = Vec::new();
            let mut seen = DetHashSet::default();
            if hit.is_some() {
                guards.try_reserve_exact(position).ok()?;
                seen.try_reserve(position).ok()?;
            }
            let mut separated = true;
            for store in &chain[..position] {
                if stop() {
                    return None;
                }
                if hit.is_none() {
                    // An unknown first guard must not debit an unvisited
                    // suffix. Successful fallthrough still pays every slot.
                    work.spend(1)?;
                    seen.try_reserve(1).ok()?;
                }
                let index = store.index;
                if !seen.insert(index) {
                    continue;
                }
                let address = state.address(&self.ctx.terms, index, work)?;
                let direct = address
                    .zip(point)
                    .and_then(|(address, point)| separated_bases(closure, address, point));
                let skip = if let Some(bases) = direct {
                    ReadSkip {
                        index,
                        index_image: index,
                        point_image: at,
                        bases,
                        range: None,
                        disequality: None,
                    }
                } else {
                    // Inspect only the two needed current classes. The cache
                    // belongs to this immutable proposal pass, not the query.
                    let index_class = closure.class(index)?;
                    let point_class = closure.class(at)?;
                    for (class, term) in [(index_class, index), (point_class, at)] {
                        if !class_addresses.contains_key(&class) {
                            let candidates = state.index_addresses(
                                &self.ctx.terms,
                                closure,
                                term,
                                work,
                                &stop,
                            )?;
                            class_addresses.try_reserve(1).ok()?;
                            class_addresses.insert(class, candidates);
                        }
                    }
                    let mut selected = None;
                    // Ordinary source/image offset proofs precede every
                    // source-range proposal. Both passes spend the same work.
                    for range_phase in [false, true] {
                        if range_phase {
                            if ranges.is_empty() {
                                break;
                            }
                            if let Some(address) = address {
                                if let Some(separation) = separated_with_ranges(
                                    closure,
                                    None,
                                    address,
                                    source_ranges,
                                    work,
                                )? {
                                    selected = Some(ReadSkip {
                                        index,
                                        index_image: index,
                                        point_image: at,
                                        bases: separation.bases,
                                        range: separation.range,
                                        disequality: None,
                                    });
                                    break;
                                }
                            }
                        }
                        'images: for &(index_image, address) in class_addresses.get(&index_class)? {
                            // An opaque actual point can still have a source
                            // range; alternate points require earlier paths.
                            let points = std::iter::once((at, point)).chain(
                                class_addresses
                                    .get(&point_class)?
                                    .iter()
                                    .filter(|(image, _)| *image != at)
                                    .map(|&(image, address)| (image, Some(address))),
                            );
                            for (point_image, point) in points {
                                work.spend(1)?;
                                if stop() {
                                    return None;
                                }
                                let image_ranges = if range_phase {
                                    ranges.get(&point_image).map_or(&[][..], Vec::as_slice)
                                } else {
                                    &[]
                                };
                                let Some(separation) = separated_with_ranges(
                                    closure,
                                    point,
                                    address,
                                    image_ranges,
                                    work,
                                )?
                                else {
                                    continue;
                                };
                                let candidate = ReadSkip {
                                    index,
                                    index_image,
                                    point_image,
                                    bases: separation.bases,
                                    range: separation.range,
                                    disequality: None,
                                };
                                if separation.bases.is_none() && separation.range.is_none() {
                                    selected = Some(candidate);
                                    break 'images;
                                }
                                if selected.is_none() {
                                    selected = Some(candidate);
                                }
                            }
                        }
                        if selected.is_some() {
                            break;
                        }
                    }
                    if selected.is_none() {
                        if authored_disequalities.is_none() {
                            authored_disequalities = Some(index_authored_disequalities(
                                &self.ctx.terms,
                                facts,
                                closure.edges().len(),
                                work,
                                &stop,
                            )?);
                        }
                        let pair = if index <= at {
                            (index, at)
                        } else {
                            (at, index)
                        };
                        if let Some(&fact) = authored_disequalities.as_ref()?.get(&pair) {
                            selected = Some(ReadSkip {
                                index,
                                index_image: index,
                                point_image: at,
                                bases: None,
                                range: None,
                                disequality: Some(fact),
                            });
                        }
                    }
                    let Some(selected) = selected else {
                        separated = false;
                        break;
                    };
                    selected
                };
                work.spend(1)?;
                if hit.is_none() {
                    guards.try_reserve(1).ok()?;
                }
                guards.push(skip);
            }
            if !separated {
                continue;
            }
            if closure.edges().len().checked_add(pending.len())? >= MAX_EDGES
                || state.witnesses.len().checked_add(pending.len())? >= MAX_EDGES
            {
                return None;
            }
            let end = if hit.is_some() {
                ReadChainEnd::Value
            } else {
                ReadChainEnd::Base(chain.last()?.inner)
            };
            let value = if let Some(value) = value {
                value
            } else {
                // All stores were separated before constructing a new read.
                // This is the exact chain tail, not a fresh memory assumption.
                let base = chain.last()?.inner;
                if let Some(value) = self.ctx.terms.get_const_array(base) {
                    value
                } else {
                    work.spend(1)?;
                    if closure.nodes().len() >= MAX_NODES || stop() {
                        return None;
                    }
                    let element_sort = shape.element_sort.clone();
                    let value =
                        self.ctx
                            .terms
                            .mk_app(Symbol::named("select"), [base, key], element_sort);
                    closure.register(value);
                    value
                }
            };
            pending.try_reserve(1).ok()?;
            pending.push((
                read,
                value,
                ReadChainWitness {
                    end,
                    index: at,
                    skipped: guards,
                },
            ));
        }
        for (read, value, witness) in pending {
            if stop() {
                return None;
            }
            work.spend(1)?;
            if closure.same_class(read, value) {
                state.completed.try_reserve(1).ok()?;
                state.completed.insert(read);
                continue;
            }
            state.witnesses.try_reserve(1).ok()?;
            state.completed.try_reserve(1).ok()?;
            let index = state.witnesses.len();
            state.witnesses.push(witness);
            if !closure.merge(read, value, EdgeReason::ReadChain(index)) {
                return None;
            }
            state.completed.insert(read);
        }
        Some(())
    }
}

#[cfg(test)]
mod class_address_controls {
    use super::*;

    #[test]
    fn index_inventory_does_not_spend_work_on_unrelated_classes() {
        let mut context = Context::new();
        let x = context.terms.mk_var("x", Sort::bitvec(8));
        let y = context.terms.mk_var("y", Sort::bitvec(8));
        let one = context.terms.mk_bitvec(1.into(), 8);
        let image = context
            .terms
            .mk_app(Symbol::named("bvadd"), [x, one], Sort::bitvec(8));
        let mut closure = GroundClosure::default();
        for term in [x, y, one, image] {
            closure.register(term);
        }
        closure.merge(y, image, EdgeReason::Congruent);
        for id in 0..128 {
            let unrelated = context
                .terms
                .mk_var(format!("unrelated{id}"), Sort::bitvec(8));
            closure.register(unrelated);
        }
        let mut state = ReadChainState::default();
        let mut work = SharedGroundWork::new(8);
        let candidates = state
            .index_addresses(&context.terms, &closure, y, &mut work, &|| false)
            .unwrap();
        assert_eq!(candidates.len(), 2);
        assert!(!work.refused());
        assert!(work.remaining() > 0);
    }

    #[test]
    fn representative_inventory_rejects_foreign_entries_and_exhausted_work() {
        let context = Context::new();
        let mut closure = GroundClosure::default();
        closure.register(TermId(u32::MAX));
        let mut state = ReadChainState::default();
        let mut work = SharedGroundWork::new(work::MAX_SHARED_WORK);
        assert!(state
            .index_addresses(
                &context.terms,
                &closure,
                TermId(u32::MAX),
                &mut work,
                &|| false
            )
            .is_none());
        let before = context.terms.len();
        let mut work = SharedGroundWork::new(0);
        assert!(state
            .index_addresses(
                &context.terms,
                &closure,
                TermId(u32::MAX),
                &mut work,
                &|| false
            )
            .is_none());
        assert_eq!(context.terms.len(), before);
    }
}

#[cfg(test)]
mod authored_guard_scan_controls {
    use super::super::facts::GroundSearch;
    use super::*;
    use ay_frontend::parse;
    use std::cell::Cell;

    fn search() -> (Executor, GroundSearch) {
        let input = "(set-logic QF_BV) (declare-const p (_ BitVec 8)) (declare-const a (_ BitVec 8)) (declare-const b (_ BitVec 8)) (declare-const c (_ BitVec 8)) (assert (and (not (= p a)) (not (= p b)) (not (= p c))))";
        let mut exec = Executor::new();
        exec.execute_all(&parse(input).unwrap()).unwrap();
        let surface = exec.ctx.assertions_parsed()[0].clone();
        let root = exec.raw_intern_ground_bv_surface(&surface).unwrap();
        let mut search = GroundSearch::default();
        exec.register_ground_subterms(&mut search.closure, root)
            .unwrap();
        exec.seed_ground_root_facts(&mut search, &[root]).unwrap();
        (exec, search)
    }

    #[test]
    fn authored_guard_scan_uses_the_same_retired_work_payer() {
        let (exec, search) = search();
        let count = search.facts.facts().len();
        assert!(count >= 3);
        let mut work = SharedGroundWork::new(count - 1);
        for _ in 0..2 {
            assert!(index_authored_disequalities(
                &exec.ctx.terms,
                &search.facts,
                search.closure.edges().len(),
                &mut work,
                &|| false
            )
            .is_none());
            assert!(work.refused());
            assert_eq!(work.remaining(), count - 1);
        }
    }

    #[test]
    fn authored_guard_scan_cancellation_publishes_no_partial_advice() {
        let (exec, search) = search();
        let count = search.facts.facts().len();
        let mut work = SharedGroundWork::new(count + 10);
        let calls = Cell::new(0);
        let stop = || {
            calls.set(calls.get() + 1);
            calls.get() >= 4
        };
        assert!(index_authored_disequalities(
            &exec.ctx.terms,
            &search.facts,
            search.closure.edges().len(),
            &mut work,
            &stop
        )
        .is_none());
        assert_eq!(calls.get(), 4);
        assert_eq!(work.remaining(), 10);
        assert!(exec.last_proof().is_none());
    }
}
