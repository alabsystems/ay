// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Branch selection and DFS frame bookkeeping for the exact 2-club search.

use super::{SearchState, TwoClub, MAX_VERTICES};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ViolatingBranchRule {
    First,
    ViolDegree,
    /// MARKED BRANCHING (`TWO_CLUB_BRANCH=marked`): on violating pair (a, b),
    /// branch `a OUT` | `a COMMITTED` (marked). The include side deletes every
    /// vertex conflicting with a marked vertex, iterated to a fixed point —
    /// the O(1.62^n) include/exclude device of the exact 2-club literature
    /// (Bourjolly 2002 onward; see the development design notes).
    Marked,
    /// MARKED branching with a SELECTION rule (`TWO_CLUB_BRANCH=marked-min`):
    /// commit the free vertex of MINIMUM violating degree.
    ///
    /// Plain [`Self::Marked`] inherited the first-by-index pair scan and always
    /// committed `pairs[pi].0`, so the branch vertex was whatever the pair
    /// ordering happened to put first — the open question left at
    /// [`SearchState::find_violating`]. Committing the pair's *other* endpoint
    /// is equally sound (the include/exclude dichotomy holds at ANY vertex of
    /// `C`), so a rule may range over vertices rather than pair indices.
    ///
    /// The textbook answer is MAXIMUM degree: the exclude child drops 1 vertex
    /// while the include child's conflict sweep drops `deg(v)` at once, so the
    /// branching vector is `(1, deg(v))` and bigger looks strictly better. It
    /// was implemented and it LOST, 7 cells out of 7 — at a fixed 4097-node
    /// budget the kill frontier fell from 145/144/145/142/144/140/141 to
    /// 110/112/105/103/112/107/108, with `dives` collapsing 3 -> 1. That is the
    /// exact signature already recorded for [`Self::ViolDegree`]: maximum degree
    /// shrinks `C` fastest, which means diving into matching-rich bottom
    /// territory, and on this instance kill HEIGHT beats kill volume.
    ///
    /// So the rule that ships is the MIRROR of the textbook one. Committing a
    /// minimum-degree vertex deletes as little as possible per include child,
    /// which keeps `C` large and holds the search high in the tree where a kill
    /// erases an exponentially bigger subtree. Measured on 2club200v15p5scn,
    /// paired same-cell, both arms run simultaneously so contention is shared:
    ///
    /// ```text
    ///   kill frontier, fixed 4097-node budget, marked -> marked-min
    ///     145->155  144->153  145->153  143->154  140->153  141->152   (6/6)
    ///   kill frontier, fixed WALL TIME (the budget the field campaign runs)
    ///     300 s:  147->160  146->156  147->157  145->155  145->156  145->155
    ///     240 s:  145->158  145->155  145->157  145->154                (10/10)
    /// ```
    ///
    /// +9..+13 levels on 10 of 10 paired cells, while doing ~5x FEWER nodes —
    /// the point is that the nodes are spent higher. `rx=` (right expansions by
    /// height band) shows where: work at `c ∈ [150,160)` goes up ~10x
    /// (37..76 -> 412..908) and the `[160,170)` band first becomes non-trivial.
    /// For scale, twelve-hour field cells under plain `marked` topped out at
    /// frontier 150.
    ///
    /// CAVEAT, stated plainly: `front` is a PROXY. No cell completes in either
    /// arm here, so this is evidence about search shape, not a demonstration of
    /// faster closure — and it is one instance family.
    ///
    /// NOT the default. `marked` is what the archived campaign ledgers were
    /// produced with, and silently redefining it would break comparability with
    /// every recorded cell.
    MarkedMinDegree,
}

impl ViolatingBranchRule {
    pub(super) fn from_selector(value: Option<&std::ffi::OsStr>) -> Self {
        if value == Some(std::ffi::OsStr::new("viol")) {
            Self::ViolDegree
        } else if value == Some(std::ffi::OsStr::new("marked")) {
            Self::Marked
        } else if value == Some(std::ffi::OsStr::new("marked-min")) {
            Self::MarkedMinDegree
        } else {
            Self::First
        }
    }

    /// Both marked variants run the mark/sweep device; they differ only in which
    /// vertex is branched on.
    pub(super) const fn is_marked(self) -> bool {
        matches!(self, Self::Marked | Self::MarkedMinDegree)
    }
}

impl SearchState {
    pub(super) fn remove(&mut self, v: usize, tc: &TwoClub, undo: &mut Vec<(u32, u8)>) {
        debug_assert!(self.in_c[v]);
        self.in_c[v] = false;
        self.c_size -= 1;
        for &pi in &tc.pair_of_vertex[v] {
            if self.both_in[pi as usize] {
                self.both_in[pi as usize] = false;
                undo.push((pi, 0));
            }
        }
        for &pi in &tc.cn_of_vertex[v] {
            self.cn_alive[pi as usize] -= 1;
            undo.push((pi, 1));
        }
    }
    pub(super) fn undo(&mut self, v: usize, log: &[(u32, u8)]) {
        for &(pi, kind) in log.iter().rev() {
            match kind {
                0 => self.both_in[pi as usize] = true,
                _ => self.cn_alive[pi as usize] += 1,
            }
        }
        self.in_c[v] = true;
        self.c_size += 1;
    }
    /// A violating pair: both endpoints in C and zero surviving common neighbours.
    pub(super) fn find_violating(&self, tc: &TwoClub) -> Option<usize> {
        // BRANCHING RULE: among the active violating pairs, pick the one whose
        // endpoints carry the maximum total VIOLATING-DEGREE (memberships in
        // other active violating pairs). Removing a high-viol-degree endpoint
        // resolves many pairs at once — the classic fail-fast branching
        // preference; the previous first-by-index scan was arbitrary. Two
        // passes over the same O(pairs) scan: collect violating pairs +
        // per-vertex counts, then score. Env A/B: TWO_CLUB_BRANCH=first
        // restores the old rule.
        // DEFAULT: first-by-index. The viol-degree rule (TWO_CLUB_BRANCH=viol)
        // cuts pure tree size ~5x on band-only synthetics but MEASURED NEGATIVE
        // on the real instance: it concentrates the DFS in matching-rich bottom
        // territory (frontier 145 -> 112, dives 5 -> 1) — kill HEIGHT beats
        // kill volume here. Re-evaluate together with marked branching.
        // MARKED mode keeps the first-by-index pair scan by DEFAULT, but the
        // "re-evaluate together with marked branching" question above is now
        // answered: see `find_violating_marked` and
        // `ViolatingBranchRule::MarkedMinDegree`. Maximum violating degree fails
        // under marked branching for the same reason it fails here (it dives);
        // MINIMUM violating degree wins, and is opt-in as `marked-min`.
        if tc.branch_rule != ViolatingBranchRule::ViolDegree {
            return self
                .both_in
                .iter()
                .enumerate()
                .position(|(idx, &active)| active && self.cn_alive[idx] == 0);
        }
        let mut viol: Vec<u32> = Vec::new();
        let mut deg = [0u32; 512];
        for (idx, &active) in self.both_in.iter().enumerate() {
            if active && self.cn_alive[idx] == 0 {
                viol.push(idx as u32);
                let (a, b, _) = &tc.pairs[idx];
                deg[*a as usize] += 1;
                deg[*b as usize] += 1;
            }
        }
        viol.into_iter()
            .max_by_key(|&idx| {
                let (a, b, _) = &tc.pairs[idx as usize];
                deg[*a as usize] + deg[*b as usize]
            })
            .map(|idx| idx as usize)
    }

    /// MARKED-mode selection: returns `(pair index, vertex to branch on)`.
    ///
    /// The marked device branches `v OUT | v COMMITTED`, and the include child's
    /// sweep deletes every vertex conflicting with `v`, so the branching vector
    /// is `(1, deg_viol(v))`. The TEXTBOOK reading of that is "commit the vertex
    /// of MAXIMUM violating degree" — and it was implemented and it LOST, 7 cells
    /// of 7, for the same reason [`ViolatingBranchRule::ViolDegree`] loses: it
    /// dives. What ships is the MIRROR, minimum violating degree, which keeps `C`
    /// large and the search high in the tree.
    ///
    /// [`ViolatingBranchRule::Marked`] keeps the historical first-by-index pair
    /// with `v = pairs[pi].0`; [`ViolatingBranchRule::MarkedMinDegree`] scans for
    /// the MIN-degree vertex and returns a pair witnessing it.
    ///
    /// SOUNDNESS: the include/exclude dichotomy `{2-clubs ⊆ C} = {those without
    /// v} ⊎ {those with v}` is valid at EVERY `v ∈ C`, so selection cannot make
    /// the enumeration incomplete — it only reorders the tree. The returned
    /// vertex is always an endpoint of the returned ACTIVE VIOLATING pair, which
    /// preserves both callers' invariants: the sweep guarantees such a pair has
    /// two free endpoints, and `deg_viol(v) ≥ 1` guarantees the include child
    /// deletes at least one vertex, so both children strictly shrink `C` and the
    /// recursion still terminates.
    pub(super) fn find_violating_marked(&self, tc: &TwoClub) -> Option<(usize, usize)> {
        let first = |pi: usize| (pi, tc.pairs[pi].0 as usize);
        if tc.branch_rule != ViolatingBranchRule::MarkedMinDegree {
            return self
                .both_in
                .iter()
                .enumerate()
                .position(|(idx, &active)| active && self.cn_alive[idx] == 0)
                .map(first);
        }
        // Same single O(pairs) scan the ViolDegree rule uses, but accumulating
        // per-VERTEX degree plus one witnessing pair each (stack arrays: the
        // recognizer caps n at MAX_VERTICES).
        let mut deg = [0u32; MAX_VERTICES];
        let mut witness = [u32::MAX; MAX_VERTICES];
        let mut any = false;
        for (idx, &active) in self.both_in.iter().enumerate() {
            if !active || self.cn_alive[idx] != 0 {
                continue;
            }
            any = true;
            let (a, b, _) = &tc.pairs[idx];
            for &endpoint in &[*a as usize, *b as usize] {
                deg[endpoint] += 1;
                if witness[endpoint] == u32::MAX {
                    witness[endpoint] = idx as u32;
                }
            }
        }
        if !any {
            return None;
        }
        // LOWEST violating degree; ties broken by lowest vertex index so the
        // traversal stays deterministic (campaign cells must be reproducible).
        // See `ViolatingBranchRule::MarkedMinDegree` for why the direction is
        // minimum rather than the textbook maximum.
        let best = (0..tc.n)
            .filter(|&v| deg[v] > 0)
            .min_by_key(|&v| (deg[v], v))?;
        Some((witness[best] as usize, best))
    }
}

// The RIGHT side of a two-sided branch on violating pair (a, b) after the
// left (remove-a) subtree unwinds.
#[derive(Clone, Copy)]
pub(super) enum RightBranch {
    /// Default rules: remove the other endpoint b.
    Remove(usize),
    /// Marked mode: COMMIT the left-removed endpoint a to every solution
    /// of the right subtree. No state change at push; the child's Enter
    /// sweep deletes every conflict of the marked set to a fixed point
    /// (the violating partner b at minimum, so the right side always
    /// shrinks C and the tree stays finite).
    Mark(usize),
}
// Explicit DFS: each frame is (vertex_removed, undo_log, phase).
pub(super) enum Frame {
    Enter,
    AfterLeft { right: Option<RightBranch> },
    Exit,
}
// Recursive helper via explicit stack of (frame, removed_vertex, undo).
// `snap`: this node adopted a dual snapshot when it branched; pop it
// (restoring the previous pricing) when its subtree unwinds — BEFORE undoing
// the node's own removal, which was accounted under the previous pricing.
pub(super) struct StackItem {
    pub(super) frame: Frame,
    pub(super) removed: Option<usize>,
    pub(super) undo: Vec<(u32, u8)>,
    pub(super) snap: bool,
    /// `c_size` when this frame was pushed — lets the progress trace report
    /// the OPEN stack's c-distribution (how much skeleton hangs above the
    /// kill frontier, the number that decides grind-vs-restructure).
    pub(super) c_at: usize,
    /// Marked mode: vertex committed when this frame was pushed (the
    /// right-branch child of a mark); unmarked LAST on unwind.
    pub(super) mark: Option<usize>,
    /// Marked mode: sweep deletions performed at this frame's Enter, in
    /// deletion order; undone in REVERSE, before `removed`, on unwind.
    pub(super) extra: Vec<(usize, Vec<(u32, u8)>)>,
}
/// Unwind one frame in EXACT reverse of its forward effects: sweep
/// deletions newest-first, then the frame's own branch removal, then its
/// mark. Callers pop any adopted dual snapshot FIRST (pop-before-undo:
/// `removed` and `extra` were both accounted under the PRE-adoption
/// pricing, which the pop restores).
pub(super) fn unwind_frame(
    item: &mut StackItem,
    state: &mut SearchState,
    lp_enabled: bool,
    dual_d: &[i128],
    dual_sum: &mut i128,
    marked: &mut [bool],
    marked_list: &mut Vec<usize>,
) {
    while let Some((v, log)) = item.extra.pop() {
        if lp_enabled {
            *dual_sum += dual_d[v].min(0);
        }
        state.undo(v, &log);
    }
    if let Some(v) = item.removed {
        if lp_enabled {
            *dual_sum += dual_d[v].min(0);
        }
        state.undo(v, &item.undo);
    }
    if let Some(m) = item.mark {
        marked[m] = false;
        let popped = marked_list.pop();
        debug_assert_eq!(popped, Some(m), "mark unwind out of order");
    }
}
