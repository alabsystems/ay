// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Body-position `let` chains for the public-sort passes.
//!
//! Each pass over a parsed term — [`Context::public_term_info`], the strict
//! retention-shape scan and its occurrence scan — used to recurse one `let`
//! level at a time, cloning the whole binder environment per level and
//! holding every clone alive down the recursion: `O(d²)` memory in the chain
//! depth `d`. These walkers visit the same levels in the same order under ONE
//! cloned environment, exactly as the elaborator's own let-chain walk does
//! (`elaborate/term.rs`).

use ay_core::kani_compat::DetHashMap as HashMap;

use crate::command::Term as ParsedTerm;

use super::{
    strict_shape_memo_key, unretained_finite_set_shape, Context, FiniteSetTermMetadata, PublicSort,
    PublicTermInfo, Result,
};

impl Context {
    /// Whether the live strict-shape scan already holds `term`'s
    /// [`Self::public_term_info`].
    fn strict_term_info_memoised(&self, term: &ParsedTerm) -> bool {
        self.strict_shape_scan
            .as_ref()
            .zip(strict_shape_memo_key(term))
            .is_some_and(|(scan, key)| scan.term_info.contains_key(&key))
    }

    /// Record `info` as `term`'s [`Self::public_term_info`] in the live
    /// strict-shape scan, if there is one.
    fn memoise_strict_term_info(&mut self, term: &ParsedTerm, info: &PublicTermInfo) {
        if let Some((scan, key)) = self
            .strict_shape_scan
            .as_mut()
            .zip(strict_shape_memo_key(term))
        {
            scan.term_info.insert(key, info.clone());
        }
    }

    /// Whether the live strict-shape scan already holds `term`'s
    /// [`Self::parsed_term_contains_finite_set_occurrence`].
    fn strict_occurrence_memoised(&self, term: &ParsedTerm) -> bool {
        self.strict_shape_scan
            .as_ref()
            .zip(strict_shape_memo_key(term))
            .is_some_and(|(scan, key)| scan.occurrence.contains_key(&key))
    }

    /// [`Self::public_term_info`] of `(let bindings body)`, walking the
    /// body-position chain of nested `let`s under ONE cloned environment.
    ///
    /// Recursing one level at a time cloned the whole environment per level
    /// and held every clone alive down the recursion: `O(d²)` memory in the
    /// chain depth `d`. That is the shape every Tseitin/CSE printer emits —
    /// `QF_LRA/hybrid_networks/*.inter.{bmc,ind}_k100` asserts 8,550-deep
    /// chains — and at `--memory 3000` the allocator's ceiling ended each of
    /// those runs after its first `check-sat`, silently with exit 124 because
    /// a verdict was already printed. A synthetic 8,000-deep chain peaked at
    /// 4.2 GB RSS here; the elaborator had already hoisted its own clone out
    /// of this loop for the same reason (`elaborate/term.rs`).
    ///
    /// Semantics are unchanged: the levels stay separate and are walked outer
    /// to inner, every value of a level is typed under the environment as it
    /// stood BEFORE that level (parallel `let`), and the level's names are
    /// published together afterwards. Metadata merges are flag unions, so the
    /// order they are folded in is immaterial. Under a strict-shape scan each
    /// inner `let` node is memoised with exactly the result its own recursion
    /// would have produced (the final body's sort, with its metadata merged
    /// with that of every level from the node inwards), and a node already in
    /// the memo ends the walk so the memo still answers it.
    pub(super) fn public_let_chain_info(
        &mut self,
        bindings: &[(String, ParsedTerm)],
        body: &ParsedTerm,
        env: &HashMap<String, PublicSort>,
    ) -> Result<PublicTermInfo> {
        // `levels[0]` is this node's binder list; `levels[i]` for `i >= 1`
        // belongs to the inner `let` node `inner_nodes[i - 1]`.
        let mut levels: Vec<&[(String, ParsedTerm)]> = vec![bindings];
        let mut inner_nodes: Vec<&ParsedTerm> = Vec::new();
        let mut final_body = body;
        while let ParsedTerm::Let(inner_bindings, inner_body) = final_body {
            if self.strict_term_info_memoised(final_body) {
                break;
            }
            levels.push(inner_bindings);
            inner_nodes.push(final_body);
            final_body = inner_body;
        }

        let mut chain_env = env.clone();
        let mut level_metadata = Vec::with_capacity(levels.len());
        let mut values = Vec::new();
        for level in &levels {
            let mut metadata = FiniteSetTermMetadata::default();
            for (name, value) in level.iter() {
                let info = self.public_term_info(value, &chain_env)?;
                metadata.merge(info.metadata);
                values.push((name.clone(), info.sort));
            }
            chain_env.extend(values.drain(..));
            level_metadata.push(metadata);
        }
        let mut result = self.public_term_info(final_body, &chain_env)?;
        drop(chain_env);
        for (level, metadata) in level_metadata.into_iter().enumerate().rev() {
            result.metadata.merge(metadata);
            if let Some(node) = level
                .checked_sub(1)
                .and_then(|inner| inner_nodes.get(inner))
            {
                self.memoise_strict_term_info(node, &result);
            }
        }
        Ok(result)
    }

    /// The `let` arm of
    /// [`Self::parsed_term_contains_finite_set_occurrence_uncached`], walking
    /// the body-position chain of nested `let`s under ONE cloned environment
    /// instead of one clone per level held alive down the recursion (`O(d²)`
    /// memory in the chain depth; see [`Self::public_let_chain_info`]).
    ///
    /// The caller has already checked this node's own `public_term_info`
    /// flags. Each inner `let` node entered is checked exactly as its own
    /// uncached scan would check it — its `public_term_info` flags first, then
    /// its values in order under the pre-level environment — and the first
    /// hit answers `true` for every node entered so far, since each of them
    /// is the disjunction of its own checks and its body's. A walk that
    /// reaches the final body answers that body's result for all of them.
    /// Under a strict-shape scan every inner node entered is memoised with
    /// that answer, and a node already in the memo ends the walk so the memo
    /// answers it. Errors propagate before anything is memoised.
    pub(super) fn let_chain_contains_finite_set_occurrence(
        &mut self,
        bindings: &[(String, ParsedTerm)],
        body: &ParsedTerm,
        env: &HashMap<String, PublicSort>,
    ) -> Result<bool> {
        let mut chain_env = env.clone();
        let mut level_bindings = bindings;
        let mut level_body = body;
        let mut inner_nodes: Vec<&ParsedTerm> = Vec::new();
        let mut values = Vec::new();
        let found = 'chain: loop {
            for (name, value) in level_bindings {
                if self.parsed_term_contains_finite_set_occurrence(value, &chain_env)? {
                    break 'chain true;
                }
                let value_sort = self.public_term_info(value, &chain_env)?.sort;
                values.push((name.clone(), value_sort));
            }
            chain_env.extend(values.drain(..));
            match level_body {
                ParsedTerm::Let(inner_bindings, inner_body)
                    if !self.strict_occurrence_memoised(level_body) =>
                {
                    inner_nodes.push(level_body);
                    let info = self.public_term_info(level_body, &chain_env)?;
                    if info.sort.contains_finite_set() || info.metadata.uses_finite_set {
                        break 'chain true;
                    }
                    level_bindings = inner_bindings;
                    level_body = inner_body;
                }
                _ => {
                    break 'chain self
                        .parsed_term_contains_finite_set_occurrence(level_body, &chain_env)?;
                }
            }
        };
        if let Some(scan) = self.strict_shape_scan.as_mut() {
            for node in inner_nodes {
                if let Some(key) = strict_shape_memo_key(node) {
                    scan.occurrence.insert(key, found);
                }
            }
        }
        Ok(found)
    }

    /// The `let` arm of [`Self::validate_strict_finite_set_retention_shape`],
    /// walking the body-position chain of nested `let`s under ONE cloned
    /// environment instead of one clone per level held alive down the
    /// recursion (`O(d²)` memory in the chain depth; see
    /// [`Self::public_let_chain_info`]). Every level is checked exactly as the
    /// per-level recursion checked it, in the same order: the `let` node's
    /// occurrence scan, then each value's shape and sort under the pre-level
    /// environment, before the level's names are published together.
    pub(super) fn validate_strict_let_chain_retention_shape(
        &mut self,
        term: &ParsedTerm,
        env: &HashMap<String, PublicSort>,
    ) -> Result<()> {
        let mut chain_env = env.clone();
        let mut node = term;
        let mut values = Vec::new();
        while let ParsedTerm::Let(bindings, body) = node {
            if self.parsed_term_contains_finite_set_occurrence(node, &chain_env)? {
                return Err(unretained_finite_set_shape("let"));
            }
            for (name, value) in bindings {
                self.validate_strict_finite_set_retention_shape(value, &chain_env)?;
                let value_sort = self.public_term_info(value, &chain_env)?.sort;
                values.push((name.clone(), value_sort));
            }
            chain_env.extend(values.drain(..));
            node = body;
        }
        self.validate_strict_finite_set_retention_shape(node, &chain_env)
    }
}
