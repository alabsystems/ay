// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The NESTED node tree (plan §3.1, milestone M2).
//!
//! Every authored root is first Skolemized at the top level: a quantifier
//! occurrence that is effectively existential (authored `exists` under an
//! even number of negations, or authored `forall` under an odd number) and
//! sits under no other quantifier and at a single polarity is replaced by its
//! body over fresh Skolem constants. Skolemizing a positive existential in any
//! Boolean context is satisfiability-preserving, so the rewritten roots are
//! equisatisfiable with the authored ones.
//!
//! Every remaining quantifier occurrence becomes a [`NNode`]:
//!
//! * consecutive same-kind binders are MERGED (`∀a ∀b ∀c` is one node with
//!   three counterexample constants) unless a name would repeat;
//! * the node's body is rewritten over fresh counterexample constants `e⃗`
//!   (capture-avoiding exact substitution), so a child quantifier subterm of
//!   that body is a closed-over-`e⃗` term that identifies the child node;
//! * each parent→child edge records the POLARITY of the occurrence inside the
//!   parent's body (positive, negative or both, e.g. under an iff).
//!
//! Quantifiers under `and`/`or`/`not`/`=>`/Bool `ite`/Bool `=`/`xor`/Bool
//! `distinct` are admitted at any depth; any other operator over a quantified
//! argument declines the whole problem.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};

use super::caps::{MAX_DEPTH, MAX_NODES};
use super::session::NestedSessionCache;
use crate::ematching::subst_vars_exact_qf;

/// Authored quantifier kind of a node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    Forall,
    Exists,
}

/// Occurrence polarity: positive, negative, or both.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Pol {
    pub(crate) pos: bool,
    pub(crate) neg: bool,
}

impl Pol {
    pub(crate) const POS: Self = Self {
        pos: true,
        neg: false,
    };
    pub(crate) const NEG: Self = Self {
        pos: false,
        neg: true,
    };
    pub(crate) const BOTH: Self = Self {
        pos: true,
        neg: true,
    };

    pub(crate) fn flip(self) -> Self {
        Self {
            pos: self.neg,
            neg: self.pos,
        }
    }

    fn union(self, other: Self) -> Self {
        Self {
            pos: self.pos || other.pos,
            neg: self.neg || other.neg,
        }
    }

    pub(crate) fn both(self) -> bool {
        self.pos && self.neg
    }
}

/// One parent→child occurrence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Edge {
    pub(crate) child: usize,
    pub(crate) pol: Pol,
}

/// One merged quantifier block.
#[derive(Clone, Debug)]
pub(crate) struct NNode {
    pub(crate) kind: Kind,
    pub(crate) binders: Vec<(String, Sort)>,
    /// Fresh counterexample constants, one per binder.
    pub(crate) ce_vars: Vec<TermId>,
    /// The merged body over `ce_vars`; its maximal quantified subterms are the
    /// children's `quantifier` terms.
    pub(crate) ce_body: TermId,
    pub(crate) children: Vec<Edge>,
    /// Alternation depth (top-level nodes are 1).
    pub(crate) depth: usize,
    /// Enclosing counterexample constants the node's instances may mention.
    pub(crate) env: Vec<TermId>,
    /// Polarity of the node's top-level occurrences, if it has any.
    pub(crate) top: Option<Pol>,
}

/// The whole problem as the nested search sees it.
#[derive(Clone, Debug, Default)]
pub(crate) struct NestedTree {
    /// Skolemized roots; their maximal quantified subterms are top nodes.
    pub(crate) roots: Vec<TermId>,
    pub(crate) nodes: Vec<NNode>,
    pub(crate) node_of: HashMap<TermId, usize>,
    /// Top-level nodes, in first-occurrence order.
    pub(crate) top: Vec<usize>,
    pub(crate) skolems: Vec<TermId>,
}

impl NestedTree {
    pub(crate) fn max_depth(&self) -> usize {
        self.nodes.iter().map(|n| n.depth).max().unwrap_or(0)
    }
}

/// Why the nested builder refused the problem.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NestedTreeDecline {
    /// A quantified argument under an operator that is not a connective.
    Connective,
    BinderSort,
    TooManyNodes,
    TooDeep,
    NoQuantifier,
    Substitution,
}

fn binders_admissible(binders: &[(String, Sort)]) -> bool {
    let mut names = HashSet::default();
    !binders.is_empty()
        && binders
            .iter()
            .all(|(name, sort)| matches!(sort, Sort::Real | Sort::Bool) && names.insert(name))
}

/// Argument polarities of a Boolean connective, or `None` for an operator
/// the tree does not treat as a connective.
pub(crate) fn arg_pols(
    terms: &TermStore,
    name: &str,
    args: &[TermId],
    pol: Pol,
) -> Option<Vec<Pol>> {
    match name {
        "and" | "or" => Some(vec![pol; args.len()]),
        "=>" => {
            let mut out = vec![pol.flip(); args.len()];
            *out.last_mut()? = pol;
            Some(out)
        }
        "xor" => Some(vec![Pol::BOTH; args.len()]),
        "=" | "distinct" if args.iter().all(|&a| matches!(terms.sort(a), Sort::Bool)) => {
            Some(vec![Pol::BOTH; args.len()])
        }
        _ => None,
    }
}

struct Builder<'a> {
    terms: &'a mut TermStore,
    /// The session cache (M4): a quantifier term it knows is rebuilt over
    /// its cached counterexample constants, so cached instances keep their
    /// meaning (`session.rs`).
    reuse: Option<&'a NestedSessionCache>,
    tree: NestedTree,
    skolem_memo: HashMap<(TermId, bool, bool), TermId>,
    all_ce: HashSet<TermId>,
    quantified: HashMap<TermId, bool>,
}

impl Builder<'_> {
    /// Memoized "contains a quantifier" (one walk per term over the build).
    fn has_quantifier(&mut self, term: TermId) -> bool {
        if let Some(&known) = self.quantified.get(&term) {
            return known;
        }
        let children: Vec<TermId> = match self.terms.get(term) {
            TermData::App(_, args) => args.clone(),
            TermData::Not(inner) => vec![*inner],
            TermData::Ite(c, a, b) => vec![*c, *a, *b],
            TermData::Var(..) | TermData::Const(..) => Vec::new(),
            // Quantifiers, and conservatively anything else (a `let`).
            _ => {
                self.quantified.insert(term, true);
                return true;
            }
        };
        let known = stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || {
            children.into_iter().any(|c| self.has_quantifier(c))
        });
        self.quantified.insert(term, known);
        known
    }

    /// Skolemize top-level single-polarity effective existentials.
    fn skolemize(&mut self, term: TermId, pol: Pol) -> Result<TermId, NestedTreeDecline> {
        if !self.has_quantifier(term) {
            return Ok(term);
        }
        if let Some(&done) = self.skolem_memo.get(&(term, pol.pos, pol.neg)) {
            return Ok(done);
        }
        let out = match self.terms.get(term).clone() {
            TermData::Not(inner) => {
                let rewritten = self.skolemize(inner, pol.flip())?;
                self.terms.mk_not_raw(rewritten)
            }
            TermData::Ite(c, a, b) => {
                let c2 = self.skolemize(c, Pol::BOTH)?;
                let a2 = self.skolemize(a, pol)?;
                let b2 = self.skolemize(b, pol)?;
                self.terms.mk_ite_raw(c2, a2, b2)
            }
            TermData::App(symbol, args) => {
                let pols = arg_pols(self.terms, symbol.name(), &args, pol)
                    .ok_or(NestedTreeDecline::Connective)?;
                let mut rewritten = Vec::with_capacity(args.len());
                for (&arg, arg_pol) in args.iter().zip(pols) {
                    rewritten.push(self.skolemize(arg, arg_pol)?);
                }
                let sort = self.terms.sort(term).clone();
                self.terms.mk_app(symbol, rewritten, sort)
            }
            TermData::Forall(binders, body, _) | TermData::Exists(binders, body, _) => {
                let exists = matches!(self.terms.get(term), TermData::Exists(..));
                let effective_exists = !pol.both() && (exists == pol.pos);
                if !effective_exists {
                    return Ok(term);
                }
                if !binders_admissible(&binders) {
                    return Err(NestedTreeDecline::BinderSort);
                }
                let mut map: HashMap<String, TermId> = HashMap::default();
                for (name, sort) in &binders {
                    let sk = self
                        .terms
                        .mk_fresh_var(&format!("qlra!sk!{name}"), sort.clone());
                    self.tree.skolems.push(sk);
                    map.insert(name.clone(), sk);
                }
                let instance = subst_vars_exact_qf(self.terms, body, &map)
                    .ok_or(NestedTreeDecline::Substitution)?;
                self.skolemize(instance, pol)?
            }
            _ => return Err(NestedTreeDecline::Connective),
        };
        self.skolem_memo.insert((term, pol.pos, pol.neg), out);
        Ok(out)
    }

    /// Maximal quantified subterms of `term` with their polarities.
    fn occurrences(
        &mut self,
        term: TermId,
        pol: Pol,
    ) -> Result<Vec<(TermId, Pol)>, NestedTreeDecline> {
        let mut found: Vec<(TermId, Pol)> = Vec::new();
        let mut seen: HashSet<(TermId, bool, bool)> = HashSet::default();
        let mut stack = vec![(term, pol)];
        while let Some((t, p)) = stack.pop() {
            if !seen.insert((t, p.pos, p.neg)) || !self.has_quantifier(t) {
                continue;
            }
            match self.terms.get(t) {
                TermData::Forall(..) | TermData::Exists(..) => {
                    match found.iter_mut().find(|(q, _)| *q == t) {
                        Some(entry) => entry.1 = entry.1.union(p),
                        None => found.push((t, p)),
                    }
                }
                TermData::Not(inner) => stack.push((*inner, p.flip())),
                // Pushed in reverse so occurrences come out left to right.
                TermData::Ite(c, a, b) => {
                    stack.extend([(*b, p), (*a, p), (*c, Pol::BOTH)]);
                }
                TermData::App(symbol, args) => {
                    let pols = arg_pols(self.terms, symbol.name(), args, p)
                        .ok_or(NestedTreeDecline::Connective)?;
                    stack.extend(args.iter().copied().zip(pols).rev());
                }
                _ => return Err(NestedTreeDecline::Connective),
            }
        }
        Ok(found)
    }

    /// The node for quantifier subterm `q`, creating it (and not yet its
    /// children) on first sight.
    fn node_for(&mut self, q: TermId, depth: usize) -> Result<usize, NestedTreeDecline> {
        if let Some(&index) = self.tree.node_of.get(&q) {
            return Ok(index);
        }
        if self.tree.nodes.len() >= MAX_NODES {
            return Err(NestedTreeDecline::TooManyNodes);
        }
        if depth > MAX_DEPTH {
            return Err(NestedTreeDecline::TooDeep);
        }
        let (kind, mut binders, mut body) = match self.terms.get(q).clone() {
            TermData::Forall(b, body, _) => (Kind::Forall, b, body),
            TermData::Exists(b, body, _) => (Kind::Exists, b, body),
            _ => return Err(NestedTreeDecline::Connective),
        };
        while let (Kind::Forall, TermData::Forall(b, inner, _))
        | (Kind::Exists, TermData::Exists(b, inner, _)) = (kind, self.terms.get(body))
        {
            let next = (b.clone(), *inner);
            if next
                .0
                .iter()
                .any(|(n, _)| binders.iter().any(|(m, _)| m == n))
            {
                break;
            }
            binders.extend(next.0);
            body = next.1;
        }
        if !binders_admissible(&binders) {
            return Err(NestedTreeDecline::BinderSort);
        }
        let env = self.env_of(q);
        let ce_vars: Vec<TermId> = match self.cached_ce_vars(q, &binders) {
            Some(cached) => cached,
            None => binders
                .iter()
                .map(|(name, sort)| {
                    self.terms
                        .mk_fresh_var(&format!("qlra!e!{name}"), sort.clone())
                })
                .collect(),
        };
        self.all_ce.extend(ce_vars.iter().copied());
        let map: HashMap<String, TermId> = binders
            .iter()
            .map(|(name, _)| name.clone())
            .zip(ce_vars.iter().copied())
            .collect();
        let ce_body =
            subst_vars_exact_qf(self.terms, body, &map).ok_or(NestedTreeDecline::Substitution)?;
        self.tree.nodes.push(NNode {
            kind,
            binders,
            ce_vars,
            ce_body,
            children: Vec::new(),
            depth,
            env,
            top: None,
        });
        let index = self.tree.nodes.len() - 1;
        self.tree.node_of.insert(q, index);
        Ok(index)
    }

    /// The session cache's counterexample constants for `q`, when they fit
    /// its merged binders exactly (count and sorts) and none is already a
    /// constant of another node of this tree.
    fn cached_ce_vars(&self, q: TermId, binders: &[(String, Sort)]) -> Option<Vec<TermId>> {
        let cached = self.reuse?.ce_vars(q)?;
        let fits = cached.len() == binders.len()
            && cached.iter().zip(binders).all(|(&var, (_, sort))| {
                matches!(self.terms.get(var), TermData::Var(..))
                    && self.terms.sort(var) == sort
                    && !self.all_ce.contains(&var)
            });
        fits.then(|| cached.to_vec())
    }

    /// Counterexample constants occurring in `q` (all free: they are fresh).
    fn env_of(&self, q: TermId) -> Vec<TermId> {
        let mut out = Vec::new();
        let mut seen = HashSet::default();
        let mut stack = vec![q];
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            if self.all_ce.contains(&t) {
                out.push(t);
            }
            match self.terms.get(t) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
                _ => {}
            }
        }
        out.sort();
        out
    }
}

/// Build the nested tree, or say why the nested search cannot treat this
/// problem. Mints Skolem and counterexample constants into `terms`.
#[cfg(test)]
pub(crate) fn build_nested_tree(
    terms: &mut TermStore,
    roots: &[TermId],
) -> Result<NestedTree, NestedTreeDecline> {
    build_nested_tree_reusing(terms, roots, None)
}

/// Build the nested tree (see `build_nested_tree`), rebuilding every quantifier term the session
/// cache knows over its cached counterexample constants (M4).
pub(crate) fn build_nested_tree_reusing(
    terms: &mut TermStore,
    roots: &[TermId],
    reuse: Option<&NestedSessionCache>,
) -> Result<NestedTree, NestedTreeDecline> {
    let mut builder = Builder {
        terms,
        reuse,
        tree: NestedTree::default(),
        skolem_memo: HashMap::default(),
        all_ce: HashSet::default(),
        quantified: HashMap::default(),
    };
    for &root in roots {
        let rewritten = builder.skolemize(root, Pol::POS)?;
        builder.tree.roots.push(rewritten);
    }
    for index in 0..builder.tree.roots.len() {
        let root = builder.tree.roots[index];
        for (q, pol) in builder.occurrences(root, Pol::POS)? {
            let node = builder.node_for(q, 1)?;
            let entry = &mut builder.tree.nodes[node];
            entry.top = Some(entry.top.unwrap_or_default().union(pol));
            if !builder.tree.top.contains(&node) {
                builder.tree.top.push(node);
            }
        }
    }
    if builder.tree.top.is_empty() {
        return Err(NestedTreeDecline::NoQuantifier);
    }
    // Breadth-first: children are created after their parent's constants.
    let mut next = 0;
    while next < builder.tree.nodes.len() {
        let (body, depth) = {
            let node = &builder.tree.nodes[next];
            (node.ce_body, node.depth)
        };
        let mut edges: Vec<Edge> = Vec::new();
        for (q, pol) in builder.occurrences(body, Pol::POS)? {
            let child = builder.node_for(q, depth + 1)?;
            edges.push(Edge { child, pol });
        }
        builder.tree.nodes[next].children = edges;
        next += 1;
    }
    Ok(builder.tree)
}
