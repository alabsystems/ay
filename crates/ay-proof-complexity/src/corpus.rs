// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Hard-formula corpus generator.
//!
//! Exposes a deterministic set of hard CNF formulas so downstream tools
//! (e.g., `ay bench run pc-hard-formulas`) can exercise the solver on
//! pigeonhole, parity, Tseitin-on-expander, and random-k-XOR families
//! without duplicating the generator code.
//!
//! The corpus is intentionally *small* (a handful of instances per
//! family) so a full pass finishes in seconds. For larger studies,
//! callers should generate custom corpora via the underlying
//! `hard_formulas::*` and `graph_formulas::*` functions.
//!
//! ## References
//!
//! - Haken (1985), PHP resolution lower bound.
//! - Urquhart (1987), Tseitin formulas on expander graphs.

use crate::cnf::Cnf;
use crate::graph_formulas::tseitin;
use crate::hard_formulas::{ordering_principle, parity, pigeonhole, random_k_cnf};
use crate::Graph;

/// One entry in the hard-formula corpus.
#[derive(Debug, Clone)]
pub struct CorpusEntry {
    /// Family tag (e.g., `"php"`, `"parity"`, `"tseitin"`, `"random-k-cnf"`,
    /// `"ordering-principle"`). Matches the `family` column in
    /// `ay-bench`'s results store.
    pub family: &'static str,
    /// Human-readable instance name, unique within the corpus.
    pub name: String,
    /// The generated formula.
    pub cnf: Cnf,
}

/// Generate the default hard-formula corpus.
///
/// Deterministic (seeded). Returns 4 * ~3 = ~12 small instances covering
/// 4 proof-complexity families. Sizes are chosen so each instance
/// generates in well under a second and stays under a few thousand
/// clauses — suitable for fast regression sweeps.
///
/// Families and their proof-complexity properties:
///
/// | Family               | Proof System     | Complexity              |
/// |----------------------|------------------|-------------------------|
/// | `php`                | Resolution       | 2^Ω(n) (Haken 1985)     |
/// | `parity`             | Resolution       | 2^Ω(n)                  |
/// | `tseitin`            | Tree-Resolution  | 2^Ω(n) (Urquhart 1987)  |
/// | `random-k-cnf`       | All known        | hard near threshold     |
/// | `ordering-principle` | Tree-Resolution  | 2^Ω(n)                  |
#[must_use]
pub fn generate_default_corpus() -> Vec<CorpusEntry> {
    let mut out = Vec::new();

    // Pigeonhole: small holes to keep clause count manageable.
    for n in [3usize, 4, 5] {
        out.push(CorpusEntry {
            family: "php",
            name: format!("php-n{n}"),
            cnf: pigeonhole(n),
        });
    }

    // Parity: exponential-size CNF, keep n small.
    for n in [3usize, 4, 5] {
        out.push(CorpusEntry {
            family: "parity",
            name: format!("parity-n{n}"),
            cnf: parity(n),
        });
    }

    // Tseitin on a simple cycle graph: a minimal expander-adjacent
    // construction without pulling in a graph generator.
    for n in [4usize, 6, 8] {
        let graph = cycle_graph(n);
        // Odd number of "1" charges on even-length cycle is unsatisfiable.
        let charges: Vec<bool> = (0..n).map(|i| i == 0).collect();
        out.push(CorpusEntry {
            family: "tseitin",
            name: format!("tseitin-cycle-n{n}"),
            cnf: tseitin(&graph, &charges),
        });
    }

    // Random k-CNF near the 3-SAT threshold, seeded for determinism.
    for (i, (n, m)) in [(20usize, 85usize), (30, 127)].iter().copied().enumerate() {
        out.push(CorpusEntry {
            family: "random-k-cnf",
            name: format!("random-3sat-n{n}-m{m}-seed{i}"),
            cnf: random_k_cnf(3, n, m, Some(i as u64 + 1)),
        });
    }

    // Ordering principle (OP): small n keeps the formula tractable.
    for n in [4usize, 5] {
        out.push(CorpusEntry {
            family: "ordering-principle",
            name: format!("op-n{n}"),
            cnf: ordering_principle(n),
        });
    }

    out
}

/// Build a simple undirected cycle on `n` vertices (each vertex connected
/// to its two neighbours modulo `n`). Used by the default corpus as a
/// lightweight substrate for Tseitin formulas.
fn cycle_graph(n: usize) -> Graph {
    let mut g = Graph::new(n);
    if n < 2 {
        return g;
    }
    for i in 0..n {
        let j = (i + 1) % n;
        g.add_edge(i, j);
    }
    g
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generate_default_corpus_deterministic() {
        let a = generate_default_corpus();
        let b = generate_default_corpus();
        assert_eq!(a.len(), b.len());
        for (ea, eb) in a.iter().zip(b.iter()) {
            assert_eq!(ea.family, eb.family);
            assert_eq!(ea.name, eb.name);
            assert_eq!(ea.cnf.num_vars(), eb.cnf.num_vars());
            assert_eq!(ea.cnf.num_clauses(), eb.cnf.num_clauses());
        }
    }

    #[test]
    fn test_corpus_contains_expected_families() {
        let corpus = generate_default_corpus();
        let families: std::collections::HashSet<_> = corpus.iter().map(|e| e.family).collect();
        assert!(families.contains("php"));
        assert!(families.contains("parity"));
        assert!(families.contains("tseitin"));
        assert!(families.contains("random-k-cnf"));
        assert!(families.contains("ordering-principle"));
    }

    #[test]
    fn test_corpus_names_are_unique() {
        let corpus = generate_default_corpus();
        let mut seen = std::collections::HashSet::new();
        for entry in &corpus {
            assert!(
                seen.insert(entry.name.clone()),
                "duplicate corpus name: {}",
                entry.name
            );
        }
    }
}
