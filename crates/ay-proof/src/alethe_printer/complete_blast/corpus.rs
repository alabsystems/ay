// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Corpus harness: render a complete Alethe certificate for every SMT-LIB
//! file in a directory, for external checking.
//!
//! The corpus itself is not in the tree, so the harness is selected by the
//! environment rather than disabled by an attribute: without `CBB_SMT2_DIR`
//! `render_corpus_certificates` returns on its first statement and costs
//! nothing. It carried `#[ignore]`, which `ay-quality-gate` forbids outright
//! and which meant the harness ran nowhere at all. Run it explicitly:
//!
//! ```text
//! CBB_SMT2_DIR=… CBB_OUT_DIR=… cargo test -p ay-proof --lib -- \
//!     complete_blast::corpus::render_corpus_certificates --nocapture
//! ```
//!
//! The SMT-LIB reader here is deliberately tiny and local: it accepts exactly
//! the closed QF_BV fragment the target corpus uses, so the harness never
//! depends on the solver's own frontend elaboration.

use super::*;
use ay_core::kani_compat::DetHashMap;
use ay_core::{Sort, Symbol, TermData, TermStore};
use num_bigint::BigInt;
use std::time::Instant;

#[derive(Debug, Clone, PartialEq, Eq)]
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

fn tokenize(input: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut current = String::new();
    for line in input.lines() {
        let line = line.split(';').next().unwrap_or("");
        for ch in line.chars() {
            match ch {
                '(' | ')' => {
                    if !current.is_empty() {
                        tokens.push(std::mem::take(&mut current));
                    }
                    tokens.push(ch.to_string());
                }
                c if c.is_whitespace() => {
                    if !current.is_empty() {
                        tokens.push(std::mem::take(&mut current));
                    }
                }
                c => current.push(c),
            }
        }
        if !current.is_empty() {
            tokens.push(std::mem::take(&mut current));
        }
    }
    tokens
}

fn parse_all(tokens: &[String]) -> Vec<Sexp> {
    let mut position = 0;
    let mut out = Vec::new();
    while position < tokens.len() {
        out.push(parse_one(tokens, &mut position));
    }
    out
}

fn parse_one(tokens: &[String], position: &mut usize) -> Sexp {
    let token = tokens[*position].clone();
    *position += 1;
    if token == "(" {
        let mut items = Vec::new();
        while tokens[*position] != ")" {
            items.push(parse_one(tokens, position));
        }
        *position += 1;
        return Sexp::List(items);
    }
    Sexp::Atom(token)
}

struct Reader<'t> {
    terms: &'t mut TermStore,
    scope: DetHashMap<String, TermId>,
}

impl Reader<'_> {
    fn width(&self, term: TermId) -> Option<u32> {
        self.terms.sort(term).bitvec_width()
    }

    fn term(&mut self, sexp: &Sexp) -> Option<TermId> {
        match sexp {
            Sexp::Atom(name) => {
                if let Some(bits) = name.strip_prefix("#b") {
                    let width = u32::try_from(bits.len()).ok()?;
                    let value = BigInt::parse_bytes(bits.as_bytes(), 2)?;
                    return Some(self.terms.mk_bitvec(value, width));
                }
                if name == "true" || name == "false" {
                    return Some(self.terms.mk_bool(name == "true"));
                }
                self.scope.get(name).copied()
            }
            Sexp::List(items) => {
                if let [Sexp::Atom(underscore), Sexp::Atom(literal), Sexp::Atom(width)] =
                    items.as_slice()
                {
                    if underscore == "_" {
                        let value = literal.strip_prefix("bv")?;
                        let value = BigInt::parse_bytes(value.as_bytes(), 10)?;
                        return Some(self.terms.mk_bitvec(value, width.parse().ok()?));
                    }
                }
                let head = items.first()?;
                let args: Vec<TermId> = items[1..]
                    .iter()
                    .map(|item| self.term(item))
                    .collect::<Option<_>>()?;
                match head {
                    Sexp::Atom(name) => self.application(name, &args),
                    Sexp::List(indexed) => {
                        let Sexp::Atom(underscore) = &indexed[0] else {
                            return None;
                        };
                        if underscore != "_" {
                            return None;
                        }
                        let Sexp::Atom(name) = &indexed[1] else {
                            return None;
                        };
                        let indices: Vec<u32> = indexed[2..]
                            .iter()
                            .map(|item| match item {
                                Sexp::Atom(text) => text.parse().ok(),
                                Sexp::List(_) => None,
                            })
                            .collect::<Option<_>>()?;
                        self.indexed_application(name, &indices, &args)
                    }
                }
            }
        }
    }

    fn application(&mut self, name: &str, args: &[TermId]) -> Option<TermId> {
        match name {
            "and" | "or" | "xor" | "=>" => {
                Some(self.terms.mk_app(Symbol::named(name), args, Sort::Bool))
            }
            "not" => Some(self.terms.mk_not_raw(args[0])),
            "=" | "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge" => {
                Some(self.terms.mk_app(Symbol::named(name), args, Sort::Bool))
            }
            "ite" => Some(self.terms.mk_ite_raw(args[0], args[1], args[2])),
            "concat" => {
                let mut total = 0;
                for arg in args {
                    total += self.width(*arg)?;
                }
                Some(
                    self.terms
                        .mk_app(Symbol::named("concat"), args, Sort::bitvec(total)),
                )
            }
            "bvadd" | "bvsub" | "bvmul" | "bvand" | "bvor" | "bvxor" | "bvshl" | "bvlshr"
            | "bvashr" | "bvnot" | "bvneg" | "bvudiv" | "bvurem" => {
                let width = self.width(args[0])?;
                Some(
                    self.terms
                        .mk_app(Symbol::named(name), args, Sort::bitvec(width)),
                )
            }
            _ => None,
        }
    }

    fn indexed_application(
        &mut self,
        name: &str,
        indices: &[u32],
        args: &[TermId],
    ) -> Option<TermId> {
        let width = match (name, indices) {
            ("extract", [high, low]) => high.checked_sub(*low)?.checked_add(1)?,
            ("zero_extend" | "sign_extend" | "repeat", [by]) => self.width(args[0])? + by,
            ("rotate_left" | "rotate_right", [_]) => self.width(args[0])?,
            _ => return None,
        };
        Some(self.terms.mk_app(
            Symbol::indexed(name, indices.to_vec()),
            args,
            Sort::bitvec(width),
        ))
    }
}

/// Parse one closed QF_BV problem into its single assertion.
pub(super) fn read_problem(source: &str) -> Option<(TermStore, TermId)> {
    let mut terms = TermStore::new();
    let mut scope = DetHashMap::default();
    let commands = parse_all(&tokenize(source));
    let mut assertion = None;
    for command in &commands {
        let Sexp::List(items) = command else {
            continue;
        };
        let Some(Sexp::Atom(head)) = items.first() else {
            continue;
        };
        match head.as_str() {
            "declare-const" => {
                let (Sexp::Atom(name), Sexp::List(sort)) = (&items[1], &items[2]) else {
                    return None;
                };
                let [Sexp::Atom(underscore), Sexp::Atom(bitvec), Sexp::Atom(width)] =
                    sort.as_slice()
                else {
                    return None;
                };
                if underscore != "_" || bitvec != "BitVec" {
                    return None;
                }
                let width: u32 = width.parse().ok()?;
                let term = terms.mk_var(name.clone(), Sort::bitvec(width));
                scope.insert(name.clone(), term);
            }
            "assert" => {
                let mut reader = Reader {
                    terms: &mut terms,
                    scope: scope.clone(),
                };
                let term = reader.term(&items[1])?;
                if assertion.is_some() {
                    return None;
                }
                assertion = Some(term);
            }
            _ => {}
        }
    }
    assertion.map(|a| (terms, a))
}

#[test]
fn reader_preserves_boolean_and_bit_vector_ite_sorts() {
    let declarations = "(declare-const x (_ BitVec 4))\n\
                        (declare-const y (_ BitVec 4))\n";

    let boolean_source = format!("{declarations}(assert (ite (= x y) (= x x) (= y y)))\n");
    let (boolean_terms, boolean_ite) = read_problem(&boolean_source).expect("Boolean ite");
    assert!(matches!(boolean_terms.get(boolean_ite), TermData::Ite(..)));
    assert_eq!(boolean_terms.sort(boolean_ite), &Sort::Bool);

    let bit_vector_source = format!("{declarations}(assert (= (ite (= x y) x y) x))\n");
    let (bit_vector_terms, equality) = read_problem(&bit_vector_source).expect("bit-vector ite");
    let TermData::App(_, equality_args) = bit_vector_terms.get(equality) else {
        panic!("bit-vector ite equality");
    };
    let bit_vector_ite = equality_args[0];
    assert!(matches!(
        bit_vector_terms.get(bit_vector_ite),
        TermData::Ite(..)
    ));
    assert_eq!(bit_vector_terms.sort(bit_vector_ite), &Sort::bitvec(4));
}

/// The problem text a checker reads, with solver options and `exit` removed.
fn checker_problem(source: &str) -> String {
    source
        .lines()
        .filter(|line| {
            let trimmed = line.trim();
            !trimmed.starts_with("(set-option") && !trimmed.starts_with("(exit)")
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Every `.smt2` problem in `directory` whose name contains `CBB_ONLY`, as
/// `(name, source)` in name order.
fn corpus_problems(directory: &str) -> Vec<(String, String)> {
    let mut entries: Vec<_> = std::fs::read_dir(directory)
        .expect("corpus directory")
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|e| e == "smt2"))
        .collect();
    entries.sort();
    let only = std::env::var("CBB_ONLY").ok();
    entries
        .into_iter()
        .map(|path| {
            let name = path.file_stem().unwrap().to_string_lossy().to_string();
            (name, path)
        })
        .filter(|(name, _)| {
            only.as_ref()
                .is_none_or(|filter| name.contains(filter.as_str()))
        })
        .map(|(name, path)| {
            let source = std::fs::read_to_string(&path).expect("readable problem");
            (name, source)
        })
        .collect()
}

/// Render one certificate per corpus problem named by `CBB_SMT2_DIR`.
///
/// A no-op when that variable is unset, which is the ordinary case: the
/// corpus lives outside the repository. Selection by environment rather than
/// by `#[ignore]` keeps the harness runnable without a disabled test in owned
/// source — the same choice `ay-core`'s serde-bignum regenerators record.
#[test]
fn render_corpus_certificates() {
    let Ok(directory) = std::env::var("CBB_SMT2_DIR") else {
        return;
    };
    let out = std::env::var("CBB_OUT_DIR").unwrap_or_else(|_| "/tmp/cbb".to_string());
    std::fs::create_dir_all(&out).expect("output directory");
    for (name, source) in corpus_problems(&directory) {
        let started = Instant::now();
        let Some((terms, assertion)) = read_problem(&source) else {
            println!("{name}\tPARSE-REFUSED\t0\t0.000");
            continue;
        };
        let mut terms = terms;
        let literal = terms.mk_not_raw(assertion);
        let printer = AlethePrinter::new(&terms);
        let rendered = printer.format_bv_complete_blast_refutation(ProofId(1), &[literal]);
        let elapsed = started.elapsed().as_secs_f64();
        match rendered {
            None => println!("{name}\tREFUSED\t0\t{elapsed:.3}"),
            Some(document) => {
                let proof = format!(
                    "(assume t0 {})\n{document}\n(step t2 (cl) :rule resolution :premises (t1 t0))\n",
                    printer.format_term(assertion)
                );
                let payload = serde_json::json!({
                    "type": "alethe_certificate",
                    "version": "1.0",
                    "problem": checker_problem(&source),
                    "proof": proof,
                });
                let target = std::path::Path::new(&out).join(format!("{name}.json"));
                std::fs::write(&target, serde_json::to_string(&payload).unwrap())
                    .expect("writable certificate");
                println!("{name}\tRENDERED\t{}\t{elapsed:.3}", proof.len());
            }
        }
    }
}

/// Print the strict checker's verdict on the `BvBitBlast` lemma `(cl (not A))`
/// of every problem in `CBB_CHECK_DIR` (filtered by `CBB_ONLY`), with its
/// refusal reason and time: the question the authored bit-blast refutation
/// asks, without a solve around it. A no-op without the variable, like
/// [`render_corpus_certificates`].
///
/// ```text
/// CBB_CHECK_DIR=… targo --unverified test -p ay-proof --lib --release -- \
///     complete_blast::corpus::check_corpus_lemmas --nocapture
/// ```
#[test]
fn check_corpus_lemmas() {
    let Ok(directory) = std::env::var("CBB_CHECK_DIR") else {
        return;
    };
    for (name, source) in corpus_problems(&directory) {
        let started = Instant::now();
        let Some((mut terms, assertion)) = read_problem(&source) else {
            println!("{name}\tPARSE-REFUSED");
            continue;
        };
        let literal = terms.mk_not_raw(assertion);
        let verdict =
            crate::checker::bv_bitblast::validate_bv_bitblast(&terms, ProofId(1), &[literal], None);
        let elapsed = started.elapsed().as_secs_f64();
        println!("{name}\t{verdict:?}\t{elapsed:.3}");
    }
}
