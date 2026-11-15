// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The proof document: steps, subproofs, gate definitions derived on demand,
//! and locally checked Boolean steps.

use super::super::emission_progress::EmissionProgress;
use super::cdcl;
use super::print::{b36, Printer};
use super::term::{Op, Terms, T};
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use std::fmt::Write;

/// A step of the document (index into `clauses`).
pub(crate) type S = u32;

/// A premise: an emitted step, or one defining clause of a gate, emitted on
/// first use.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Prem {
    Step(S),
    Gate(T, u8),
}

pub(crate) enum Arg {
    Int(usize),
    Term(T),
}

pub(crate) struct GateDef {
    rule: &'static str,
    arg: Option<usize>,
    lits: Vec<T>,
}

impl GateDef {
    pub(crate) fn lits(&self) -> &[T] {
        &self.lits
    }
}

pub(crate) struct Proof<'a> {
    pub(crate) t: Terms,
    pr: Printer,
    pub(crate) out: String,
    id_prefix: String,
    clauses: Vec<Vec<T>>,
    tseitin: HashMap<(T, u8), S>,
    scopes: Vec<Vec<(T, u8)>>,
    /// Work bound on local refutations; exhausted means the document is abandoned.
    pub(crate) budget: u64,
    /// The original printer owner; cloning its handle never renews permission.
    progress: EmissionProgress<'a>,
    named: HashMap<S, String>,
    /// The spelling of the externally named step's clause, when the caller
    /// prints that clause itself.
    pub(crate) named_spelling: Option<String>,
    /// Words every bit-blaster keeps closed while it is set: the schoolbook's
    /// limbs, whose bits it reads as their own `@bit_of` projections even
    /// when a limb is itself an `extract`.
    pub(crate) opaque: HashSet<T>,
}

impl<'a> Proof<'a> {
    #[cfg(test)]
    pub(crate) fn new(id_prefix: String, name_prefix: String) -> Self {
        Self::new_with_progress(id_prefix, name_prefix, EmissionProgress::default())
    }

    pub(crate) fn new_with_progress(
        id_prefix: String,
        name_prefix: String,
        progress: EmissionProgress<'a>,
    ) -> Self {
        Proof {
            t: Terms::new(),
            pr: Printer::new(name_prefix),
            out: String::new(),
            id_prefix,
            clauses: Vec::new(),
            tseitin: HashMap::default(),
            scopes: vec![Vec::new()],
            budget: 400_000_000,
            progress,
            named: HashMap::default(),
            named_spelling: None,
            opaque: HashSet::default(),
        }
    }

    /// An observation is a refusal boundary, not a fresh local budget.
    pub(crate) fn observe(&self) -> Option<()> {
        self.progress.poll().then_some(())
    }

    pub(crate) fn progress(&self) -> &EmissionProgress<'a> {
        &self.progress
    }

    pub(crate) fn id(&self, s: S) -> String {
        if let Some(name) = self.named.get(&s) {
            return name.clone();
        }
        format!("{}{}", self.id_prefix, b36(u64::from(s)))
    }

    /// Emit a step under an externally chosen id.
    pub(crate) fn emit_named(&mut self, id: &str, clause: &[T], rule: &str, prem: &[S]) -> S {
        let cl = match self.named_spelling.take() {
            Some(spelled) => spelled,
            None => self.render_clause(clause),
        };
        let s = self.new_step(clause);
        self.named.insert(s, id.to_string());
        self.write_step(s, &cl, rule, prem, &[], "");
        s
    }

    pub(crate) fn clause(&self, s: S) -> &[T] {
        &self.clauses[s as usize]
    }

    /// The single literal of a unit step.
    pub(crate) fn unit(&self, s: S) -> T {
        self.clauses[s as usize]
            .last()
            .copied()
            .unwrap_or(self.t.tt)
    }

    pub(crate) fn render(&mut self, t: T) -> String {
        self.pr.ensure(&self.t, t, &mut self.out);
        self.pr.render(&self.t, t)
    }

    /// A clause literal with its head spelled out (its arguments by name)
    /// where the printer's surface judges read that head off the printed
    /// command: the disjunction of a unit clause (the only premise `or`
    /// splits, judged against the premise's printed term, whose conclusion
    /// names each disjunct) and, under `poly_simp`, an equality. A defined
    /// name in that position reads as no application at all and is refused.
    fn render_literal(&mut self, l: T, unit: bool, spell_eq: bool) -> String {
        let head = match self.t.op(l) {
            Op::Or if unit => "or",
            Op::Eq if spell_eq => "=",
            _ => return self.render(l),
        };
        let mut s = format!("({head}");
        for a in self.t.args(l).to_vec() {
            let r = self.render(a);
            s.push(' ');
            s.push_str(&r);
        }
        s.push(')');
        s
    }

    fn render_clause_with(&mut self, lits: &[T], spell_eq: bool) -> String {
        let mut s = String::from("(cl");
        for &l in lits {
            let r = self.render_literal(l, lits.len() == 1, spell_eq);
            s.push(' ');
            s.push_str(&r);
        }
        s.push(')');
        s
    }

    fn render_clause(&mut self, lits: &[T]) -> String {
        self.render_clause_with(lits, false)
    }

    fn new_step(&mut self, clause: &[T]) -> S {
        self.clauses.push(clause.to_vec());
        (self.clauses.len() - 1) as S
    }

    pub(crate) fn emit(&mut self, clause: &[T], rule: &str, prem: &[S], args: &[Arg]) -> S {
        let cl = self.render_clause_with(clause, rule == "poly_simp");
        let mut arg_text = Vec::new();
        for a in args {
            match a {
                Arg::Int(i) => arg_text.push(i.to_string()),
                Arg::Term(t) => arg_text.push(self.render(*t)),
            }
        }
        let s = self.new_step(clause);
        self.write_step(s, &cl, rule, prem, &arg_text, "");
        s
    }

    /// The one writer of a `:rule`. Its names are `&'static str` arguments
    /// spelled across this subtree, so the bound is here: a name outside
    /// [`ay_core::CHECKABLE_ALETHE_RULES`] (which the wire-rule probe covers)
    /// is never written and the step is the honest hole instead.
    /// `RULE_BOUNDED_EMITTERS` in `tests/wire_rule_coverage.rs` asserts the
    /// bound is still here.
    fn write_step(&mut self, s: S, cl: &str, rule: &str, prem: &[S], args: &[String], extra: &str) {
        let id = self.id(s);
        let rule = if ay_core::is_checkable_alethe_rule(rule) {
            rule
        } else {
            ay_core::UNPROVED_STEP_RULE
        };
        let _ = write!(self.out, "(step {id} {cl} :rule {rule}");
        if !prem.is_empty() {
            let ps: Vec<String> = prem.iter().map(|&p| self.id(p)).collect();
            let _ = write!(self.out, " :premises ({})", ps.join(" "));
        }
        if !args.is_empty() {
            let _ = write!(self.out, " :args ({})", args.join(" "));
        }
        let _ = writeln!(self.out, "{extra})");
    }

    pub(crate) fn assume(&mut self, t: T) -> S {
        let r = self.render(t);
        let s = self.new_step(&[t]);
        let id = self.id(s);
        let _ = writeln!(self.out, "(assume {id} {r})");
        s
    }

    /// Open a subproof; with variables it is a `bind` context.
    pub(crate) fn anchor(&mut self, vars: &[T]) -> S {
        let s = self.new_step(&[]);
        let id = self.id(s);
        if vars.is_empty() {
            let _ = writeln!(self.out, "(anchor :step {id})");
        } else {
            let mut vs = Vec::new();
            for &v in vars {
                let name = self.pr.render(&self.t, v);
                vs.push(format!(
                    "({name} {})",
                    super::print::sort_str(self.t.sort(v))
                ));
            }
            let _ = writeln!(self.out, "(anchor :step {id} :args ({}))", vs.join(" "));
        }
        self.scopes.push(Vec::new());
        s
    }

    /// Close the subproof opened by `anchor` with its concluding step.
    pub(crate) fn close(&mut self, s: S, clause: &[T], rule: &str, discharge: &[S]) -> S {
        if let Some(keys) = self.scopes.pop() {
            for k in keys {
                self.tseitin.remove(&k);
            }
        }
        let cl = self.render_clause(clause);
        self.clauses[s as usize] = clause.to_vec();
        let extra = if discharge.is_empty() {
            String::new()
        } else {
            let ds: Vec<String> = discharge.iter().map(|&d| self.id(d)).collect();
            format!(" :discharge ({})", ds.join(" "))
        };
        self.write_step(s, &cl, rule, &[], &[], &extra);
        s
    }

    pub(crate) fn gate_defs(&mut self, g: T) -> Vec<GateDef> {
        let a = self.t.args(g).to_vec();
        let ng = self.t.not(g);
        let mut out = Vec::new();
        let def =
            |rule: &'static str, arg: Option<usize>, lits: Vec<T>| GateDef { rule, arg, lits };
        match self.t.op(g).clone() {
            Op::And => {
                for (i, &x) in a.iter().enumerate() {
                    out.push(def("and_pos", Some(i), vec![ng, x]));
                }
                let mut l = vec![g];
                for &x in &a {
                    l.push(self.t.not(x));
                }
                out.push(def("and_neg", None, l));
            }
            Op::Or => {
                let mut l = vec![ng];
                l.extend(&a);
                out.push(def("or_pos", None, l));
                for (i, &x) in a.iter().enumerate() {
                    let nx = self.t.not(x);
                    out.push(def("or_neg", Some(i), vec![g, nx]));
                }
            }
            Op::Xor | Op::Eq => {
                let (p, q) = (a[0], a[1]);
                let (np, nq) = (self.t.not(p), self.t.not(q));
                if matches!(self.t.op(g), Op::Xor) {
                    out.push(def("xor_pos1", None, vec![ng, p, q]));
                    out.push(def("xor_pos2", None, vec![ng, np, nq]));
                    out.push(def("xor_neg1", None, vec![g, p, nq]));
                    out.push(def("xor_neg2", None, vec![g, np, q]));
                } else {
                    out.push(def("equiv_pos1", None, vec![ng, p, nq]));
                    out.push(def("equiv_pos2", None, vec![ng, np, q]));
                    out.push(def("equiv_neg1", None, vec![g, np, nq]));
                    out.push(def("equiv_neg2", None, vec![g, p, q]));
                }
            }
            Op::Ite => {
                let (c, p, q) = (a[0], a[1], a[2]);
                let (nc, np, nq) = (self.t.not(c), self.t.not(p), self.t.not(q));
                out.push(def("ite_pos1", None, vec![ng, c, q]));
                out.push(def("ite_pos2", None, vec![ng, nc, p]));
                out.push(def("ite_neg1", None, vec![g, c, nq]));
                out.push(def("ite_neg2", None, vec![g, nc, np]));
            }
            Op::True => out.push(def("true", None, vec![g])),
            Op::False => out.push(def("false", None, vec![ng])),
            _ => {}
        }
        out
    }

    /// Virtual premises for every defining clause of gate `g`.
    pub(crate) fn gate(&mut self, g: T) -> Vec<Prem> {
        let n = self.gate_defs(g).len();
        (0..n).map(|k| Prem::Gate(g, k as u8)).collect()
    }

    pub(crate) fn materialize(&mut self, p: Prem) -> Option<S> {
        self.observe()?;
        match p {
            Prem::Step(s) => Some(s),
            Prem::Gate(g, k) => {
                if let Some(&s) = self.tseitin.get(&(g, k)) {
                    return Some(s);
                }
                let defs = self.gate_defs(g);
                let d = defs.get(k as usize)?;
                let args: Vec<Arg> = d.arg.map(Arg::Int).into_iter().collect();
                let s = self.emit(&d.lits.clone(), d.rule, &[], &args);
                self.tseitin.insert((g, k), s);
                if let Some(top) = self.scopes.last_mut() {
                    top.push((g, k));
                }
                self.observe()?;
                Some(s)
            }
        }
    }

    pub(crate) fn lits_of(&mut self, p: Prem) -> Vec<T> {
        match p {
            Prem::Step(s) => self.clauses[s as usize].clone(),
            Prem::Gate(g, k) => {
                let defs = self.gate_defs(g);
                defs.into_iter()
                    .nth(k as usize)
                    .map(|d| d.lits)
                    .unwrap_or_default()
            }
        }
    }

    /// Derive `target` from `prems` by a checked `resolution` (when it is a
    /// reverse unit propagation consequence) or a `drup` step carrying the
    /// learned clauses of a local CDCL refutation.
    pub(crate) fn derive(&mut self, target: &[T], prems: &[Prem], decide: &[T]) -> Option<S> {
        self.observe()?;
        let mut db = Vec::with_capacity(prems.len());
        for &p in prems {
            self.observe()?;
            let lits = self.lits_of(p);
            db.push(lits.iter().map(|&l| self.t.lit_of(l)).collect::<Vec<_>>());
        }
        let tgt: Vec<(T, bool)> = target.iter().map(|&l| self.t.lit_of(l)).collect();
        let dv: Vec<T> = decide.iter().map(|&l| self.t.lit_of(l).0).collect();
        let progress = self.progress.clone();
        let res = cdcl::refute(&db, &tgt, &dv, &mut self.budget, &progress)?;
        self.observe()?;
        let mut used = Vec::new();
        for &k in &res.used {
            self.observe()?;
            if let Some(&p) = prems.get(k) {
                let s = self.materialize(p)?;
                if !used.contains(&s) {
                    used.push(s);
                }
            }
        }
        if res.learned.is_empty() && used.len() >= 2 {
            let step = self.emit(target, "resolution", &used, &[]);
            self.observe()?;
            return Some(step);
        }
        if used.is_empty() || res.learned.is_empty() {
            return self.drup_step(target, &tgt, &used, &res.learned);
        }
        // each learned clause as its own RUP-checked resolution step (no clause terms as arguments)
        let mut prev = used;
        for lem in &res.learned {
            self.observe()?;
            let mut lits: Vec<T> = target.to_vec();
            for &(a, pol) in lem {
                if tgt.iter().all(|&(b, _)| b != a) {
                    lits.push(if pol { a } else { self.t.not(a) });
                }
            }
            let s = self.emit(&lits, "resolution", &prev, &[]);
            prev.push(s);
        }
        let step = self.emit(target, "resolution", &prev, &[]);
        self.observe()?;
        Some(step)
    }

    fn drup_step(
        &mut self,
        target: &[T],
        tgt: &[(T, bool)],
        used: &[S],
        learned: &[Vec<(T, bool)>],
    ) -> Option<S> {
        self.observe()?;
        let mut args = Vec::new();
        for lem in learned {
            self.observe()?;
            let mut lits: Vec<T> = target.to_vec();
            for &(a, p) in lem {
                if tgt.iter().all(|&(b, _)| b != a) {
                    lits.push(if p { a } else { self.t.not(a) });
                }
            }
            args.push(self.render_clause(&lits));
        }
        args.push(self.render_clause(target));
        let cl = self.render_clause(target);
        let s = self.new_step(target);
        self.write_step(s, &cl, "drup", used, &args, "");
        self.observe()?;
        Some(s)
    }
}

#[cfg(test)]
#[path = "proof/rup_argument_tests.rs"]
mod rup_argument_tests;
