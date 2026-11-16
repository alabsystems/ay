// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded, independently replayable concat/extract/selector identities.
//!
//! Every source node is validated, including discarded concat children. ITE
//! distribution is derived by discharging both cases; it is never an axiom.
//! Matching normal forms only chooses a derivation, and the emitted Alethe
//! steps remain subject to the consumer's independent checker.

mod addition;
#[cfg(test)]
mod addition_tests;
#[cfg(test)]
mod aggregate_tests;
mod boolean;
mod boolean_cases;
mod boolean_reduce;
mod circuit;
mod complement;
#[cfg(test)]
mod complement_tests;
mod conditional;
mod congruence;
mod context;
mod guarded;
mod guarded_range;
#[cfg(test)]
mod guarded_tests;
mod literal_spelling;
mod lower;
#[cfg(test)]
mod masked_tests;
#[cfg(test)]
mod nested_connective_tests;
mod partition;
mod product;
mod shift;
mod sparse;
#[cfg(test)]
mod sparse_tests;
mod surface_add_zero;
#[cfg(test)]
mod tests;
mod wire;
#[cfg(test)]
mod wire_tests;
#[cfg(test)]
mod zero_extend_zero_tests;

use super::{AlethePrinter, CheckableRule};
use ay_core::kani_compat::DetHashMap;
use ay_core::{ProofId, Sort, Symbol, TermData, TermId};

const MAX_WIDTH: usize = 128;
const MAX_NODES: usize = 512;
const MAX_DEPTH: usize = 64;
// A complete 16-byte aggregate includes separately checked byte operations
// and address carries. Bound their combined document, including definitions;
// the caller additionally charges it against its global emission budget.
const MAX_TEXT: usize = 64 * 1024 * 1024;
const MAX_SPELLINGS: usize = 65_536;

#[derive(Clone, Copy)]
enum DefinitionMode {
    Nullary,
    /// Open universal parameters must not occur free in a nullary alias.
    Inline,
}

#[derive(Clone)]
struct Equality {
    left: String,
    right: String,
    step: String,
}

#[derive(Clone)]
struct Value {
    equality: Equality,
    // Little endian, as required by Alethe's @bbterm.
    bits: Vec<String>,
}

struct PackedProof<'a, 'terms> {
    printer: &'a AlethePrinter<'terms>,
    prefix: String,
    next: usize,
    visited: usize,
    out: String,
    definitions: String,
    definition_mode: DefinitionMode,
    // A universal child shares this printer and the enclosing document cap.
    // Its private text cannot consume a second MAX_TEXT grant.
    text_base_bytes: usize,
    spellings: DetHashMap<String, String>,
    /// The body of every `define-fun` in `spellings`, by name.
    definition_bodies: DetHashMap<String, String>,
    definition_prefix: String,
    vectors: DetHashMap<TermId, Value>,
    booleans: DetHashMap<TermId, Equality>,
    boolean_lemmas: DetHashMap<(String, String), Equality>,
    arrays: DetHashMap<TermId, Vec<sparse::Write>>,
    /// Opaque-word mode (`format_bv_packed_opaque_identity`): every
    /// bit-vector term outside the wiring operators is one `bitblast_var`
    /// leaf, and every Boolean term `boolean` does not read is one `refl`
    /// leaf.
    opaque_words: bool,
}

impl AlethePrinter<'_> {
    pub(super) fn format_bv_packed_identity(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        let proof = PackedProof::new(self, id)?;
        self.format_bv_packed_identity_with(id, clause, proof)
    }

    /// [`Self::format_bv_packed_identity`] for an identity that holds by
    /// WIRING alone: `extract`, `concat`, `zero_extend`, `sign_extend` and
    /// constant-branch `ite` over operands taken as opaque words, such as
    /// `(= ((_ extract 31 0) ((_ zero_extend 32) (bvmul a b))) (bvmul a b))`.
    /// Each maximal operand outside those operators is named bit by bit with
    /// `bitblast_var`, which Carcara checks for any bit-vector term (it
    /// rebuilds `(@bbterm ((_ @bit_of 0) t) ..)` from `t` itself), and a
    /// Boolean condition the lane does not read is one `refl` leaf. The two
    /// sides must still produce the SAME bit spellings, so an identity that
    /// needs the operand's arithmetic fails here and is left to the exact
    /// lanes; one that does not is never charged a multiplier circuit.
    pub(super) fn format_bv_packed_opaque_identity(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        let mut proof = PackedProof::with_prefix(
            self,
            format!("{id}.opaque"),
            &format!("__ay_opaque_{}_", id.0),
        )?;
        proof.opaque_words = true;
        self.format_bv_packed_identity_with(id, clause, proof)
    }

    fn format_bv_packed_identity_with<'p>(
        &'p self,
        id: ProofId,
        clause: &[TermId],
        mut proof: PackedProof<'p, '_>,
    ) -> Option<String> {
        let [root] = clause else { return None };
        let TermData::App(Symbol::Named(op), args) = self.terms.get(*root) else {
            return None;
        };
        let [left, right] = args.as_slice() else {
            return None;
        };
        if op != "=" || self.terms.sort(*root) != &Sort::Bool {
            return None;
        }
        let left = proof.vector(*left, 0)?;
        let right = proof.vector(*right, 0)?;
        if left.bits != right.bits
            || self.format_term(*root)
                != format!("(= {} {})", left.equality.left, right.equality.left)
        {
            return None;
        }
        let reverse = proof.equality(
            &right.equality.right,
            &right.equality.left,
            "symm",
            &[&right.equality.step],
        )?;
        proof.named_step(
            &id.to_string(),
            &format!("(= {} {})", left.equality.left, right.equality.left),
            "trans",
            &[&left.equality.step, &reverse.step],
            "",
        )?;
        proof.definitions.push_str(&proof.out);
        Some(proof.definitions)
    }
}

impl<'a, 'terms> PackedProof<'a, 'terms> {
    fn new(printer: &'a AlethePrinter<'terms>, id: ProofId) -> Option<Self> {
        Self::with_prefix(
            printer,
            format!("{id}.packed"),
            &format!("__ay_packed_{}_", id.0),
        )
    }

    fn with_prefix(
        printer: &'a AlethePrinter<'terms>,
        prefix: String,
        definition_prefix: &str,
    ) -> Option<Self> {
        let definition_prefix = (0..32)
            .map(|nonce| format!("{definition_prefix}{nonce}!"))
            .find(|prefix| !printer.proof_definition_name_collision(prefix))?;
        Some(Self::empty(printer, prefix, definition_prefix))
    }

    fn empty(
        printer: &'a AlethePrinter<'terms>,
        prefix: String,
        definition_prefix: String,
    ) -> Self {
        Self {
            printer,
            prefix,
            next: 0,
            visited: 0,
            out: String::new(),
            definitions: String::new(),
            definition_mode: DefinitionMode::Nullary,
            text_base_bytes: 0,
            spellings: DetHashMap::default(),
            definition_bodies: DetHashMap::default(),
            definition_prefix,
            vectors: DetHashMap::default(),
            booleans: DetHashMap::default(),
            boolean_lemmas: DetHashMap::default(),
            arrays: DetHashMap::default(),
            opaque_words: false,
        }
    }

    // Parent definition names end in decimal IDs. This descendant uses a
    // distinct letter suffix and a fresh parent ID, so it cannot collide with
    // parent/sibling definitions. The parent's already-checked prefix also
    // excludes every source symbol, binder and override; no new arena scan.
    fn fresh_universal_child(&mut self) -> Option<Self> {
        let serial = self.next;
        let prefix = self.fresh();
        let mut child = Self::empty(
            self.printer,
            format!("{prefix}.zx"),
            format!("{}zx{serial}!", self.definition_prefix),
        );
        // The maintained binder guard conservatively scopes anchor variables
        // over the entire proof. Inline this finite theorem instead of
        // introducing nullary definitions with free universal parameters.
        child.definition_mode = DefinitionMode::Inline;
        child.text_base_bytes = self
            .text_base_bytes
            .checked_add(self.out.len())?
            .checked_add(self.definitions.len())?;
        Some(child)
    }
}

impl PackedProof<'_, '_> {
    fn enter(&mut self, depth: usize) -> Option<()> {
        if self.printer.work_budget_exhausted() {
            return None;
        }
        self.visited = self.visited.checked_add(1)?;
        (depth <= MAX_DEPTH && self.visited <= MAX_NODES).then_some(())
    }

    fn fresh(&mut self) -> String {
        let name = format!("{}.{}", self.prefix, self.next);
        self.next += 1;
        name
    }

    fn append(&mut self, text: &str) -> Option<()> {
        if self
            .text_base_bytes
            .checked_add(self.out.len())?
            .checked_add(self.definitions.len())?
            .checked_add(text.len())?
            > MAX_TEXT
        {
            return None;
        }
        self.printer.charge(text.len() as u64);
        if self.printer.work_budget_exhausted() {
            return None;
        }
        self.out.push_str(text);
        Some(())
    }

    fn named_step(
        &mut self,
        name: &str,
        clause: &str,
        rule: &str,
        premises: &[&str],
        extra: &str,
    ) -> Option<()> {
        let rule = CheckableRule::new(rule)?;
        self.named_step_with_rule(name, clause, rule, premises, extra)
    }

    fn named_step_with_rule(
        &mut self,
        name: &str,
        clause: &str,
        rule: CheckableRule,
        premises: &[&str],
        extra: &str,
    ) -> Option<()> {
        let premises = if premises.is_empty() {
            String::new()
        } else {
            format!(" :premises ({})", premises.join(" "))
        };
        self.append(&format!(
            "(step {name} (cl {clause}) :rule {rule}{premises}{extra})\n"
        ))
    }

    fn step(&mut self, clause: &str, rule: &str, premises: &[&str]) -> Option<String> {
        let name = self.fresh();
        self.named_step(&name, clause, rule, premises, "")?;
        Some(name)
    }

    fn equality(
        &mut self,
        left: &str,
        right: &str,
        rule: &str,
        premises: &[&str],
    ) -> Option<Equality> {
        if let Some(gate) =
            nested_connective_simplification(rule, left, right, |name| self.definition_body(name))
        {
            return self.nested_connective_equality(gate, left, right, rule);
        }
        let step = self.step(
            &format!("(= {} {})", self.spelling(left), self.spelling(right)),
            rule,
            premises,
        )?;
        Some(Equality {
            left: left.into(),
            right: right.into(),
            step,
        })
    }

    fn spelling<'a>(&'a self, term: &'a str) -> &'a str {
        self.spellings.get(term).map_or(term, String::as_str)
    }

    fn define_word(&mut self, bits: &[String]) -> Option<String> {
        let term = bbterm(bits);
        self.define_term(&term, &format!("(_ BitVec {})", bits.len()))
    }

    fn define_term(&mut self, term: &str, sort: &str) -> Option<String> {
        if matches!(self.definition_mode, DefinitionMode::Inline) {
            // Admit the returned copy before cloning it. The eventual printed
            // occurrences are charged again by append; there is no new grant.
            if self
                .text_base_bytes
                .checked_add(self.out.len())?
                .checked_add(self.definitions.len())?
                .checked_add(term.len())?
                > MAX_TEXT
            {
                return None;
            }
            self.printer.charge(term.len() as u64);
            if self.printer.work_budget_exhausted() {
                return None;
            }
            return Some(term.into());
        }
        if let Some(name) = self.spellings.get(term) {
            return Some(name.clone());
        }
        if self.spellings.len() >= MAX_SPELLINGS {
            return None;
        }
        let name = format!("{}{}", self.definition_prefix, self.next);
        self.next += 1;
        let declaration = format!("(define-fun {name} () {sort} {term})\n");
        if self
            .text_base_bytes
            .checked_add(self.out.len())?
            .checked_add(self.definitions.len())?
            .checked_add(declaration.len())?
            > MAX_TEXT
        {
            return None;
        }
        self.printer.charge(declaration.len() as u64);
        if self.printer.work_budget_exhausted() {
            return None;
        }
        self.definitions.push_str(&declaration);
        self.spellings.insert(term.into(), name.clone());
        self.definition_bodies.insert(name.clone(), term.into());
        Some(name)
    }

    /// `(= source survivor)` by `rule` (`and_simplify` / `or_simplify`), where
    /// `survivor` is the ONE argument of `source`'s `op` application that
    /// survives. The pinned checker compares the surviving arguments with the
    /// ARGUMENTS of an `op`-headed result (carcara `generic_and_or_simplify`),
    /// so when `survivor` is itself — or names, through a proof-local
    /// `define-fun` — an `op` application, the one-step `(= (and true X) X)`
    /// compares `[X]` with `X`'s own arguments and is rejected (clean
    /// `e75141b7b`: "checking failed on step 't1.packed.25152' with rule
    /// 'and_simplify'", external-codegen's narrow-u8 wasm obligations). The unary
    /// `(op survivor)` is accepted on both sides: `(= (and true X) (and X))`
    /// compares `[X]` with `[X]`, and `(= (and X) X)` unwraps the unary source
    /// to `X`'s arguments before comparing.
    fn simplify_to_survivor(
        &mut self,
        source: &str,
        survivor: &str,
        op: &str,
        rule: &str,
    ) -> Option<Equality> {
        let unary = format!("({op} {survivor})");
        let first = self.equality(source, &unary, rule, &[])?;
        let second = self.equality(&unary, survivor, rule, &[])?;
        self.chain(first, second)
    }

    fn definition_body(&self, name: &str) -> Option<&str> {
        self.definition_bodies.get(name).map(String::as_str)
    }

    /// `(= left right)` for an `and_simplify`/`or_simplify` instance whose
    /// single surviving operand `right` is itself an application of the same
    /// connective (see [`nested_connective_simplification`]), derived through
    /// the unary application the consumer's rule does accept:
    /// `(= left (gate right))`, then `(= (gate right) right)`, then `trans`.
    fn nested_connective_equality(
        &mut self,
        gate: &str,
        left: &str,
        right: &str,
        rule: &str,
    ) -> Option<Equality> {
        let wrapped = format!("({gate} {})", self.spelling(right));
        let first = self.equality(left, &wrapped, rule, &[])?;
        let second = self.equality(&wrapped, right, rule, &[])?;
        self.chain(first, second)
    }

    fn chain(&mut self, first: Equality, second: Equality) -> Option<Equality> {
        if first.right != second.left {
            return None;
        }
        self.equality(
            &first.left,
            &second.right,
            "trans",
            &[&first.step, &second.step],
        )
    }

    fn congruence(&mut self, op: &str, args: &[Equality]) -> Option<Equality> {
        let left = application(op, args.iter().map(|a| a.left.as_str()));
        let right = application(op, args.iter().map(|a| a.right.as_str()));
        let premises: Vec<_> = args.iter().map(|a| a.step.as_str()).collect();
        self.equality(&left, &right, "cong", &premises)
    }
}

/// The connective of an `and_simplify`/`or_simplify` step `(= left right)`
/// that the consumer's checker refuses as written, or `None`.
///
/// Carcara's `generic_and_or_simplify` (upstream 9a352ee and Clean's vendored
/// copy alike) drops the identity operands and duplicates of `left` and then
/// compares what survives with the ARGUMENTS of `right` whenever `right` is an
/// application of the same connective, after expanding proof `define-fun`s.
/// So when exactly one operand survives and it is itself such an application —
/// `(= (and true (and a b)) (and a b))`, or a name defined as `(and a b)` — it
/// compares `[(and a b)]` with `[a, b]` and rejects a valid simplification.
/// Measured on external-codegen's `narrow u8 mul` and `AtomicRmw` obligations: Clean
/// 414913cce answered `checking failed on step ... with rule 'and_simplify':
/// rule validation failed` for documents AY had disclosed as hole-free. The
/// unary application `(gate right)` is what the rule unwraps, so the caller
/// derives the equality through it instead.
fn nested_connective_simplification<'r, 'b>(
    rule: &'r str,
    left: &str,
    right: &str,
    body: impl Fn(&str) -> Option<&'b str>,
) -> Option<&'r str> {
    let gate = rule
        .strip_suffix("_simplify")
        .filter(|gate| matches!(*gate, "and" | "or"))?;
    let identity = if gate == "and" { "true" } else { "false" };
    let operands = super::split_application(left, gate)?;
    // A unary `left` is the form the rule unwraps; it never needs this.
    if operands.len() < 2 {
        return None;
    }
    let mut surviving: Vec<&str> = Vec::new();
    for operand in &operands {
        if operand != identity && !surviving.contains(&operand.as_str()) {
            surviving.push(operand);
        }
    }
    let [only] = surviving.as_slice() else {
        return None;
    };
    // A `define-fun` name is expanded by the consumer before the rule runs,
    // so compare, and inspect, the terms the names stand for.
    let expand = |term: &str| {
        let mut term = term.to_owned();
        for _ in 0..MAX_DEPTH {
            match body(&term) {
                Some(expanded) => term = expanded.to_owned(),
                None => break,
            }
        }
        term
    };
    let only = expand(only);
    (only == expand(right) && super::split_application(&only, gate).is_some()).then_some(gate)
}

fn application<'a>(op: &str, args: impl IntoIterator<Item = &'a str>) -> String {
    format!("({op} {})", args.into_iter().collect::<Vec<_>>().join(" "))
}

fn bbterm(bits: &[String]) -> String {
    application("@bbterm", bits.iter().map(String::as_str))
}
