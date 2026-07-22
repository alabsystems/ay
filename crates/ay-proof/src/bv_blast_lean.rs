//! Render a [`BvBlastProof`] as the verified-firewall Lean shape (BV-large piece 3/3).
//!
//! This is the emitter that turns a zero-trust bit-blast refutation into the
//! "import-the-verified-theorem" file: it grounds a BV UNSAT verdict in the
//! machine-checked `AySoundness.firewall_combined_unsat` + `lratCheck_sound`, with
//! the bit-blasting gates carried as per-gate "respect" hypotheses (the
//! gate-respecting-assignment shape proved out in
//! `verification/lean/AySoundness/CombinedBvBlastAbstract.lean`).
//!
//! The emitted file defines:
//!   * `Val` — a propositional assignment `α : Nat → Bool` plus, per [`BitLemma`],
//!     a proof that the gate output bit equals `gateEval` of its inputs;
//!   * `atomVal m = m.α` — atoms are bits, gate outputs are constrained (not
//!     computed), so there is no recursion over the gate DAG;
//!   * `original` — the `Disequality`-provenance clauses (the refuted obligation);
//!   * `lemmas` — the `BitLemmaCnf` clauses (each valid under any gate-respecting α);
//!   * `proof` — the [`Refutation`] resolution chain as RUP/`lratCheck` steps;
//!   * `lemmas_valid` — proved per clause LOCALLY (case-split only that clause's
//!     gate's ≤ 3 inputs + its own respect), so it scales independent of width;
//!   * `wα` + `val_inhabited : Nonempty Val` — a witness assignment (topological
//!     gate eval) certifying `Val` is INHABITED, so `no_model`'s `∀ m` is
//!     non-vacuous. Without it, an adversarial proof with contradictory gate
//!     respects (uninhabited `Val`) would let `no_model` check vacuously for a
//!     *satisfiable* `original` — a false "verified". `validate()` cannot catch
//!     that (it sees clause/resolution well-formedness, not joint satisfiability of
//!     the respects), so the witness is emitted here and an uninhabited `Val` fails
//!     `val_inhabited`'s `decide` → the kernel rejects the file (fail-closed).
//!   * `no_model` — `firewall_combined_unsat … = ∀ m, ¬ Sat (atomVal m) original`.
//!
//! Atom convention: firewall atom = bit-blast variable id (0-based) + 1, so literal
//! `Lit { var, neg }` renders to `±(var + 1)`. Clause/step ids are `BvBlastProof`
//! id + 1 (clauses get `1..=n`, resolution steps `n+1..`, matching the namespacing
//! the proof's premise ids already use).
//!
//! Soundness note: the `decide` that discharges `lratCheck … = true` is kernel
//! reduction over a `List`-based checker — fine for small/medium refutations; very
//! large bit-blasts (hundreds of clauses) need a verified *efficient* checker (a
//! shared concern, orthogonal to this emitter).

use crate::bv_blast_export::{BitLemmaKind, BvBlastProof, ClauseProvenance, Lit};
use std::collections::BTreeMap;

/// Evaluate a gate over concrete input bits. Mirrors `bv_blast_export::gate_eval`
/// exactly; used to compute the inhabitation witness (`wα`).
fn eval_gate(kind: BitLemmaKind, ins: &[bool]) -> bool {
    match kind {
        BitLemmaKind::And2 => ins[0] && ins[1],
        BitLemmaKind::Or2 => ins[0] || ins[1],
        BitLemmaKind::Xor2 => ins[0] ^ ins[1],
        BitLemmaKind::Xor3 => ins[0] ^ ins[1] ^ ins[2],
        BitLemmaKind::FullAdderCarry => (ins[0] && ins[1]) || (ins[2] && (ins[0] ^ ins[1])),
        BitLemmaKind::Not => !ins[0],
        BitLemmaKind::ConstTrue => true,
        BitLemmaKind::ConstFalse => false,
        BitLemmaKind::XnorEq => !(ins[0] ^ ins[1]),
    }
}

/// Firewall atom for a 0-based bit-blast variable id (1-based, so literals can be
/// signed without colliding with `0`).
fn atom(var: u32) -> i64 {
    i64::from(var) + 1
}

/// Render a literal as a signed firewall atom.
fn lit_to_int(l: Lit) -> i64 {
    let a = atom(l.var);
    if l.neg {
        -a
    } else {
        a
    }
}

/// Render a clause (`List Int`).
fn clause_to_lean(lits: &[Lit]) -> String {
    let inner: Vec<String> = lits.iter().map(|l| lit_to_int(*l).to_string()).collect();
    format!("[{}]", inner.join(", "))
}

/// `α`-application for a bit-blast variable under a binding prefix: `"α "` inside
/// the `structure Val` field (where `α` is the bound field), or `"m.α "` inside a
/// proof where `m : Val`.
fn av(prefix: &str, var: u32) -> String {
    format!("{prefix}{}", atom(var))
}

/// The `gateEval` expression for a gate kind over its input variables, as a Lean
/// `Bool` term (each input rendered as `<prefix><atom>`). Mirrors
/// `bv_blast_export::gate_eval` exactly.
fn gate_eval_lean(kind: BitLemmaKind, ins: &[u32], prefix: &str) -> String {
    let a = |i: usize| av(prefix, ins[i]);
    match kind {
        BitLemmaKind::And2 => format!("({} && {})", a(0), a(1)),
        BitLemmaKind::Or2 => format!("({} || {})", a(0), a(1)),
        BitLemmaKind::Xor2 => format!("(Bool.xor {} {})", a(0), a(1)),
        BitLemmaKind::Xor3 => format!("(Bool.xor (Bool.xor {} {}) {})", a(0), a(1), a(2)),
        BitLemmaKind::FullAdderCarry => format!(
            "(({a0} && {a1}) || ({a2} && Bool.xor {a0} {a1}))",
            a0 = a(0),
            a1 = a(1),
            a2 = a(2)
        ),
        BitLemmaKind::Not => format!("(!{})", a(0)),
        BitLemmaKind::ConstTrue => "true".to_string(),
        BitLemmaKind::ConstFalse => "false".to_string(),
        BitLemmaKind::XnorEq => format!("(!(Bool.xor {} {}))", a(0), a(1)),
    }
}

/// Render a [`BvBlastProof`] as a self-contained verified-firewall Lean module.
///
/// The result `import`s `AySoundness.Firewall`, so it must be checked with the
/// `AySoundness` library on `LEAN_PATH` (the `verification/lean` lake project). The
/// proof must be well-formed (e.g. [`BvBlastProof::validate`] succeeds); a
/// malformed proof renders a file that simply fails to kernel-check.
#[must_use]
pub fn render_bv_blast_proof_lean(proof: &BvBlastProof, module: &str) -> String {
    let mut out = String::new();
    let nl = '\n';

    out.push_str("import AySoundness.Firewall\n");
    out.push_str(&format!(
        "/-! Auto-generated by AY: bit-blast UNSAT for `{}`, grounded in the verified\n    \
         firewall `AySoundness.firewall_combined_unsat` + `lratCheck_sound`. -/\n",
        proof.asserted_smt
    ));
    out.push_str(&format!("namespace AySoundness.{module}{nl}"));
    out.push_str("open AySoundness\n\n");

    // --- Val: an assignment plus one `respects_<id>` proof per gate. ----------
    out.push_str(
        "/-- A gate-respecting assignment: `α` plus, per gate, a proof that the\n    \
         output bit equals `gateEval` of its inputs. -/\n",
    );
    out.push_str("structure Val where\n");
    out.push_str("  α : Nat → Bool\n");
    for lem in &proof.bit_lemmas {
        out.push_str(&format!(
            "  respects_{} : α {} = {}\n",
            lem.id,
            atom(lem.out),
            gate_eval_lean(lem.kind, &lem.ins, "α ")
        ));
    }
    out.push('\n');

    out.push_str("def atomVal (m : Val) (n : Nat) : Bool := m.α n\n\n");

    // --- Inhabitation witness: certify `Val` is non-empty, so `no_model`'s `∀ m`
    // is NON-VACUOUS (otherwise an uninhabited `Val` — e.g. contradictory gate
    // respects — would let `no_model` kernel-check for a *satisfiable* `original`,
    // a false "verified"). Compute a satisfying assignment by topological gate
    // evaluation over all-false inputs; emit it as `wα` and discharge each gate's
    // respect by `decide`. An unsatisfiable set of respects fails to check HERE —
    // fail-closed. (Gates are emitted in `bit_lemmas` order, which the producer
    // builds bottom-up = topological: each `out` is computed after its inputs.)
    // Bounded fixpoint so any ACYCLIC gate order converges (≤ #gates passes),
    // not just a perfectly topological one — a legitimately-reordered proof is
    // then not falsely rejected, while genuinely-contradictory respects (e.g.
    // ConstTrue ∧ ConstFalse on one var, or a cycle) never stabilise and so fail
    // the `decide` below (fail-closed).
    let mut witness: BTreeMap<u32, bool> = BTreeMap::new();
    for _ in 0..=proof.bit_lemmas.len() {
        let mut changed = false;
        for lem in &proof.bit_lemmas {
            let ins: Vec<bool> = lem
                .ins
                .iter()
                .map(|&i| witness.get(&i).copied().unwrap_or(false))
                .collect();
            let v = eval_gate(lem.kind, &ins);
            if witness.insert(lem.out, v) != Some(v) {
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    out.push_str(
        "/-- A witness assignment (topological gate eval over all-false inputs): it\n    \
         certifies `Val` is inhabited, so `no_model` below is non-vacuous. -/\n",
    );
    out.push_str("def wα : Nat → Bool := fun n => match n with\n");
    for (&v, &b) in &witness {
        out.push_str(&format!("  | {} => {}\n", atom(v), b));
    }
    out.push_str("  | _ => false\n\n");
    out.push_str("theorem val_inhabited : Nonempty Val :=\n  ⟨{ α := wα");
    for lem in &proof.bit_lemmas {
        out.push_str(&format!(", respects_{} := by decide", lem.id));
    }
    out.push_str(" }⟩\n\n");

    // --- original (Disequality clauses) and lemmas (gate Tseitin clauses). ----
    let mut original: Vec<String> = Vec::new();
    let mut lemmas: Vec<String> = Vec::new();
    for cl in &proof.clauses {
        let cid = i64::from(cl.id) + 1;
        let entry = format!("({}, {})", cid, clause_to_lean(&cl.lits));
        match cl.provenance {
            ClauseProvenance::Disequality => original.push(entry),
            ClauseProvenance::BitLemmaCnf { .. } => lemmas.push(entry),
        }
    }
    out.push_str(&format!(
        "def original : List (Cid × Clause) := [{}]{nl}",
        original.join(", ")
    ));
    out.push_str(&format!(
        "def lemmas : List (Cid × Clause) := [{}]{nl}{nl}",
        lemmas.join(", ")
    ));

    // --- proof: the resolution chain as RUP steps. ----------------------------
    // Premise ids (clauses < nclauses, steps >= nclauses) all map by +1; the last
    // step derives the empty clause.
    out.push_str("def proof : List (Cid × Clause × List Int) := [\n");
    let nsteps = proof.refutation.steps.len();
    for (i, step) in proof.refutation.steps.iter().enumerate() {
        let cid = i64::from(step.id) + 1;
        let clause = clause_to_lean(&step.clause);
        let hints: Vec<String> = step
            .premises
            .iter()
            .map(|p| (i64::from(*p) + 1).to_string())
            .collect();
        let comma = if i + 1 < nsteps { "," } else { "" };
        out.push_str(&format!(
            "  ({cid}, {clause}, [{}]){comma}{nl}",
            hints.join(", ")
        ));
    }
    out.push_str("]\n\n");

    // --- lemmas_valid: each gate clause valid under any gate-respecting α. -----
    out.push_str(
        "/-- Every gate Tseitin clause holds under any gate-respecting assignment:\n    \
         per clause, case-split that gate's inputs and apply its `respects_*`. -/\n",
    );
    out.push_str(
        "theorem lemmas_valid :\n    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by\n",
    );
    out.push_str("  intro cl hcl m\n");
    out.push_str(
        "  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,\n    \
         List.not_mem_nil, or_false] at hcl\n",
    );
    // Gather the BitLemmaCnf clauses in order, with their gate, to emit per-clause bullets.
    let lemma_clauses: Vec<&crate::bv_blast_export::Clause> = proof
        .clauses
        .iter()
        .filter(|c| matches!(c.provenance, ClauseProvenance::BitLemmaCnf { .. }))
        .collect();
    if lemma_clauses.is_empty() {
        out.push_str("  exact absurd hcl (by simp)\n");
    } else {
        // `hcl : cl = c0 ∨ cl = c1 ∨ … ∨ cl = c_{k-1}` (last has no `∨`).
        let pat = std::iter::repeat_n("h", lemma_clauses.len())
            .collect::<Vec<_>>()
            .join(" | ");
        out.push_str(&format!("  rcases hcl with {pat}\n"));
        for cl in &lemma_clauses {
            let lemma_idx = match cl.provenance {
                ClauseProvenance::BitLemmaCnf { lemma } => lemma,
                ClauseProvenance::Disequality => unreachable!(),
            };
            let lem = &proof.bit_lemmas[lemma_idx as usize];
            // Case-split this gate's inputs (≤ 3), then simp_all with its respect.
            // The NAMED form (`cases h : …`) records each split as a hypothesis so
            // `simp_all` can substitute it even though the bit only becomes visible
            // after `clauseSat`/`litSat` are unfolded.
            let cases: String = lem.ins.iter().fold(String::new(), |mut acc, &v| {
                use std::fmt::Write as _;
                let _ = write!(acc, "cases hv{v} : {} <;> ", av("m.α ", v));
                acc
            });
            out.push_str(&format!(
                "  · subst h; {cases}simp_all [clauseSat, litSat, atomVal, m.respects_{}]\n",
                lem.id
            ));
        }
    }
    out.push('\n');

    // --- no_model: the firewall verdict. --------------------------------------
    out.push_str(
        "/-- No gate-respecting assignment satisfies the obligation — bit-blasting\n    \
         through the verified firewall (per-gate validity + `lratCheck`). -/\n",
    );
    out.push_str("theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=\n");
    out.push_str(
        "  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)\n    \
         atomVal (by decide) (by decide) lemmas_valid (by decide)\n\n",
    );

    out.push_str(&format!("end AySoundness.{module}{nl}"));
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bv_blast_export::{
        BitLemma, BvBlastProof, BvOp, Clause, ClauseProvenance, OperandRef, Refutation, ResRule,
        ResolutionStep, SliceObligation, VarRole, VarTable,
    };

    /// Build the small UNSAT obligation `(a ∧ b) = 1 ∧ a = 0` as a hand-checked
    /// `BvBlastProof` (one And2 gate). The gate's full Tseitin CNF (4 clauses, the
    /// producer's enumeration) plus the two assertion clauses, refuted by a 3-step
    /// resolution chain to the empty clause. `validate()` confirms well-formedness.
    pub(super) fn and2_unsat_proof() -> BvBlastProof {
        // vars: 0 = a, 1 = b, 2 = out (= a ∧ b).
        let mut vars = VarTable::default();
        let _ = vars.alloc(VarRole::InputA { bit: 0 });
        let _ = vars.alloc(VarRole::InputB { bit: 0 });
        let _ = vars.alloc(VarRole::Out { bit: 0 });

        let bit_lemmas = vec![BitLemma {
            id: 0,
            kind: BitLemmaKind::And2,
            out: 2,
            ins: vec![0, 1],
        }];

        // And2(out=2, ins=[0,1]) Tseitin enumeration (forbid each violating row):
        //   [2,¬0,¬1], [¬2,0,1], [¬2,0,¬1], [¬2,¬0,1]
        let g = |lemma| ClauseProvenance::BitLemmaCnf { lemma };
        let clauses = vec![
            Clause {
                id: 0,
                lits: vec![Lit::neg(2), Lit::pos(0), Lit::pos(1)],
                provenance: g(0),
            },
            Clause {
                id: 1,
                lits: vec![Lit::neg(2), Lit::pos(0), Lit::neg(1)],
                provenance: g(0),
            },
            Clause {
                id: 2,
                lits: vec![Lit::neg(2), Lit::neg(0), Lit::pos(1)],
                provenance: g(0),
            },
            Clause {
                id: 3,
                lits: vec![Lit::pos(2), Lit::neg(0), Lit::neg(1)],
                provenance: g(0),
            },
            // Obligation: out = 1, a = 0.
            Clause {
                id: 4,
                lits: vec![Lit::pos(2)],
                provenance: ClauseProvenance::Disequality,
            },
            Clause {
                id: 5,
                lits: vec![Lit::neg(0)],
                provenance: ClauseProvenance::Disequality,
            },
        ];

        // Refutation: res(c0,c1 | pivot 1) = [¬2,0]; res(c4,step6 | pivot 2) = [0];
        // res(step7,c5 | pivot 0) = []. Step ids are namespaced after clause ids.
        let refutation = Refutation {
            steps: vec![
                ResolutionStep {
                    id: 6,
                    clause: vec![Lit::neg(2), Lit::pos(0)],
                    rule: ResRule::Resolution,
                    premises: [0, 1],
                    pivot: 1,
                },
                ResolutionStep {
                    id: 7,
                    clause: vec![Lit::pos(0)],
                    rule: ResRule::Resolution,
                    premises: [4, 6],
                    pivot: 2,
                },
                ResolutionStep {
                    id: 8,
                    clause: vec![],
                    rule: ResRule::Resolution,
                    premises: [7, 5],
                    pivot: 0,
                },
            ],
        };

        BvBlastProof {
            format_version: crate::bv_blast_export::FORMAT_VERSION,
            obligation: SliceObligation {
                width: 1,
                op: BvOp::And,
                lhs_args: [OperandRef::A, OperandRef::B],
                rhs_args: [OperandRef::A, OperandRef::B],
            },
            asserted_smt: "(and (= (bvand a b) #b1) (= a #b0))".to_string(),
            vars,
            bit_lemmas,
            clauses,
            refutation,
        }
    }

    /// A DEEP-DAG obligation: `g₂ = (a ∧ b) ∧ c = 1 ∧ a = 0` (two chained And2
    /// gates, `g₂`'s input is the gate `g₁`). Exercises the renderer's per-clause
    /// LOCAL validity (a gate whose input is another gate's output, cased as an
    /// opaque bit) and a 5-step resolution chain through the RUP transcription.
    /// vars: 0=a 1=b 2=c 3=g₁(=a∧b) 4=g₂(=g₁∧c).
    pub(super) fn and_chain_unsat_proof() -> BvBlastProof {
        let mut vars = VarTable::default();
        let _ = vars.alloc(VarRole::InputA { bit: 0 });
        let _ = vars.alloc(VarRole::InputB { bit: 0 });
        let _ = vars.alloc(VarRole::InputA { bit: 1 });
        let _ = vars.alloc(VarRole::Aux { bit: 0 });
        let _ = vars.alloc(VarRole::Out { bit: 0 });

        let bit_lemmas = vec![
            BitLemma {
                id: 0,
                kind: BitLemmaKind::And2,
                out: 3,
                ins: vec![0, 1],
            },
            BitLemma {
                id: 1,
                kind: BitLemmaKind::And2,
                out: 4,
                ins: vec![3, 2],
            },
        ];
        let g = |lemma| ClauseProvenance::BitLemmaCnf { lemma };
        let clauses = vec![
            // And2(g₁=3, [0,1]) Tseitin enumeration.
            Clause {
                id: 0,
                lits: vec![Lit::neg(3), Lit::pos(0), Lit::pos(1)],
                provenance: g(0),
            },
            Clause {
                id: 1,
                lits: vec![Lit::neg(3), Lit::pos(0), Lit::neg(1)],
                provenance: g(0),
            },
            Clause {
                id: 2,
                lits: vec![Lit::neg(3), Lit::neg(0), Lit::pos(1)],
                provenance: g(0),
            },
            Clause {
                id: 3,
                lits: vec![Lit::pos(3), Lit::neg(0), Lit::neg(1)],
                provenance: g(0),
            },
            // And2(g₂=4, [3,2]) Tseitin enumeration.
            Clause {
                id: 4,
                lits: vec![Lit::neg(4), Lit::pos(3), Lit::pos(2)],
                provenance: g(1),
            },
            Clause {
                id: 5,
                lits: vec![Lit::neg(4), Lit::pos(3), Lit::neg(2)],
                provenance: g(1),
            },
            Clause {
                id: 6,
                lits: vec![Lit::neg(4), Lit::neg(3), Lit::pos(2)],
                provenance: g(1),
            },
            Clause {
                id: 7,
                lits: vec![Lit::pos(4), Lit::neg(3), Lit::neg(2)],
                provenance: g(1),
            },
            // Obligation: g₂ = 1, a = 0.
            Clause {
                id: 8,
                lits: vec![Lit::pos(4)],
                provenance: ClauseProvenance::Disequality,
            },
            Clause {
                id: 9,
                lits: vec![Lit::neg(0)],
                provenance: ClauseProvenance::Disequality,
            },
        ];
        // g₂→g₁ (res 4,5 | 2); g₁→a (res 0,1 | 1); g₂∧(g₂→g₁)→g₁ (res 8,10 | 4);
        // g₁∧(g₁→a)→a (res 11,12 | 3); a∧¬a → ⊥ (res 13,9 | 0).
        let step = |id, clause, premises, pivot| ResolutionStep {
            id,
            clause,
            rule: ResRule::Resolution,
            premises,
            pivot,
        };
        let refutation = Refutation {
            steps: vec![
                step(10, vec![Lit::neg(4), Lit::pos(3)], [4, 5], 2),
                step(11, vec![Lit::neg(3), Lit::pos(0)], [0, 1], 1),
                step(12, vec![Lit::pos(3)], [8, 10], 4),
                step(13, vec![Lit::pos(0)], [11, 12], 3),
                step(14, vec![], [13, 9], 0),
            ],
        };
        BvBlastProof {
            format_version: crate::bv_blast_export::FORMAT_VERSION,
            obligation: SliceObligation {
                width: 1,
                op: BvOp::And,
                lhs_args: [OperandRef::A, OperandRef::B],
                rhs_args: [OperandRef::A, OperandRef::B],
            },
            asserted_smt: "(and (= (bvand (bvand a b) c) #b1) (= a #b0))".to_string(),
            vars,
            bit_lemmas,
            clauses,
            refutation,
        }
    }

    #[test]
    fn hand_built_proof_is_well_formed() {
        and2_unsat_proof()
            .validate()
            .expect("hand-built proof must validate");
        and_chain_unsat_proof()
            .validate()
            .expect("chain proof must validate");
    }

    #[test]
    fn render_contains_the_firewall_shape() {
        let lean = render_bv_blast_proof_lean(&and2_unsat_proof(), "RenderedAnd2");
        // Grounds in the verified firewall, not a re-defined/native checker.
        assert!(lean.contains("import AySoundness.Firewall"));
        assert!(lean.contains("firewall_combined_unsat"));
        assert!(!lean.contains("native_decide"));
        assert!(!lean.contains("sorry"));
        // The gate respect uses bare `α` (the bound field), out atom 3 = α1 && α2.
        assert!(lean.contains("respects_0 : α 3 = (α 1 && α 2)"));
        // atoms are var+1; the disequality `out = 1` clause is [3], `a = 0` is [-1].
        assert!(lean.contains("def original : List (Cid × Clause) := [(5, [3]), (6, [-1])]"));
        // last proof step derives the empty clause.
        assert!(lean.contains("(9, [], [8, 6])"));
        // the inhabitation witness makes `no_model`'s `∀ m : Val` non-vacuous.
        assert!(lean.contains("def wα : Nat → Bool"));
        assert!(lean.contains("theorem val_inhabited : Nonempty Val"));
    }
}

#[cfg(test)]
mod golden {
    use super::*;

    const DIR: &str = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../verification/lean/AySoundness/"
    );

    /// One (proof, module, golden-artifact) row. Each artifact is committed,
    /// imported into the `AySoundness` lake library, and kernel-re-verified on
    /// every build, so this golden test ties the emitter's output to a
    /// machine-checked certificate. Set `AY_DUMP_RENDER=1` to regenerate the
    /// artifacts after a renderer change (then re-run `lake build`).
    #[test]
    fn renderer_matches_kernel_checked_artifacts() {
        let cases: &[(BvBlastProof, &str, &str)] = &[
            (
                tests::and2_unsat_proof(),
                "CombinedBvBlastRendered",
                include_str!("../../../verification/lean/AySoundness/CombinedBvBlastRendered.lean"),
            ),
            (
                tests::and_chain_unsat_proof(),
                "CombinedBvBlastChain",
                include_str!("../../../verification/lean/AySoundness/CombinedBvBlastChain.lean"),
            ),
        ];
        let dump = std::env::var("AY_DUMP_RENDER").is_ok();
        for (proof, module, golden) in cases {
            let rendered = render_bv_blast_proof_lean(proof, module);
            if dump {
                std::fs::write(format!("{DIR}{module}.lean"), &rendered).unwrap();
                continue;
            }
            assert_eq!(
                &rendered, golden,
                "renderer output for {module} drifted from the kernel-checked artifact; \
                 regenerate with AY_DUMP_RENDER=1"
            );
        }
    }
}

#[cfg(test)]
mod fail_closed {
    use super::*;
    use crate::bv_blast_export::{
        BitLemma, BvBlastProof, BvOp, Clause, ClauseProvenance, OperandRef, Refutation, ResRule,
        ResolutionStep, SliceObligation, VarRole, VarTable,
    };

    /// The adversarial proof from the soundness review: `ConstTrue(out=0)` AND
    /// `ConstFalse(out=0)`. `validate()` ACCEPTS it (both gate clauses are genuine
    /// Tseitin clauses of their cited lemmas, and `[0],[¬0]` resolve to ⊥), yet
    /// `Val` is UNINHABITED — so without the inhabitation witness `no_model` would
    /// kernel-check vacuously for the SATISFIABLE `original = [1]` (a false
    /// "verified"). The emitted `val_inhabited` closes this: its witness assigns the
    /// conflicted bit ONE value, contradicting the other gate's respect, so the
    /// `by decide` fails and the kernel REJECTS the file (verified empirically: the
    /// rendered `AttackUninhab` is rejected at `wα 1 = true`).
    fn uninhabited_proof() -> BvBlastProof {
        let mut vars = VarTable::default();
        let _ = vars.alloc(VarRole::Out { bit: 0 }); // var 0 = conflicted gate output
        let _ = vars.alloc(VarRole::InputA { bit: 0 }); // var 1 = original (SAT) var
        BvBlastProof {
            format_version: crate::bv_blast_export::FORMAT_VERSION,
            obligation: SliceObligation {
                width: 1,
                op: BvOp::And,
                lhs_args: [OperandRef::A, OperandRef::B],
                rhs_args: [OperandRef::A, OperandRef::B],
            },
            asserted_smt: "(adversarial: uninhabited Val)".to_string(),
            vars,
            bit_lemmas: vec![
                BitLemma {
                    id: 0,
                    kind: BitLemmaKind::ConstTrue,
                    out: 0,
                    ins: vec![],
                },
                BitLemma {
                    id: 1,
                    kind: BitLemmaKind::ConstFalse,
                    out: 0,
                    ins: vec![],
                },
            ],
            clauses: vec![
                Clause {
                    id: 0,
                    lits: vec![Lit::pos(0)],
                    provenance: ClauseProvenance::BitLemmaCnf { lemma: 0 },
                },
                Clause {
                    id: 1,
                    lits: vec![Lit::neg(0)],
                    provenance: ClauseProvenance::BitLemmaCnf { lemma: 1 },
                },
                Clause {
                    id: 2,
                    lits: vec![Lit::pos(1)],
                    provenance: ClauseProvenance::Disequality,
                },
            ],
            refutation: Refutation {
                steps: vec![ResolutionStep {
                    id: 3,
                    clause: vec![],
                    rule: ResRule::Resolution,
                    premises: [0, 1],
                    pivot: 0,
                }],
            },
        }
    }

    #[test]
    fn uninhabited_proof_validates_but_render_is_fail_closed() {
        let proof = uninhabited_proof();
        // validate() cannot see inhabitation, so it ACCEPTS this faithfulness-broken proof.
        proof.validate().expect("adversarial proof validates");
        let lean = render_bv_blast_proof_lean(&proof, "AttackUninhab");
        // The witness assigns the conflicted bit (atom 1) `false` (ConstFalse wins the
        // fixpoint), but gate 0's respect demands it be `true` — so `val_inhabited`'s
        // `decide` provably fails and the kernel rejects the file. Both facts are present:
        assert!(
            lean.contains("respects_0 : α 1 = true"),
            "ConstTrue demands α1 = true"
        );
        assert!(
            lean.contains("| 1 => false"),
            "witness assigns α1 = false (ConstFalse)"
        );
        assert!(lean.contains("theorem val_inhabited : Nonempty Val"));
    }
}
