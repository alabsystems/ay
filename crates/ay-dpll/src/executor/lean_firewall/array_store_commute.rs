// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{fnv_hex, nested_base_name, nested_scalar_key, NestedScalarKey};
use ay_frontend::command::Term as PTerm;

/// Distinct-scalar pool for the store-commutativity model: every index / value /
/// base scalar gets a stable `m.2` valuation slot in first-appearance order, and
/// the single named base array is recorded once. Mirrors the identity discipline
/// of `NestedStoreCtx` (named / literal scalars share the `NestedScalarKey`
/// namespace).
struct StoreCommPool {
    scalars: Vec<NestedScalarKey>,
    base: Option<String>,
}

impl StoreCommPool {
    fn new() -> Self {
        StoreCommPool {
            scalars: Vec::new(),
            base: None,
        }
    }

    fn slot(&mut self, key: NestedScalarKey) -> usize {
        if let Some(p) = self.scalars.iter().position(|s| s == &key) {
            p
        } else {
            self.scalars.push(key);
            self.scalars.len() - 1
        }
    }
}

/// Parse a `store`-chain `store(store(… base …, iₖ, vₖ) …)` into its writes in
/// OUTERMOST-first order as `(index_slot, value_slot)` pairs, bottoming out at a
/// single named base array (recorded/checked in `pool.base`). Indices and values
/// must be opaque scalars (Symbol / nullary app / literal). `None` for any shape
/// outside this fragment (compound index/value, a second base array, a non-store
/// non-base leaf).
fn parse_store_commute_chain(t: &PTerm, pool: &mut StoreCommPool) -> Option<Vec<(usize, usize)>> {
    match t {
        PTerm::App(op, args) if op == "store" && args.len() == 3 => {
            let idx = pool.slot(nested_scalar_key(&args[1])?);
            let val = pool.slot(nested_scalar_key(&args[2])?);
            let mut rest = parse_store_commute_chain(&args[0], pool)?;
            let mut v = Vec::with_capacity(rest.len() + 1);
            v.push((idx, val));
            v.append(&mut rest);
            Some(v)
        }
        _ => {
            let name = nested_base_name(t)?;
            match &pool.base {
                Some(b) if b != &name => None,
                _ => {
                    pool.base = Some(name);
                    Some(Vec::new())
                }
            }
        }
    }
}

/// Cap on the number of DISTINCT store indices in a store-commute conflict: the
/// read-index reduction emits a `2ⁿ`-leaf `by_cases … <;> simp_all` product and
/// the guard clause carries `n·(n−1)/2` index-coincidence atoms, so `n` must stay
/// small. All targeted regressions have `n ≤ 3`.
const STORE_COMMUTE_MAX_INDICES: usize = 6;

/// The two `store`-chain sides of a candidate store-commute disequality, reduced
/// to a shared scalar pool.
struct StoreCommuteSides {
    /// `Some(k_slot)` for the SELECT form (`select CHAIN k` on both sides, same
    /// `k`); `None` for the DIRECT array-disequality form.
    read: Option<usize>,
    lhs: Vec<(usize, usize)>,
    rhs: Vec<(usize, usize)>,
}

/// Recognize `(select CHAIN k)` — the read-forwarding side shape.
fn store_commute_select(t: &PTerm) -> Option<(&PTerm, &PTerm)> {
    match t {
        PTerm::App(o, a) if o == "select" && a.len() == 2 => Some((&a[0], &a[1])),
        _ => None,
    }
}

/// Reduce the two sides `lt`, `rt` of a `(not (= lt rt))` assertion to their
/// store-chains over a shared pool, detecting the SELECT (`select CHAIN k`) or
/// DIRECT (`CHAIN` = array) form. `None` when the shape does not fit (mixed
/// forms, differing read indices, non-store leaves).
fn store_commute_extract(
    lt: &PTerm,
    rt: &PTerm,
    pool: &mut StoreCommPool,
) -> Option<StoreCommuteSides> {
    if let (Some((al, kl)), Some((ar, kr))) = (store_commute_select(lt), store_commute_select(rt)) {
        // SELECT form: both `(select CHAIN k)` with the SAME read index `k`.
        let kk = nested_scalar_key(kl)?;
        if Some(&kk) != nested_scalar_key(kr).as_ref() {
            return None;
        }
        let lhs = parse_store_commute_chain(al, pool)?;
        let rhs = parse_store_commute_chain(ar, pool)?;
        let read = pool.slot(kk);
        Some(StoreCommuteSides {
            read: Some(read),
            lhs,
            rhs,
        })
    } else {
        // DIRECT form: both sides are store-chains over the common base.
        let lhs = parse_store_commute_chain(lt, pool)?;
        let rhs = parse_store_commute_chain(rt, pool)?;
        Some(StoreCommuteSides {
            read: None,
            lhs,
            rhs,
        })
    }
}

/// Collect the asserted scalar disequalities that can back guard literals.
fn store_commute_disequalities(parsed: &[PTerm]) -> Vec<(NestedScalarKey, NestedScalarKey)> {
    let mut diseqs = Vec::new();
    for asrt in parsed {
        let PTerm::App(op, args) = asrt else {
            continue;
        };
        if op == "distinct" && args.len() >= 2 {
            let keys: Vec<Option<NestedScalarKey>> = args.iter().map(nested_scalar_key).collect();
            for a in 0..keys.len() {
                for b in (a + 1)..keys.len() {
                    if let (Some(x), Some(y)) = (keys[a].clone(), keys[b].clone()) {
                        diseqs.push((x, y));
                    }
                }
            }
            continue;
        }
        if op != "not" || args.len() != 1 {
            continue;
        }
        let PTerm::App(eq, ea) = &args[0] else {
            continue;
        };
        if eq != "=" || ea.len() != 2 {
            continue;
        }
        if let (Some(x), Some(y)) = (nested_scalar_key(&ea[0]), nested_scalar_key(&ea[1])) {
            diseqs.push((x, y));
        }
    }
    diseqs
}

/// Emit a verified-firewall Lean proof for a STORE-COMMUTATIVITY conflict among
/// the PARSED assertions: `(not (= LHS RHS))` where `LHS`/`RHS` are two `store`-
/// chains that permute the SAME set of writes over the SAME base — directly as
/// arrays (`(not (= (store (store a i v) j w) (store (store a j w) i v)))`) or
/// forwarded through a shared read (`(not (= (select L k) (select R k)))`) — and
/// the pairwise index disequalities that make the permutation value-preserving
/// are all asserted. Under those disequalities each index is written once, so the
/// two chains denote the same array (`sel_upd_same` / `sel_upd_other` + `ext`);
/// asserting they differ is UNSAT.
///
/// Grounding uses `firewall_combined_unsat` and the functional array model from
/// the ROW1 emitters. Each chain unfolds to a raw McCarthy read-over-write tree;
/// the guarded row equality is proved by cases on index coincidences and the
/// read index. DIRECT equality is noncomputable; SELECT equality stays computable.
///
/// Fail-closed: declines (`None`) unless there is a single base array, both
/// chains permute an identical set of `(index, value)` writes with the indices
/// distinct within each chain, and EVERY pairwise index coincidence is backed by
/// an asserted disequality (so the guarded clause is valid). NO verdict/clause
/// change on decline.
pub(crate) fn emit_array_store_commute_firewall_lean_from_parsed(
    parsed: &[PTerm],
) -> Option<String> {
    // Pass 1: collect asserted index disequalities that back the guard literals —
    // from `(not (= x y))` and expanded `(distinct t1 … tn)` (same discipline as
    // the nested-store emitter).
    let diseqs = store_commute_disequalities(parsed);

    // Pass 2: find the main store-commute disequality and reconstruct it.
    for asrt in parsed {
        let PTerm::App(op, args) = asrt else { continue };
        if op != "not" || args.len() != 1 {
            continue;
        }
        let PTerm::App(eq, ea) = &args[0] else {
            continue;
        };
        if eq != "=" || ea.len() != 2 {
            continue;
        }
        let mut pool = StoreCommPool::new();
        let Some(sides) = store_commute_extract(&ea[0], &ea[1], &mut pool) else {
            continue;
        };
        // Both sides must be genuine (non-empty) store-chains.
        if sides.lhs.is_empty() || sides.rhs.is_empty() {
            continue;
        }
        // Indices distinct within each chain (no repeated write to one slot);
        // keeps the last-write set the full write set and the guard set complete.
        let idx_set = |chain: &[(usize, usize)]| -> Option<Vec<usize>> {
            let mut seen: Vec<usize> = Vec::new();
            for &(i, _) in chain {
                if seen.contains(&i) {
                    return None;
                }
                seen.push(i);
            }
            Some(seen)
        };
        let (Some(mut li), Some(mut ri)) = (idx_set(&sides.lhs), idx_set(&sides.rhs)) else {
            continue;
        };
        li.sort_unstable();
        ri.sort_unstable();
        if li != ri {
            continue; // different index sets — not a permutation of the same writes
        }
        // Same SET of `(index, value)` writes (value agreement per index): both
        // chains must denote the same array once the indices are distinct.
        let mut lw: Vec<(usize, usize)> = sides.lhs.clone();
        let mut rw: Vec<(usize, usize)> = sides.rhs.clone();
        lw.sort_unstable();
        rw.sort_unstable();
        if lw != rw {
            continue;
        }
        let indices = li; // sorted, distinct, shared
        if indices.len() < 2 || indices.len() > STORE_COMMUTE_MAX_INDICES {
            continue;
        }
        // Guard set: every pairwise index coincidence, each backed by an asserted
        // disequality. Fail closed if any pair is unbacked (the guarded clause
        // would not be valid).
        let mut guards: Vec<(usize, usize)> = Vec::new();
        let mut all_backed = true;
        for a in 0..indices.len() {
            for b in (a + 1)..indices.len() {
                let (sa, sb) = (indices[a], indices[b]);
                let ka = &pool.scalars[sa];
                let kb = &pool.scalars[sb];
                let backed = diseqs
                    .iter()
                    .any(|(x, y)| (x == ka && y == kb) || (x == kb && y == ka));
                if !backed {
                    all_backed = false;
                }
                guards.push((sa, sb));
            }
        }
        if !all_backed || guards.is_empty() {
            continue;
        }
        return Some(render_array_store_commute_lean(
            sides.read,
            &sides.lhs,
            &sides.rhs,
            &indices,
            &guards,
            fnv_hex(&format!("store_commute:{asrt:?}")),
        ));
    }
    None
}

/// Unfold a `store`-chain (outermost-first `(index_slot, value_slot)` writes) at
/// read expression `read` into nested raw `if`-updates, bottoming out at the base
/// read `m.1 read`.
fn store_commute_tree(chain: &[(usize, usize)], read: &str) -> String {
    match chain.split_first() {
        None => format!("(m.1 {read})"),
        Some(((idx, val), rest)) => format!(
            "(if {read} = (m.2 {idx}) then (m.2 {val}) else {})",
            store_commute_tree(rest, read)
        ),
    }
}

/// Build the guarded proof cascade, ending in the all-indices-distinct row proof.
fn store_commute_proof_body(
    read: Option<usize>,
    read_expr: &str,
    lhs_side: &str,
    rhs_side: &str,
    indices: &[usize],
    guards: &[(usize, usize)],
) -> String {
    let leaf = |indent: &str| -> String {
        let inner = format!("{indent}  ");
        let bycases: String = indices
            .iter()
            .enumerate()
            .map(|(k, s)| format!("by_cases hk{k} : {read_expr} = (m.2 {s})"))
            .collect::<Vec<_>>()
            .join(" <;> ");
        let funext = if read.is_some() {
            String::new()
        } else {
            format!("{inner}funext x\n")
        };
        format!(
            "{indent}have hrow : {lhs_side} = {rhs_side} := by\n\
             {funext}{inner}{bycases} <;> simp_all\n\
             {indent}simp [clauseSat, litSat, atomVal, hrow]"
        )
    };

    fn cascade(
        guards: &[(usize, usize)],
        idx: usize,
        indent: &str,
        leaf: &dyn Fn(&str) -> String,
    ) -> String {
        if idx == guards.len() {
            return leaf(indent);
        }
        let (a, b) = guards[idx];
        let id = 2 + idx;
        let inner_ind = format!("{indent}  ");
        let inner = cascade(guards, idx + 1, &inner_ind, leaf);
        let inner_trimmed = inner.strip_prefix(inner_ind.as_str()).unwrap_or(&inner);
        format!(
            "{indent}by_cases hg{id} : (m.2 {a}) = (m.2 {b})\n\
             {indent}· simp [clauseSat, litSat, atomVal, hg{id}]\n\
             {indent}· {inner_trimmed}"
        )
    }

    cascade(guards, 0, "  ", &leaf)
}

type StoreCommClauseData<'a> = (&'a str, &'a str, &'a str, usize, usize, &'a str);

fn render_store_commute_template(
    read: Option<usize>,
    hash: String,
    lhs_side: &str,
    rhs_side: &str,
    clauses: StoreCommClauseData<'_>,
    proof_body: &str,
) -> String {
    let (guard_arms, original, lemma_lits, lemma_id, proof_id, proof_prems) = clauses;
    let is_select = read.is_some();
    let classical_attr = if is_select {
        String::new()
    } else {
        "attribute [local instance] Classical.propDecidable\n\n".to_string()
    };
    let noncomputable = if is_select { "" } else { "noncomputable " };
    let axiom_note = if is_select {
        "{propext, Quot.sound}"
    } else {
        "{propext, Classical.choice, Quot.sound}"
    };
    let form_note = if is_select {
        "forwarded through a shared read `select _ k` (values compared as `Nat`)"
    } else {
        "compared directly as arrays (`funext`; the function-equality atom is \
         `noncomputable` via `Classical.propDecidable`)"
    };

    format!(
        r#"import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — STORE-COMMUTATIVITY conflict, grounded
  in the verified `firewall_combined_unsat`. Two `store`-chains permute the same
  writes over the same base and are {form_note}; under the asserted pairwise index
  disequalities each index is written once, so the chains denote the SAME array
  (McCarthy `sel_upd_same`/`sel_upd_other` + extensionality) and asserting they
  differ is UNSAT. Reconstructed from the frontend assertions (ay refutes arrays
  eagerly as bare-trust). Model: `(Nat → Nat) × (Nat → Nat)` = base array × scalar
  valuation (`m.1` the array, `m.2 k` the k-th index/element). The theory lemma is
  the guarded clause `row_eq ∨ (⋁ index-coincidences)`, valid by `by_cases` on
  each asserted index coincidence + read-index reduction. Pure Lean 4 core; axioms
  ⊆ {axiom_note}.
-/
namespace AySoundness.Emitted.ArrStoreComm_{hash}
open AySoundness

{classical_attr}abbrev Val := (Nat → Nat) × (Nat → Nat)

-- atom 1 = (LHS = RHS) with each store-chain unfolded to nested if-updates;
-- atoms 2.. = the pairwise index coincidences that guard the permutation.
{noncomputable}def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide ({lhs_side} = {rhs_side})
{guard_arms}  | _ => false

def original : List (Cid × Clause) := [{original}]
def lemmas   : List (Cid × Clause) := [({lemma_id}, [{lemma_lits}])]
def proof    : List (Cid × Clause × List Int) := [({proof_id}, [], [{proof_prems}])]

theorem lemma_valid (m : Val) : clauseSat (atomVal m) [{lemma_lits}] = true := by
{proof_body}

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- The store-commutativity conflict has no model — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.Emitted.ArrStoreComm_{hash}
"#,
    )
}

fn render_array_store_commute_lean(
    read: Option<usize>,
    lhs: &[(usize, usize)],
    rhs: &[(usize, usize)],
    indices: &[usize],
    guards: &[(usize, usize)],
    hash: String,
) -> String {
    use std::fmt::Write as _;

    let is_select = read.is_some();
    let read_expr = match read {
        Some(k) => format!("(m.2 {k})"),
        None => "x".to_string(),
    };
    let lhs_tree = store_commute_tree(lhs, &read_expr);
    let rhs_tree = store_commute_tree(rhs, &read_expr);
    // The SELECT form compares `Nat`s at the shared read index; the DIRECT form
    // compares whole arrays, so the equated terms are `fun x => …` functions and
    // the row lemma is a function equality proved under `funext`.
    let lhs_side = if is_select {
        lhs_tree.clone()
    } else {
        format!("(fun x => {lhs_tree})")
    };
    let rhs_side = if is_select {
        rhs_tree.clone()
    } else {
        format!("(fun x => {rhs_tree})")
    };
    let g = guards.len();

    // atomVal: atom 1 = row_eq, atoms 2..=1+g = pairwise index coincidences.
    let mut guard_arms = String::new();
    for (k, (a, b)) in guards.iter().enumerate() {
        let _ = writeln!(
            &mut guard_arms,
            "  | {id} => decide ((m.2 {a}) = (m.2 {b}))",
            id = 2 + k
        );
    }
    let original: String = std::iter::once("(1, [-1])".to_string())
        .chain((0..g).map(|k| format!("({id}, [-{id}])", id = 2 + k)))
        .collect::<Vec<_>>()
        .join(", ");
    let lemma_lits: String = (1..=1 + g)
        .map(|n| n.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let lemma_id = 2 + g;
    let proof_id = 3 + g;
    let proof_prems: String = (1..=lemma_id)
        .map(|n| n.to_string())
        .collect::<Vec<_>>()
        .join(", ");

    let proof_body =
        store_commute_proof_body(read, &read_expr, &lhs_side, &rhs_side, indices, guards);
    render_store_commute_template(
        read,
        hash,
        &lhs_side,
        &rhs_side,
        (
            &guard_arms,
            &original,
            &lemma_lits,
            lemma_id,
            proof_id,
            &proof_prems,
        ),
        &proof_body,
    )
}
