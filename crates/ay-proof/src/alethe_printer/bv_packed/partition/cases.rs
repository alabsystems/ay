// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl PartitionProof<'_, '_, '_, '_> {
    pub(super) fn leaf(
        &mut self,
        leaf: &IntervalLeaf,
        ordered: &(String, String),
    ) -> Option<String> {
        let pc = self.proof.printer.format_term(leaf.point);
        let start = self.proof.printer.format_term(self.identity.start);
        let end = self.proof.printer.format_term(self.identity.end);
        let a = format!("(bvult {pc} {start})");
        let b = format!("(bvult {pc} {end})");
        let goal = self.proof.printer.format_term(leaf.equality);
        let mut outer = Vec::new();
        for av in [true, false] {
            let aend = self.proof.fresh();
            let aid = self.proof.fresh();
            let alit = if av { a.clone() } else { format!("(not {a})") };
            self.proof
                .append(&format!("(anchor :step {aend})\n(assume {aid} {alit})\n"))?;
            let mut inner = Vec::new();
            for bv in [true, false] {
                let bend = self.proof.fresh();
                let bid = self.proof.fresh();
                let blit = if bv { b.clone() } else { format!("(not {b})") };
                self.proof
                    .append(&format!("(anchor :step {bend})\n(assume {bid} {blit})\n"))?;
                let ar = self.literal_order(&pc, &start, av, &aid)?;
                let br = self.literal_order(&pc, &end, bv, &bid)?;
                if av && !bv {
                    let lemma = self.proof.fresh();
                    let clause = [ordered, &ar, &br].map(|x| order::negate(&x.0)).join(" ");
                    self.proof
                        .named_step(&lemma, &clause, "la_generic", &[], " :args (1 1 1)")?;
                    let empty =
                        self.proof
                            .step("", "resolution", &[&lemma, &ordered.1, &ar.1, &br.1])?;
                    self.proof.step(&goal, "weakening", &[&empty])?;
                } else {
                    let s_unit = self.complement(&start, &pc, &ar, !av)?;
                    let e_unit = self.complement(&end, &pc, &br, !bv)?;
                    let s_cmp = format!("(bvule {start} {pc})");
                    let e_cmp = format!("(bvule {end} {pc})");
                    // Each branch gets fresh contextual equalities. No facts or
                    // derived units can survive their assumption's discharge.
                    let facts = DetHashMap::from_iter([
                        (a.clone(), self.fact(&a, av, &aid)?),
                        (b.clone(), self.fact(&b, bv, &bid)?),
                        (s_cmp.clone(), self.fact(&s_cmp, !av, &s_unit)?),
                        (e_cmp.clone(), self.fact(&e_cmp, !bv, &e_unit)?),
                    ]);
                    let result = self.rewrite(leaf.sum, leaf, &facts, 0)?;
                    let TermData::App(_, args) = self.proof.printer.terms.get(leaf.equality) else {
                        return None;
                    };
                    let target = self.proof.printer.format_term(args[1]);
                    let same = self
                        .proof
                        .equality(&result.right, &target, "poly_simp", &[])?;
                    let result = self.proof.chain(result, same)?;
                    if format!("(= {} {})", result.left, result.right) != goal {
                        return None;
                    }
                }
                self.proof.named_step(
                    &bend,
                    &format!("(not {blit}) {goal}"),
                    "subproof",
                    &[],
                    &format!(" :discharge ({bid})"),
                )?;
                inner.push(bend);
            }
            self.proof
                .step(&goal, "resolution", &[&inner[0], &inner[1]])?;
            self.proof.named_step(
                &aend,
                &format!("(not {alit}) {goal}"),
                "subproof",
                &[],
                &format!(" :discharge ({aid})"),
            )?;
            outer.push(aend);
        }
        self.proof
            .step(&goal, "resolution", &[&outer[0], &outer[1]])
    }
}
