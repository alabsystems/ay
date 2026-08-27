// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

impl PolyManager {
    /// Variables in Brown-recursion order: eliminate the cheapest degree first.
    fn mod_gcd_vars(&self, u: &Poly, v: &Poly) -> Option<Vec<PVar>> {
        let mut all = self.vars(u);
        for x in self.vars(v) {
            if !all.contains(&x) {
                all.push(x);
            }
        }
        let mut keyed: Vec<(u32, PVar)> = all
            .iter()
            .map(|&x| (self.degree(u, x).min(self.degree(v, x)), x))
            .collect();
        keyed.sort_unstable();
        let vars = keyed.into_iter().map(|(_, x)| x).collect::<Vec<_>>();
        (!vars.is_empty()).then_some(vars)
    }
}
