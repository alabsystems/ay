// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Class lengths for [`super::SeqStructure`]: `seq.len` model rows, units,
//! the empty sequence and concrete values, propagated through concatenations
//! and extracts to a fixpoint.

use num_traits::ToPrimitive;

use super::{SeqStructure, Shape};

impl SeqStructure<'_> {
    /// The length of every class, from `seq.len` model rows, structure and
    /// existing concrete values, propagated through concatenations and
    /// extracts. `None` on a contradiction.
    pub(super) fn class_lengths(&self) -> Option<Vec<Option<usize>>> {
        let mut lengths: Vec<Option<usize>> = vec![None; self.class_count];
        let set = |lengths: &mut Vec<Option<usize>>, class: usize, n: usize| -> Option<bool> {
            match lengths[class] {
                None => {
                    lengths[class] = Some(n);
                    Some(true)
                }
                Some(m) => (m == n).then_some(false),
            }
        };
        for &(read, s) in &self.len_reads {
            let Some(&i) = self.index.get(&s) else {
                continue;
            };
            if let Some(n) = self.raw_int(read).and_then(|v| v.to_usize()) {
                set(&mut lengths, self.class_of[i], n)?;
            }
        }
        for (i, shape) in self.shapes.iter().enumerate() {
            let class = self.class_of[i];
            match shape {
                Shape::Empty => set(&mut lengths, class, 0).map(|_| ())?,
                Shape::Unit(_) => set(&mut lengths, class, 1).map(|_| ())?,
                Shape::Opaque => {
                    if let Some(elems) = &self.concrete[i] {
                        set(&mut lengths, class, elems.len())?;
                    }
                }
                _ => {}
            }
        }
        // Each productive pass fixes at least one more class, so the class
        // count bounds the passes.
        for _ in 0..=self.class_count {
            let mut changed = false;
            for (i, shape) in self.shapes.iter().enumerate() {
                let class = self.class_of[i];
                match shape {
                    Shape::Concat(parts) => {
                        changed |= self.infer_concat_length(&mut lengths, class, parts)?;
                    }
                    Shape::Extract { src, start, count } => {
                        let Some(src_len) = lengths[self.class_of[*src]] else {
                            continue;
                        };
                        if let Some((_, n)) = self.extract_window(&lengths, *start, *count, src_len)
                        {
                            changed |= set(&mut lengths, class, n)?;
                        }
                    }
                    _ => {}
                }
            }
            if !changed {
                break;
            }
        }
        Some(lengths)
    }

    /// Length of a concatenation from its parts, or of its one unknown part
    /// (possibly repeated) from the class length. `Some(changed)`, or `None`
    /// on a contradiction.
    fn infer_concat_length(
        &self,
        lengths: &mut [Option<usize>],
        class: usize,
        parts: &[usize],
    ) -> Option<bool> {
        let mut known = 0usize;
        let mut unknown: Option<(usize, usize)> = None;
        for &p in parts {
            let pc = self.class_of[p];
            match lengths[pc] {
                Some(n) => known = known.checked_add(n)?,
                None => match unknown {
                    None => unknown = Some((pc, 1)),
                    Some((c, k)) if c == pc => unknown = Some((c, k + 1)),
                    Some(_) => return Some(false),
                },
            }
        }
        match (unknown, lengths[class]) {
            (None, Some(total)) => (total == known).then_some(false),
            (None, None) => {
                lengths[class] = Some(known);
                Some(true)
            }
            (Some((pc, k)), Some(total)) => {
                let rest = total.checked_sub(known)?;
                if rest % k != 0 {
                    return None;
                }
                lengths[pc] = Some(rest / k);
                Some(true)
            }
            (Some(_), None) => Some(false),
        }
    }
}
