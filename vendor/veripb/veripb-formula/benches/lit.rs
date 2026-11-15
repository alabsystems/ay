use criterion::{Criterion, criterion_group, criterion_main};
use rand::prelude::*;

use veripb_formula::prelude::*;

fn add_lit(num_lits: usize) {
    let mut rng = rand::rng();
    let ber = rand::distr::Bernoulli::new(0.5).unwrap();

    for idx in 0..num_lits {
        Lit::from_var(idx, ber.sample(&mut rng));
    }
}

fn negate(num_iter: usize) {
    let mut lit = Lit::from_var(0, false);
    let mut rng = rand::rng();
    let ber = rand::distr::Bernoulli::new(0.5).unwrap();
    for _ in 0..num_iter {
        if ber.sample(&mut rng) {
            lit.negate();
        }
    }
}

fn get_negated_polarity(num_iter: usize) {
    let mut rng = rand::rng();
    let ber = rand::distr::Bernoulli::new(0.5).unwrap();

    for idx in 0..num_iter {
        let mut lit = Lit::from_var(idx, ber.sample(&mut rng));
        lit.negate();

        let negation = lit.is_negated();
        if negation {
            lit.negate();
        }
        lit.is_negated();
    }
}

fn add_lits_get_polarity(num_iter: usize) {
    let mut vec = Vec::with_capacity(num_iter);
    let mut rng = rand::rng();
    let ber = rand::distr::Bernoulli::new(0.5).unwrap();

    for idx in 0..num_iter {
        vec.push(Lit::from_var(idx, ber.sample(&mut rng)));
    }

    for lit in vec.iter_mut() {
        if lit.is_negated() {
            lit.negate();
        }
    }

    for lit in vec {
        if lit.is_negated() {
            panic!();
        }
    }
}

fn lit_black_box(num_iter: usize) {
    let mut vec = Vec::with_capacity(num_iter);
    for idx in 0..num_iter {
        let mut lit = Lit::from_var(std::hint::black_box(idx), std::hint::black_box(false));
        lit.negate();
        lit.get_var();
        lit.is_negated();
        vec.push(lit);
    }

    for lit in vec.iter_mut() {
        if lit.is_negated() {
            lit.negate();
            lit.get_var();
        }
    }
}

fn lit_assignment(num_iter: usize) {
    let mut assign: Assignment<BooleanVar> = Assignment::with_size(num_iter);
    for idx in 0..num_iter {
        let lit = Lit::from_var(std::hint::black_box(idx), std::hint::black_box(false));
        assign.set_lit_value(lit, BoolValue::Assigned(false));
        assign.get_lit_value(lit);
        assign.set_lit_value(lit, BoolValue::Assigned(true));
        assign.get_lit_value(lit);
        assign.set_lit_value(lit, BoolValue::Unassigned);
        assign.get_lit_value(lit);
    }

    for idx in 0..num_iter {
        let lit = Lit::from_var(std::hint::black_box(idx), std::hint::black_box(true));
        assign.set_lit_value(lit, BoolValue::Assigned(false));
        assign.get_lit_value(lit);
        assign.set_lit_value(lit, BoolValue::Assigned(true));
        assign.get_lit_value(lit);
        assign.set_lit_value(lit, BoolValue::Unassigned);
        assign.get_lit_value(lit);
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("add lits", |b| {
        b.iter(|| add_lit(std::hint::black_box(1_000_000)))
    });
    c.bench_function("negate", |b| {
        b.iter(|| negate(std::hint::black_box(1_000_000)))
    });
    c.bench_function("get negated polarity", |b| {
        b.iter(|| get_negated_polarity(std::hint::black_box(1_000_000)))
    });
    c.bench_function("add lits get polarity", |b| {
        b.iter(|| add_lits_get_polarity(std::hint::black_box(1_000_000)))
    });
    c.bench_function("lit black box", |b| {
        b.iter(|| lit_black_box(std::hint::black_box(1_000_000)))
    });
    c.bench_function("lit assignment", |b| {
        b.iter(|| lit_assignment(std::hint::black_box(1_000_000)))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
