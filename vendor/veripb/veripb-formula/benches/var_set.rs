use criterion::{Criterion, criterion_group, criterion_main};

use veripb_formula::prelude::*;

fn add_vars(num_vars: usize, num_iter: usize) {
    let mut var_set = VarNameManager::with_capacity(num_vars);
    let mut assignment: Assignment<BooleanVar> = Assignment::default();
    for idx in 0..num_vars {
        let var = var_set.add_by_name(&idx.to_string());
        assignment.resize(var_set.len());
        assignment.set_value(var, BoolValue::Assigned(true));
        assert_eq!(assignment.get_value(var), BoolValue::Assigned(true));
        for _ in 0..num_iter {
            let var2 = var;
            assignment.set_value(var2, BoolValue::Assigned(false));
            assert_eq!(assignment.get_value(var), BoolValue::Assigned(false));
        }
    }
}

fn add_same_var(num_vars: usize, num_iter: usize) {
    let mut var_set = VarNameManager::with_capacity(num_vars);
    let mut assignment: Assignment<BooleanVar> = Assignment::default();
    for _ in 0..num_vars {
        let var = var_set.add_by_name("x1");
        assignment.resize(var_set.len());
        assignment.set_value(var, BoolValue::Assigned(true));
        assert_eq!(assignment.get_value(var), BoolValue::Assigned(true));
        for _ in 0..num_iter {
            let var2 = var;
            assignment.set_value(var2, BoolValue::Assigned(false));
            assert_eq!(assignment.get_value(var), BoolValue::Assigned(false));
        }
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("add 100_000 vars", |b| {
        b.iter(|| add_vars(std::hint::black_box(100_000), std::hint::black_box(100)))
    });
    c.bench_function("add 100_000 same var", |b| {
        b.iter(|| add_same_var(std::hint::black_box(100_000), std::hint::black_box(100)))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
