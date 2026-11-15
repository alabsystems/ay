// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn euf_constructor_aliases_require_all_boolean_sources_to_agree() {
    for conflicting_source in 0..4 {
        let mut exec = fixture();
        let proxy = exec.ctx.terms.mk_var("bool_conflict_proxy", sort("Arg"));
        let flag = if conflicting_source == 3 {
            exec.ctx.terms.true_term()
        } else {
            exec.ctx.terms.mk_var("bool_conflict_field", Sort::Bool)
        };
        let ptr = bv(&mut exec, 0x2a);
        let funptr = bv(&mut exec, 0x7f);
        let constructor = app(&mut exec, "Placeholder", vec![ptr, funptr, flag], "Arg");
        let roots = [proxy, constructor];
        let mut model = model_with_classes(&[(proxy, "@Arg!bool"), (constructor, "@Arg!bool")]);
        let mut values = [true; 3];
        if conflicting_source == 3 {
            values = [false; 3]; // All raw rows conflict with literal true.
        } else {
            values[conflicting_source] = false;
        }
        model.sat_model = vec![values[0]];
        model.term_to_var.insert(flag, 0);
        model.bool_overrides.insert(flag, values[1]);
        let mut bool_overrides = HashMap::default();
        bool_overrides.insert(flag, values[2]);
        model.bv_model = Some(BvModel {
            values: HashMap::default(),
            term_to_bits: HashMap::default(),
            bool_overrides,
        });
        assert_eq!(
            exec.complete_euf_datatype_constructor_aliases(&mut model, &roots),
            0
        );
        assert_unpinned(&model, &roots);

        // Agreement restores a concrete candidate without changing its fields.
        model.sat_model[0] = true;
        assert_eq!(model.bool_overrides.insert(flag, true), Some(values[1]));
        assert_eq!(
            model
                .bv_model
                .as_mut()
                .unwrap()
                .bool_overrides
                .insert(flag, true),
            Some(values[2])
        );
        assert_eq!(
            exec.complete_euf_datatype_constructor_aliases(&mut model, &roots),
            1
        );
        assert_value(&model, proxy, &placeholder_value(0x2a));
    }
}

#[test]
fn euf_constructor_aliases_refuse_invalid_or_disagreeing_raw_bitvectors() {
    for (raw, literal_field) in [
        (BigInt::from(-1), false),
        (BigInt::from(1u8) << 1024usize, false),
        (BigInt::from(0x2bu8), true),
    ] {
        let mut exec = fixture();
        let proxy = exec.ctx.terms.mk_var("bv_conflict_proxy", sort("Arg"));
        let ptr = if literal_field {
            bv(&mut exec, 0x2a)
        } else {
            exec.ctx.terms.mk_var("bv_conflict_field", Sort::bitvec(8))
        };
        let funptr = bv(&mut exec, 0x7f);
        let flag = exec.ctx.terms.true_term();
        let constructor = app(&mut exec, "Placeholder", vec![ptr, funptr, flag], "Arg");
        let roots = [proxy, constructor];
        let mut model = model_with_classes(&[(proxy, "@Arg!bv"), (constructor, "@Arg!bv")]);
        let mut values = HashMap::default();
        values.insert(ptr, raw.clone());
        model.bv_model = Some(BvModel {
            values,
            term_to_bits: HashMap::default(),
            bool_overrides: HashMap::default(),
        });
        assert_eq!(
            exec.complete_euf_datatype_constructor_aliases(&mut model, &roots),
            0
        );
        assert_unpinned(&model, &roots);
        assert_eq!(
            model.bv_model.as_ref().unwrap().values.get(&ptr),
            Some(&raw)
        );

        assert_eq!(
            model
                .bv_model
                .as_mut()
                .unwrap()
                .values
                .insert(ptr, BigInt::from(0x2au8)),
            Some(raw)
        );
        assert_eq!(
            exec.complete_euf_datatype_constructor_aliases(&mut model, &roots),
            1
        );
        assert_value(&model, proxy, &placeholder_value(0x2a));
    }
}
