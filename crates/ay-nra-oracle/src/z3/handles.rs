// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `z3.rs`; these distinct transparent wrappers preserve
// the C pointer ABI while making cross-kind handle mistakes fail to type-check.

macro_rules! raw_handle {
    ($name:ident) => {
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        struct $name(*mut c_void);
    };
}

raw_handle!(RawConfig);
raw_handle!(RawContext);
raw_handle!(RawSort);
raw_handle!(RawSymbol);
raw_handle!(RawAstVector);
raw_handle!(RawAst);

trait NullableHandle: Copy {
    fn is_null(self) -> bool;
}

macro_rules! nullable_handle {
    ($($name:ident),+ $(,)?) => {
        $(
            impl NullableHandle for $name {
                fn is_null(self) -> bool {
                    self.0.is_null()
                }
            }
        )+
    };
}

nullable_handle!(
    RawConfig,
    RawContext,
    RawSort,
    RawSymbol,
    RawAstVector,
    RawAst
);
