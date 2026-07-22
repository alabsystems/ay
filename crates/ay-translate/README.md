# ay-translate

`ay-translate` is the shared Rust translation layer for ay consumers that
already have their own sort and expression types.

It gives consumers one place to reuse:

- solver + variable/function caches
- fresh-name generation
- recursive AST lowering
- prebuilt operator constructors for common theories

The crate is intended for verification tools and other Rust applications that
wrap `ay_dpll::api::Solver` alongside their own `HashMap<Key, Term>` state.

## Core Types

- `TranslationContext<V>`: owning wrapper around `Solver` and translation state
- `TranslationState<V>`: reusable variable/function cache without solver
- `TranslationSession<'_, V>`: borrowed translation host for a solver that is
  owned elsewhere
- `TranslationHost<V>`: low-level host trait for operator builders
- `TranslationTermHost<V>`: recursive translation host trait used by
  `TermTranslator`
- `SortTranslator`: map consumer sorts to `ay_dpll::api::Sort`
- `TermTranslator`: recursively lower consumer AST nodes to
  `ay_dpll::api::Term`
- `ops`: prebuilt constructors for arithmetic, bitvectors, arrays, UF, strings,
  sequences, floating-point, and datatypes

## Host Choice

Use `TranslationContext<V>` when the translation layer owns the solver.

Use `TranslationState<V>` plus `TranslationSession<'_, V>` when a larger system
already owns the solver and only needs a borrowed translation pass.

The same `TermTranslator` implementation works against both host styles.
See:

- `examples/simple_translate.rs`
- `tests/group_translate/dual_host_6302.rs`

## Minimal Pattern

```rust
use ay_translate::ops::{self, Comparison};
use ay_translate::{
    Logic, Sort, SortTranslator, Term, TermTranslator, TranslationContext,
    TranslationTermHost,
};

#[derive(Clone, Copy)]
enum MySort {
    Bool,
    Int,
}

enum Expr {
    Int(i64),
    Var { name: String, sort: MySort },
    Eq(Box<Expr>, Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
}

#[derive(Default)]
struct Translator;

impl SortTranslator for Translator {
    type Sort = MySort;
    type Error = String;

    fn translate_sort(&self, sort: &Self::Sort) -> Result<Sort, Self::Error> {
        Ok(match sort {
            MySort::Bool => Sort::Bool,
            MySort::Int => Sort::Int,
        })
    }
}

impl TermTranslator for Translator {
    type Expr = Expr;
    type VarKey = String;
    type Error = String;

    fn translate<H: TranslationTermHost<Self::VarKey>>(
        &self,
        ctx: &mut H,
        expr: &Self::Expr,
    ) -> Result<Term, Self::Error> {
        match expr {
            Expr::Int(n) => Ok(ctx.solver().int_const(*n)),
            Expr::Var { name, sort } => {
                let sort = self.translate_sort(sort)?;
                Ok(ctx.get_or_declare(name.clone(), name, sort))
            }
            Expr::Eq(a, b) => {
                let a = self.translate(ctx, a)?;
                let b = self.translate(ctx, b)?;
                Ok(ops::compare(ctx, Comparison::Eq, a, b))
            }
            Expr::Add(a, b) => {
                let a = self.translate(ctx, a)?;
                let b = self.translate(ctx, b)?;
                Ok(ops::arith::add(ctx, a, b))
            }
        }
    }
}

let translator = Translator::default();
let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfLia);
let expr = Expr::Eq(
    Box::new(Expr::Add(Box::new(Expr::Int(1)), Box::new(Expr::Int(2)))),
    Box::new(Expr::Int(3)),
);
let term = translator.translate(&mut ctx, &expr)?;
ctx.assert_term(term);
assert!(ctx.check_sat().is_sat());
# Ok::<(), String>(())
```

## Borrowed Solver Pattern

If your integration already owns a `Solver`, keep that ownership and borrow it
through `TranslationSession`:

```rust
use ay_translate::{Logic, Solver, TranslationSession, TranslationState};

let mut solver = Solver::try_new(Logic::QfLia)?;
let mut state = TranslationState::<String>::new();
let mut session = TranslationSession::new(&mut solver, &mut state);

// Reuse the same TermTranslator implementation used with TranslationContext.
let term = translator.translate(&mut session, &expr)?;
session.try_assert_term(term)?;
assert!(session.check_sat().is_sat());
# Ok::<(), ay_translate::SolverError>(())
```

`TranslationContext::session()` is available when an owning caller wants to
temporarily borrow its internal state and use the session-style API.

## Embed Into Existing Encoder

Consumers with large encoders should embed `TranslationState`
as a sibling field next to their existing `Solver`, rather than replacing the
whole encoder with `TranslationContext`. Domain-specific metadata stays on the
encoder itself.

| Existing consumer field | New home |
|-------------------------|----------|
| `solver: Solver` | keep on the encoder |
| `HashMap<Key, Term>` var cache | `TranslationState<Key>` |
| `HashMap<String, FuncDecl>` function cache | `TranslationState<Key>` |
| type/heap/diagnostic metadata | keep on the encoder |

```rust
use ay_translate::{Solver, TranslationSession, TranslationState};

struct MyEncoder {
    solver: Solver,
    translate: TranslationState<String>,
    // Domain metadata stays here, not in TranslationState.
    var_types: HashMap<String, MyType>,
}

impl MyEncoder {
    fn session(&mut self) -> TranslationSession<'_, String> {
        TranslationSession::new(&mut self.solver, &mut self.translate)
    }

    fn lower_and_assert(&mut self, translator: &impl TermTranslator, expr: &Expr) {
        let mut session = self.session();
        let term = translator.translate(&mut session, expr).expect("translate");
        session.assert_term(term);
    }
}
```

Variable and function caches persist in `TranslationState` across sessions.
See `examples/embedded_encoder.rs` and
`tests/group_translate/embedded_state_4696.rs` for complete working code.

## Migration Hints

Common replacement patterns:

- `Solver` + `HashMap<Key, Term>` wrapper -> `TranslationContext<Key>`
- borrowed `&mut Solver` + temporary caches -> `TranslationState<Key>` +
  `TranslationSession<'_, Key>`
- custom sort lowering match -> `SortTranslator`
- custom recursive expression lowering -> `TermTranslator`
- hand-written binary/n-ary operator constructors -> `ops::*`

## Local Verification

```bash
cargo test -p ay-translate
cargo test -p ay-translate --release
cargo run -p ay-translate --example simple_translate
```
