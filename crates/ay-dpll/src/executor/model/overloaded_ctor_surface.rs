// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Re-readable spelling of printed datatype values (#overloaded-nil-surface).
//!
//! SMT-LIB 2.6 lets two datatypes declare a constructor of the same name
//! (§4.2.3). A NULLARY one is then ambiguous bare (z3 refuses `(cons B nil)`
//! when `L1` and `L2` both declare `nil`), and `(as nil L1)` (§3.6.4) selects
//! it, which is how z3 prints such a value.
//!
//! In [`ValueSpelling::Surface`] this module may ascribe a nullary
//! constructor whose surface name [`Executor::overloaded_nullary_ctors`]
//! collects, spelled by `ay_core::ascribed_constructor_spelling`, at the
//! positions whose sort [`Executor::ascribe_overloaded_ctors`] follows; in
//! [`ValueSpelling::Sorted`] it adds no ascription.
//! [`Executor::table_cell_surface`] gives the name, if any, to print for a
//! function-table cell.
//!
//! Printed text is not always read as it was meant: a name may print
//! unquoted (for example the constructor `|p\|q|` as `p|q`), and the
//! application of a constructor named `as` can have the text of an
//! ascription. So [`Executor::ascribe_overloaded_ctors`] returns a rewritten
//! value only where `crate::constructor_ascription::reads_as_bare` accepts
//! each ascribed atom and, for a compound value, the whole value, and
//! [`Executor::surface_response`] can fall back to the `Sorted` rendering of
//! the whole response.

use std::cell::OnceCell;

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::Sort;

use crate::executor::Executor;
use crate::executor_format::format_sort_surface;

/// Nesting bound of one rewritten value; deeper text is left as printed.
const MAX_DEPTH: usize = 4096;

/// One parsed node of a printed value, with its byte span in the source.
enum Node {
    Atom {
        start: usize,
        end: usize,
    },
    List {
        start: usize,
        end: usize,
        items: Vec<Node>,
    },
}

impl Node {
    fn span(&self) -> (usize, usize) {
        match self {
            Node::Atom { start, end } | Node::List { start, end, .. } => (*start, *end),
        }
    }
}

/// Parse one s-expression of `text` starting at `*pos` (after whitespace).
fn parse(text: &[u8], pos: &mut usize, depth: usize) -> Option<Node> {
    while *pos < text.len() && text[*pos].is_ascii_whitespace() {
        *pos += 1;
    }
    let start = *pos;
    match *text.get(start)? {
        b'(' => {
            if depth >= MAX_DEPTH {
                return None;
            }
            *pos += 1;
            let mut items = Vec::new();
            loop {
                while *pos < text.len() && text[*pos].is_ascii_whitespace() {
                    *pos += 1;
                }
                match *text.get(*pos)? {
                    b')' => {
                        *pos += 1;
                        return Some(Node::List {
                            start,
                            end: *pos,
                            items,
                        });
                    }
                    _ => items.push(parse(text, pos, depth + 1)?),
                }
            }
        }
        b')' => None,
        b'|' => {
            *pos += 1;
            while *text.get(*pos)? != b'|' {
                *pos += if text[*pos] == b'\\' { 2 } else { 1 };
            }
            *pos += 1;
            Some(Node::Atom { start, end: *pos })
        }
        b'"' => {
            *pos += 1;
            loop {
                if *text.get(*pos)? == b'"' {
                    *pos += 1;
                    if text.get(*pos) != Some(&b'"') {
                        break;
                    }
                }
                *pos += 1;
            }
            Some(Node::Atom { start, end: *pos })
        }
        _ => {
            while *pos < text.len()
                && !text[*pos].is_ascii_whitespace()
                && !matches!(text[*pos], b'(' | b')')
            {
                *pos += 1;
            }
            Some(Node::Atom { start, end: *pos })
        }
    }
}

/// The symbol an atom spells (quotes removed), or `None` for an atom that
/// is empty or starts with a digit, `"`, `#` or `-`.
fn atom_symbol(raw: &str) -> Option<String> {
    if let Some(inner) = raw.strip_prefix('|').and_then(|r| r.strip_suffix('|')) {
        return Some(inner.replace("\\|", "|").replace("\\\\", "\\"));
    }
    let first = raw.chars().next()?;
    (!first.is_ascii_digit() && !matches!(first, '"' | '#' | '-')).then(|| raw.to_string())
}

/// Who reads a printed `(get-value)` or `(get-model)` response
/// (#overloaded-nil-surface).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ValueSpelling {
    /// SMT-LIB text that leaves the solver, for example the response of the
    /// command, `Solver::try_get_model_str` or `Solver::values_smtlib`. Its
    /// reader may have only the text, so an overloaded nullary constructor
    /// may be ascribed, for example `(as nil L1)`.
    Surface,
    /// Text read inside this process by a reader that holds the solver, for
    /// example a typed decoder or `Solver::try_get_model_str_for_decoder`.
    /// This module adds no ascription here: a typed decoder already has the
    /// sort, and a whole-model reader then has no ascription of this
    /// module's to tell from the application of a constructor named `as`.
    Sorted,
}

/// What this module may ascribe in one print call: the surface names
/// [`Executor::overloaded_nullary_ctors`] collects, none in `Sorted`.
pub(super) struct OverloadedCtors {
    /// The surface names.
    names: HashSet<String>,
    /// The printed names of the constructors, resolved once, on first use:
    /// `Context::datatype_output_names` takes a census of every datatype
    /// member.
    printed: OnceCell<PrintedCtors>,
}

/// The name `DatatypeOutputNames::name` gives each constructor
/// ([`OverloadedCtors::printed`]).
struct PrintedCtors {
    /// Per datatype carrier, that name of each constructor to its identity.
    by_carrier: HashMap<String, HashMap<String, String>>,
    /// Each constructor identity (for example `__ay_overload_N`, or
    /// `<name>@<instance>` of a member of a parametric instance) to which
    /// `DatatypeOutputNames::name` gives another name, to its carrier and
    /// that name.
    renamed: HashMap<String, (String, String)>,
}

impl OverloadedCtors {
    fn new(names: HashSet<String>) -> Self {
        Self {
            names,
            printed: OnceCell::new(),
        }
    }

    /// Whether there is no constructor to ascribe.
    pub(super) fn is_empty(&self) -> bool {
        self.names.is_empty()
    }

    fn mentioned_in(&self, text: &str) -> bool {
        self.names.iter().any(|name| text.contains(name.as_str()))
    }

    fn printed(&self, exec: &Executor) -> &PrintedCtors {
        self.printed.get_or_init(|| {
            let names = exec.ctx.datatype_output_names();
            let mut by_carrier: HashMap<String, HashMap<String, String>> = HashMap::default();
            let mut renamed = HashMap::default();
            for (carrier, ctors) in exec.ctx.datatype_iter() {
                let printed = by_carrier.entry(carrier.to_string()).or_default();
                for ctor in ctors {
                    let name = names.name(ctor);
                    if name != ctor.as_str() {
                        renamed.insert(ctor.clone(), (carrier.to_string(), name.to_string()));
                    }
                    // Within a carrier, the first constructor of a name.
                    printed
                        .entry(name.to_string())
                        .or_insert_with(|| ctor.clone());
                }
            }
            PrintedCtors {
                by_carrier,
                renamed,
            }
        })
    }

    /// The identity of the constructor of `carrier` printed as `name`.
    fn constructor(&self, exec: &Executor, carrier: &str, name: &str) -> Option<&str> {
        self.printed(exec)
            .by_carrier
            .get(carrier)?
            .get(name)
            .map(String::as_str)
    }

    /// The name `DatatypeOutputNames::name` gives the constructor `identity`
    /// of `carrier`, when that is not `identity` itself.
    fn printed_name(&self, exec: &Executor, carrier: &str, identity: &str) -> Option<&str> {
        let (owner, name) = self.printed(exec).renamed.get(identity)?;
        (owner == carrier).then_some(name.as_str())
    }
}

impl Executor {
    /// What this module may ascribe in `spelling`:
    /// [`Self::overloaded_nullary_ctors`] in `Surface`, nothing in `Sorted`.
    pub(super) fn overloaded_ctors_for(&self, spelling: ValueSpelling) -> OverloadedCtors {
        match spelling {
            ValueSpelling::Surface => self.overloaded_nullary_ctors(),
            ValueSpelling::Sorted => OverloadedCtors::new(HashSet::default()),
        }
    }

    /// The surface names `Context::overloaded_surface_name` gives nullary
    /// constructors.
    fn overloaded_nullary_ctors(&self) -> OverloadedCtors {
        let mut out = HashSet::default();
        for (_, ctors) in self.ctx.datatype_iter() {
            for ctor in ctors {
                let nullary = self
                    .ctx
                    .constructor_selector_info(ctor)
                    .is_none_or(<[_]>::is_empty);
                if nullary {
                    if let Some(surface) = self.ctx.overloaded_surface_name(ctor) {
                        out.insert(surface.to_string());
                    }
                }
            }
        }
        OverloadedCtors::new(out)
    }

    /// The name to print for the function-table cell `cell` of `sort`
    /// (#overloaded-nil-surface), or `None` to keep the cell as it is.
    ///
    /// A cell can hold a constructor's identity that is no symbol of the
    /// script, for example `__ay_overload_N`. In both spellings this returns
    /// the name `DatatypeOutputNames::name` gives `cell` in `sort`'s carrier
    /// when the frontend records a surface name for `cell`, that name differs
    /// from `cell`, and `crate::constructor_ascription::reads_as_one_symbol`
    /// accepts it. Written unquoted into the `ite` chain, a refused name such
    /// as `x(y` or `true` would not read back as the constructor.
    pub(super) fn table_cell_surface(
        &self,
        cell: &str,
        sort: &Sort,
        overloaded: &OverloadedCtors,
    ) -> Option<String> {
        // A cell with no surface name on record is left as it is.
        self.ctx.dt_surface_name(cell)?;
        let carrier = match sort {
            Sort::Datatype(dt) => dt.name.as_str(),
            Sort::Uninterpreted(name) => name.as_str(),
            _ => return None,
        };
        overloaded
            .printed_name(self, carrier, cell)
            .filter(|name| crate::constructor_ascription::reads_as_one_symbol(name))
            .map(str::to_string)
    }

    /// The response `print` renders for a reader outside the solver: its
    /// [`ValueSpelling::Surface`] rendering, or its [`ValueSpelling::Sorted`]
    /// one when the `Surface` rendering contains `(as `,
    /// [`Self::overloaded_nullary_ctors`] is non-empty, the two renderings
    /// differ, and `crate::constructor_ascription::reads_as_bare` does not
    /// take the `Surface` one as the `Sorted` one. The check is of the whole
    /// response because an unquoted name (`y|`) can pair with the bars of an
    /// ascribed sort (`(as nil |My List|)`) lines away.
    pub(super) fn surface_response(&self, print: impl Fn(ValueSpelling) -> String) -> String {
        let surface = print(ValueSpelling::Surface);
        if !surface.contains("(as ") {
            return surface;
        }
        let overloaded = self.overloaded_nullary_ctors();
        if overloaded.is_empty() {
            return surface;
        }
        let bare = print(ValueSpelling::Sorted);
        if bare == surface || crate::constructor_ascription::reads_as_bare(&bare, &surface) {
            surface
        } else {
            bare
        }
    }

    /// `value` as printed for a term of `sort`, either as is or with the
    /// spelling `ay_core::ascribed_constructor_spelling` gives under `S` in
    /// place of each unquoted atom `c` of `overloaded` that, at a position
    /// whose sort `S` the rewrite follows, is the printed name
    /// ([`OverloadedCtors::printed`]) of a nullary constructor of `S`, where
    /// `crate::constructor_ascription::reads_as_bare` accepts that spelling.
    /// It is returned as is when, for example, it is no term or
    /// `reads_as_bare` rejects the rewritten value.
    pub(super) fn ascribe_overloaded_ctors(
        &self,
        value: &str,
        sort: &Sort,
        overloaded: &OverloadedCtors,
    ) -> String {
        if overloaded.is_empty() || !overloaded.mentioned_in(value) {
            return value.to_string();
        }
        let bytes = value.as_bytes();
        let mut pos = 0;
        let Some(node) = parse(bytes, &mut pos, 0) else {
            return value.to_string();
        };
        // A value that is not one `ay_core::smtlib_term_len` term stays as
        // printed, for example `(rec p|q nil)`, where `|q nil)` opens a
        // quoted symbol that never closes.
        let is_term = ay_core::smtlib_term_len(value.trim()) == Some(value.trim().len());
        if is_term && value[pos..].trim().is_empty() {
            if let Some(rewritten) = self.ascribe_node(value, &node, sort, overloaded) {
                // A lone atom was checked where it was ascribed.
                if matches!(node, Node::Atom { .. })
                    || crate::constructor_ascription::reads_as_bare(value, &rewritten)
                {
                    return rewritten;
                }
            }
        }
        value.to_string()
    }

    /// [`Self::ascribe_overloaded_ctors`] on the value `v` of each constant
    /// definition `(define-fun c () S v)` whose printed sort `S` reads back to
    /// a sort (`Self::printed_symbol_sorts`, or an atom that names a
    /// datatype). Other definitions are left as they are.
    pub(super) fn ascribe_overloaded_constant_definitions(
        &self,
        definitions: &mut [String],
        overloaded: &OverloadedCtors,
    ) {
        if overloaded.is_empty() {
            return;
        }
        // The sort a definition prints, back to the sort it was printed from.
        // Built on the first definition that mentions an overloaded name.
        let mut printed_sorts: Option<HashMap<String, &Sort>> = None;
        for def in definitions.iter_mut() {
            if !overloaded.mentioned_in(def) {
                continue;
            }
            let printed_sorts = printed_sorts.get_or_insert_with(|| self.printed_symbol_sorts());
            if let Some(rewritten) =
                self.ascribe_constant_definition(def, printed_sorts, overloaded)
            {
                *def = rewritten;
            }
        }
    }

    /// Every result and argument sort of a declared symbol, keyed by its
    /// `format_sort_surface` text, so that a printed sort such as
    /// `(List Int)` or `(Array Int L2)` can be read back.
    fn printed_symbol_sorts(&self) -> HashMap<String, &Sort> {
        let mut out = HashMap::default();
        for (_, info) in self.ctx.symbol_iter() {
            for sort in std::iter::once(&info.sort).chain(&info.arg_sorts) {
                out.entry(format_sort_surface(&self.ctx, sort))
                    .or_insert(sort);
            }
        }
        out
    }

    fn ascribe_constant_definition(
        &self,
        def: &str,
        printed_sorts: &HashMap<String, &Sort>,
        overloaded: &OverloadedCtors,
    ) -> Option<String> {
        let mut pos = 0;
        let Node::List { items, .. } = parse(def.as_bytes(), &mut pos, 0)? else {
            return None;
        };
        let [Node::Atom { start: k0, end: k1 }, _, Node::List { items: params, .. }, sort, value] =
            items.as_slice()
        else {
            return None;
        };
        if &def[*k0..*k1] != "define-fun" || !params.is_empty() {
            return None;
        }
        let (s0, s1) = sort.span();
        let named;
        let sort = match printed_sorts.get(&def[s0..s1]) {
            Some(sort) => *sort,
            // A sort no declared symbol has: an atom that names a datatype
            // still directs the rewrite.
            None => {
                let Node::Atom { .. } = sort else {
                    return None;
                };
                let carrier = atom_symbol(&def[s0..s1])?;
                self.ctx.datatype_constructors(&carrier)?;
                named = Sort::Uninterpreted(carrier);
                &named
            }
        };
        let (v0, v1) = value.span();
        let printed = &def[v0..v1];
        let ascribed = self.ascribe_overloaded_ctors(printed, sort, overloaded);
        (ascribed != printed).then(|| format!("{}{ascribed}{}", &def[..v0], &def[v1..]))
    }

    /// The array form of [`Self::ascribe_node`]: a constant array
    /// `((as const S) v)` descends into `v` with the element sort, and a
    /// store `(store a i v)` into `a`, `i` and `v` with the array, index and
    /// element sorts. Any other array spelling is left as printed.
    fn ascribe_array_node(
        &self,
        src: &str,
        node: &Node,
        sort: &Sort,
        overloaded: &OverloadedCtors,
    ) -> Option<String> {
        let (index, element) = (sort.array_index()?, sort.array_element()?);
        let Node::List { items, .. } = node else {
            return None;
        };
        let text = |node: &Node| {
            let (start, end) = node.span();
            &src[start..end]
        };
        let children: Vec<(&Node, &Sort)> = match items.as_slice() {
            [Node::List { items: head, .. }, default]
                if matches!(head.as_slice(), [Node::Atom { .. }, Node::Atom { .. }, _]
                    if text(&head[0]) == "as" && text(&head[1]) == "const") =>
            {
                vec![(default, element)]
            }
            [head @ Node::Atom { .. }, base, at, value] if text(head) == "store" => {
                vec![(base, sort), (at, index), (value, element)]
            }
            _ => return None,
        };
        splice(
            src,
            node,
            children.into_iter().map(|(child, child_sort)| {
                (child, self.ascribe_node(src, child, child_sort, overloaded))
            }),
        )
    }

    /// `Some(text)` when `node` (of `sort`) needs a different spelling.
    fn ascribe_node(
        &self,
        src: &str,
        node: &Node,
        sort: &Sort,
        overloaded: &OverloadedCtors,
    ) -> Option<String> {
        let carrier = match sort {
            Sort::Datatype(dt) => dt.name.as_str(),
            Sort::Uninterpreted(name) => name.as_str(),
            Sort::Array(_) => return self.ascribe_array_node(src, node, sort, overloaded),
            _ => return None,
        };
        self.ctx.datatype_constructors(carrier)?;
        match node {
            Node::Atom { start, end } => {
                let bare = &src[*start..*end];
                let name = atom_symbol(bare)?;
                // Only an unquoted atom: `ay_core::bare_constructor_spelling`
                // takes an ascription back as the name unquoted, so a quoted
                // atom (`|pop|`) would not read back as itself.
                if name != bare || !overloaded.names.contains(&name) {
                    return None;
                }
                let ctor = overloaded.constructor(self, carrier, &name)?;
                let nullary = self
                    .ctx
                    .constructor_selector_info(ctor)
                    .is_none_or(<[_]>::is_empty);
                if !nullary {
                    return None;
                }
                // The spelling `ay_core::ascribed_constructor_spelling`
                // gives, where `reads_as_bare` accepts it; otherwise the
                // constructor stays bare.
                let ascribed = ay_core::ascribed_constructor_spelling(
                    &name,
                    &format_sort_surface(&self.ctx, sort),
                )?;
                crate::constructor_ascription::reads_as_bare(bare, &ascribed).then_some(ascribed)
            }
            Node::List { items, .. } => {
                let (head, args) = items.split_first()?;
                let Node::Atom { start, end } = head else {
                    return None;
                };
                let name = atom_symbol(&src[*start..*end])?;
                let ctor = overloaded.constructor(self, carrier, &name)?;
                let fields = self.ctx.constructor_selector_info(ctor)?;
                if fields.len() != args.len() {
                    return None;
                }
                splice(
                    src,
                    node,
                    args.iter().zip(fields).map(|(arg, (_, field_sort))| {
                        (arg, self.ascribe_node(src, arg, field_sort, overloaded))
                    }),
                )
            }
        }
    }
}

/// The printed text of `node` with each rewritten child in place of its own
/// span, in order; every other byte (the head, the spacing between tokens) is
/// the printed one. `None` when no child was rewritten.
fn splice<'n>(
    src: &str,
    node: &Node,
    children: impl Iterator<Item = (&'n Node, Option<String>)>,
) -> Option<String> {
    let (start, end) = node.span();
    let mut out = String::new();
    let mut copied = start;
    for (child, rewritten) in children {
        if let Some(rewritten) = rewritten {
            let (child_start, child_end) = child.span();
            out.push_str(&src[copied..child_start]);
            out.push_str(&rewritten);
            copied = child_end;
        }
    }
    (copied != start).then(|| {
        out.push_str(&src[copied..end]);
        out
    })
}

#[cfg(test)]
mod tests {
    use crate::Executor;
    use ay_frontend::parse;
    use ntest::timeout;

    /// The outputs `execute_all` returns for `src`, once in each posture.
    fn run_both(src: &str) -> Vec<Vec<String>> {
        [true, false]
            .into_iter()
            .map(|z3_mode| {
                let mut exec = Executor::new();
                exec.set_competition_mode(z3_mode);
                exec.execute_all(&parse(src).expect("parse"))
                    .expect("execute")
            })
            .collect()
    }

    /// Whether `printed` still names `nil` outside an `(as nil L1)`,
    /// `(as nil L2)` or `(as nil (List Int))` ascription.
    fn bare_nil_remains(printed: &str) -> bool {
        printed
            .replace("(as nil L1)", "")
            .replace("(as nil L2)", "")
            .replace("(as nil (List Int))", "")
            .contains("nil")
    }

    /// Two list sorts both declare `nil`: here no `nil` of the values or the
    /// model is left unascribed, and `y`'s is `(as nil L2)`.
    #[test]
    #[timeout(60000)]
    fn overloaded_nil_is_ascribed_in_values_and_models() {
        for out in run_both(
            "(set-logic ALL)\n\
            (declare-datatypes ((E 0)) (((A) (B))))\n\
            (declare-datatypes ((L1 0)) (((cons (hd E) (tl L1)) (nil))))\n\
            (declare-datatypes ((L2 0)) (((cons (hd Int) (tl L2)) (nil))))\n\
            (declare-const x L1) (declare-const y L2)\n\
            (assert (not (= x (as nil L1)))) (assert (= (hd x) B))\n\
            (assert (= y (as nil L2)))\n\
            (check-sat)\n\
            (get-value (x y (tl x)))\n\
            (get-model)\n",
        ) {
            assert_eq!(out[0], "sat");
            assert!(!bare_nil_remains(&out[1]), "{}", out[1]);
            assert!(out[1].contains("(y (as nil L2))"), "{}", out[1]);
            assert!(out[1].contains("(as nil L1)"), "{}", out[1]);
            let model = &out[2];
            assert!(
                model.contains("(define-fun y () L2 (as nil L2))"),
                "{model}"
            );
            assert!(!bare_nil_remains(model), "{model}");
        }
    }

    /// An enumeration of 4000 constructors and then `shared`, which a second
    /// datatype also declares: here the 200 constants that hold `shared`
    /// print ascribed in the model and the values within the timeout.
    #[test]
    #[timeout(30000)]
    fn ascribing_the_last_constructor_of_a_wide_enumeration_is_not_per_value() {
        use std::fmt::Write as _;
        let (constructors, constants) = (4000, 200);
        let mut src = String::from("(set-logic ALL)\n(declare-datatypes ((A 0)) ((");
        for at in 0..constructors {
            write!(src, "(c{at}) ").expect("write");
        }
        src.push_str("(shared))))\n(declare-datatypes ((B 0)) (((z) (shared))))\n");
        for at in 0..constants {
            writeln!(
                src,
                "(declare-const x{at} A) (assert (= x{at} (as shared A)))"
            )
            .expect("write");
        }
        src.push_str(
            "(declare-const b B) (assert (= b (as shared B)))\n(check-sat)\n(get-model)\n",
        );
        src.push_str("(get-value (");
        for at in 0..constants {
            write!(src, "x{at} ").expect("write");
        }
        src.push_str("b))\n");
        for out in run_both(&src) {
            assert_eq!(out[0], "sat");
            let model = &out[1];
            assert_eq!(model.matches("A (as shared A))").count(), constants);
            assert!(
                model.contains("(define-fun b () B (as shared B))"),
                "{model}"
            );
            let values = &out[2];
            assert_eq!(values.matches(" (as shared A))").count(), constants);
            assert!(values.contains("(b (as shared B))"), "{values}");
        }
    }

    /// Here `nil` of `(List Int)` prints as `(as nil (List Int))`, as the
    /// value of `z` and nested in `v`, in `(get-value)` and `(get-model)`.
    #[test]
    #[timeout(60000)]
    fn parametric_nil_is_ascribed_under_its_sort_application() {
        for out in run_both(
            "(set-logic ALL)\n\
            (declare-datatypes ((List 1)) ((par (T) ((cons (hd T) (tl (List T))) (nil)))))\n\
            (declare-datatypes ((L2 0)) (((cons (hd Int) (tl L2)) (nil))))\n\
            (declare-datatypes ((W 0)) (((w (f1 (List Int)) (f2 L2)))))\n\
            (declare-const v W) (declare-const z (List Int))\n\
            (assert (= v (w (as nil (List Int)) (as nil L2))))\n\
            (assert (= z (as nil (List Int))))\n\
            (check-sat)\n\
            (get-value (z v))\n\
            (get-model)\n",
        ) {
            assert_eq!(out[0], "sat");
            assert_eq!(
                out[1],
                "((z (as nil (List Int))) (v (w (as nil (List Int)) (as nil L2))))"
            );
            let model = &out[2];
            assert!(
                model.contains("(define-fun z () (List Int) (as nil (List Int)))"),
                "{model}"
            );
            assert!(
                model.contains("(define-fun v () W (w (as nil (List Int)) (as nil L2)))"),
                "{model}"
            );
            assert!(!bare_nil_remains(model), "{model}");
        }
    }

    /// Here the array values leave no `nil` unascribed, as indices and as
    /// elements, in `(get-value)` and in `(get-model)`.
    #[test]
    #[timeout(60000)]
    fn overloaded_nil_is_ascribed_inside_array_values() {
        for out in run_both(
            "(set-logic ALL)\n\
            (declare-datatypes ((L1 0)) (((cons (hd Bool) (tl L1)) (nil))))\n\
            (declare-datatypes ((L2 0)) (((cons (hd Int) (tl L2)) (nil))))\n\
            (declare-const a (Array Int L2)) (declare-const b (Array L1 Int))\n\
            (assert (= (select a 3) (as nil L2)))\n\
            (assert (= (select a 4) (cons 1 (as nil L2))))\n\
            (assert (= (select b (as nil L1)) 7))\n\
            (assert (= (select b (cons true (as nil L1))) 8))\n\
            (check-sat)\n\
            (get-value (a b))\n\
            (get-model)\n",
        ) {
            assert_eq!(out[0], "sat");
            for printed in [&out[1], &out[2]] {
                assert!(!bare_nil_remains(printed), "{printed}");
                assert!(printed.contains(" 3 (as nil L2))"), "{printed}");
                assert!(printed.contains("(cons 1 (as nil L2))"), "{printed}");
                assert!(printed.contains(" (as nil L1) 7)"), "{printed}");
                assert!(printed.contains("(cons true (as nil L1)) 8)"), "{printed}");
            }
        }
    }

    /// Uninterpreted functions over two list sorts that both declare `nil`:
    /// here neither response leaves a `nil` unascribed or holds
    /// `__ay_overload`.
    #[test]
    #[timeout(60000)]
    fn overloaded_nil_is_ascribed_in_function_tables() {
        for out in run_both(
            "(set-logic ALL)\n\
            (declare-datatypes ((E 0)) (((A) (B))))\n\
            (declare-datatypes ((L1 0)) (((cons (hd E) (tl L1)) (nil))))\n\
            (declare-datatypes ((L2 0)) (((cons (hd Int) (tl L2)) (nil))))\n\
            (declare-fun f (L2) L2) (declare-fun g (Int) L1) (declare-fun h (L1 Int) Int)\n\
            (declare-const x L1) (declare-const y L2)\n\
            (assert (not (= x (as nil L1)))) (assert (= (hd x) B))\n\
            (assert (= y (as nil L2)))\n\
            (assert (= (f y) (as nil L2)))\n\
            (assert (= (g 0) (as nil L1))) (assert (= (g 1) x))\n\
            (assert (= (h (as nil L1) 2) 5)) (assert (= (h x 2) 6))\n\
            (check-sat)\n\
            (get-model)\n\
            (get-value ((hd (as nil L2)) (tl (as nil L2))))\n",
        ) {
            assert_eq!(out[0], "sat");
            let model = &out[1];
            assert!(!bare_nil_remains(model), "{model}");
            assert!(model.contains("(= x0 0) (as nil L1) "), "{model}");
            assert!(
                model.contains("(and (= x0 (as nil L1)) (= x1 2)) 5 "),
                "{model}"
            );
            assert!(
                model.contains("(define-fun f ((x0 L2)) L2\n    (as nil L2))"),
                "{model}"
            );
            assert!(!model.contains("__ay_overload"), "{model}");
            assert!(!out[2].contains("__ay_overload"), "{}", out[2]);
            assert!(out[2].starts_with("(((hd (as nil L2)) "), "{}", out[2]);
            assert!(!bare_nil_remains(&out[2]), "{}", out[2]);
        }
    }

    /// Here `nil` of the one datatype `L` prints bare in `(get-value)`.
    #[test]
    #[timeout(60000)]
    fn unique_nil_prints_bare() {
        for out in run_both(
            "(set-logic ALL)\n\
            (declare-datatypes ((L 0)) (((cons (hd Int) (tl L)) (nil))))\n\
            (declare-const x L) (assert (= x nil))\n\
            (check-sat) (get-value (x))\n",
        ) {
            assert_eq!(out, ["sat", "((x nil))"]);
        }
    }
}
