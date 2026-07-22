// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Runtime loading of a Z3-ABI shared library.
//!
//! Nothing here is linked at build time. Both the AY library and libz3 are
//! opened with `dlopen` at runtime (`RTLD_NOW | RTLD_LOCAL`) so that their
//! identical `Z3_*` symbols live in separate namespaces and do not collide,
//! and so that an outsider can point this tool at ANY two `.dylib`/`.so`
//! files without recompiling.

use std::collections::BTreeSet;
use std::ffi::c_void;
use std::os::raw::c_char;
use std::path::Path;
use std::process::Command;

#[cfg(unix)]
pub(crate) use libloading::os::unix::Library;
// Windows: LoadLibrary/GetProcAddress resolve exports strictly per-module, so
// the RTLD_LOCAL isolation this tool depends on holds there by construction.
#[cfg(windows)]
pub(crate) use libloading::os::windows::Library;

/// Opaque `Z3_context` / `Z3_config` handle. The real layout is private to the
/// solver; we only ever pass these pointers back to the same library.
pub(crate) type Z3Ptr = *mut c_void;

pub(crate) type MkConfigFn = unsafe extern "C" fn() -> Z3Ptr;
pub(crate) type MkContextFn = unsafe extern "C" fn(Z3Ptr) -> Z3Ptr;
pub(crate) type DelConfigFn = unsafe extern "C" fn(Z3Ptr);
pub(crate) type DelContextFn = unsafe extern "C" fn(Z3Ptr);
/// `Z3_string Z3_eval_smtlib2_string(Z3_context, Z3_string)` — runs an
/// SMT-LIB2 script and returns the concatenated textual output of its
/// commands. The returned string is owned by the context, so callers MUST
/// copy it before deleting the context.
pub(crate) type EvalFn = unsafe extern "C" fn(Z3Ptr, *const c_char) -> *const c_char;

/// The five raw C entry points needed to run a script through one solver.
///
/// Every field is a bare function pointer (an address inside the loaded
/// library), which is `Send`, so the whole struct can be moved into a worker
/// thread for the per-file timebox. Callers must keep the owning [`Library`]
/// alive for as long as any `SolverApi` copy is in use.
#[derive(Clone, Copy)]
pub(crate) struct SolverApi {
    pub(crate) mk_config: MkConfigFn,
    pub(crate) mk_context: MkContextFn,
    pub(crate) del_config: DelConfigFn,
    pub(crate) del_context: DelContextFn,
    pub(crate) eval: EvalFn,
}

/// `dlopen(path, RTLD_NOW | RTLD_LOCAL)`.
///
/// `RTLD_LOCAL` is essential: both the AY library and libz3 export the same
/// `Z3_*` symbols, and without local scoping the second `dlopen` would resolve
/// against the first library's already-global symbols.
#[cfg(unix)]
pub(crate) fn open_local(path: &Path) -> Result<Library, String> {
    // SAFETY: `dlopen` of an arbitrary path. The loaded library runs its own
    // initializers; we treat it as an opaque Z3-ABI provider.
    unsafe {
        Library::open(Some(path), libc::RTLD_NOW | libc::RTLD_LOCAL)
            .map_err(|e| format!("dlopen {}: {e}", path.display()))
    }
}

/// Windows counterpart of the `dlopen` above. No flags are needed: DLL
/// exports never enter a process-global namespace, so two libraries with
/// identical `Z3_*` exports stay isolated exactly as `RTLD_LOCAL` provides
/// on Unix.
#[cfg(windows)]
pub(crate) fn open_local(path: &Path) -> Result<Library, String> {
    // SAFETY: `LoadLibrary` of an arbitrary path. The loaded library runs its
    // own initializers; we treat it as an opaque Z3-ABI provider.
    unsafe { Library::new(path).map_err(|e| format!("LoadLibrary {}: {e}", path.display())) }
}

/// Resolve the five script-evaluation entry points from an already-open
/// library. Copies each function pointer out of the borrowing `Symbol`; this
/// is sound as long as `lib` outlives the returned [`SolverApi`].
pub(crate) fn load_api(lib: &Library) -> Result<SolverApi, String> {
    // SAFETY: each symbol is looked up by its documented Z3 C name and used
    // strictly at the matching signature declared above.
    unsafe {
        let get_fn = |name: &[u8]| -> Result<*const c_void, String> {
            lib.get::<*const c_void>(name)
                .map(|s| *s)
                .map_err(|e| format!("missing symbol {}: {e}", String::from_utf8_lossy(name)))
        };
        let mk_config = get_fn(b"Z3_mk_config\0")?;
        let mk_context = get_fn(b"Z3_mk_context\0")?;
        let del_config = get_fn(b"Z3_del_config\0")?;
        let del_context = get_fn(b"Z3_del_context\0")?;
        let eval = get_fn(b"Z3_eval_smtlib2_string\0")?;
        Ok(SolverApi {
            mk_config: std::mem::transmute::<*const c_void, MkConfigFn>(mk_config),
            mk_context: std::mem::transmute::<*const c_void, MkContextFn>(mk_context),
            del_config: std::mem::transmute::<*const c_void, DelConfigFn>(del_config),
            del_context: std::mem::transmute::<*const c_void, DelContextFn>(del_context),
            eval: std::mem::transmute::<*const c_void, EvalFn>(eval),
        })
    }
}

/// `Z3_string Z3_get_full_version(void)` — optional, used to stamp the bench
/// certificate with each library's self-reported version string.
type FullVersionFn = unsafe extern "C" fn() -> *const c_char;

/// Best-effort `Z3_get_full_version()` for an open library. `None` when the
/// symbol is absent or returns NULL; version strings are metadata only and
/// never affect verdicts.
pub(crate) fn full_version(lib: &Library) -> Option<String> {
    // SAFETY: resolved by its documented Z3 C name and called at the matching
    // zero-argument signature; the returned string is static in libz3 and
    // copied out immediately.
    unsafe {
        let sym = lib.get::<FullVersionFn>(b"Z3_get_full_version\0").ok()?;
        let ptr = sym();
        if ptr.is_null() {
            return None;
        }
        Some(std::ffi::CStr::from_ptr(ptr).to_string_lossy().into_owned())
    }
}

/// Test whether `name` is `dlsym`-able in an open library. Success = present.
/// This is the outsider's proof of symbol presence: no trust in any embedded
/// list, just a live `dlsym`.
pub(crate) fn has_symbol(lib: &Library, name: &str) -> bool {
    let mut bytes = name.as_bytes().to_vec();
    bytes.push(0);
    // SAFETY: we only test resolvability; the resolved address is never called.
    unsafe { lib.get::<*const c_void>(&bytes).is_ok() }
}

/// Shell out to `nm -gU <path>` and return every exported `Z3_*` symbol with
/// its platform underscore prefix stripped. Re-derivable by anyone with `nm`.
pub(crate) fn nm_z3_symbols(path: &Path) -> Result<BTreeSet<String>, String> {
    let out = Command::new("nm")
        .arg("-gU")
        .arg(path)
        .output()
        .map_err(|e| format!("failed to run `nm -gU {}`: {e}", path.display()))?;
    if !out.status.success() {
        return Err(format!(
            "`nm -gU {}` failed ({}): {}",
            path.display(),
            out.status,
            String::from_utf8_lossy(&out.stderr).trim()
        ));
    }
    Ok(extract_z3_symbols(&String::from_utf8_lossy(&out.stdout)))
}

/// Extract `Z3_*` symbol names from raw `nm` output.
///
/// Handles both Mach-O (`_Z3_foo`, single leading underscore) and ELF
/// (`Z3_foo`, no underscore) conventions by stripping at most one leading `_`.
pub(crate) fn extract_z3_symbols(nm_output: &str) -> BTreeSet<String> {
    let mut set = BTreeSet::new();
    for line in nm_output.lines() {
        for tok in line.split_whitespace() {
            let name = tok.strip_prefix('_').unwrap_or(tok);
            if name.len() > 3
                && name.starts_with("Z3_")
                && name[3..]
                    .bytes()
                    .all(|b| b.is_ascii_alphanumeric() || b == b'_')
            {
                set.insert(name.to_string());
            }
        }
    }
    set
}

#[cfg(test)]
mod tests {
    use super::extract_z3_symbols;

    #[test]
    fn parses_macho_and_elf_lines() {
        let macho = "0000000000995d9c T _Z3_mk_config\n0000000000998a34 T _Z3_del_context\n";
        let elf = "0000000000012340 T Z3_mk_config\n0000000000012350 T Z3_del_context\n";
        let a = extract_z3_symbols(macho);
        let b = extract_z3_symbols(elf);
        assert!(a.contains("Z3_mk_config"));
        assert!(a.contains("Z3_del_context"));
        assert_eq!(a, b, "underscore stripping should normalize both platforms");
    }

    #[test]
    fn ignores_non_z3_and_address_columns() {
        let out = "0000000000000001 t _some_local\n0000000000000002 T _malloc\n0000000000000003 T _Z3_ast_to_string\n";
        let s = extract_z3_symbols(out);
        assert_eq!(s.len(), 1);
        assert!(s.contains("Z3_ast_to_string"));
    }
}
