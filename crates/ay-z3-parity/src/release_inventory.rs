// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Source/discovery inventory only; never an ABI or semantic completion claim.
#[cfg(unix)]
use ay_sys::child_pipe::ChildPipeWriter;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::ffi::OsString;
use std::fs::{self, File};
use std::io::{Read, Write};
#[cfg(unix)]
use std::os::unix::process::CommandExt;
use std::path::Path;
#[cfg(unix)]
use std::process::{Child, Command, Stdio};
use std::time::Duration;
#[cfg(unix)]
use std::time::Instant;

type Result<T> = std::result::Result<T, String>;
type Map = BTreeMap<String, Value>;
const OUTPUT_LIMIT: u64 = 64 * 1024 * 1024;
const SOURCE_LIMIT: u64 = 64 * 1024 * 1024;

pub(crate) fn run(args: &[String]) -> i32 {
    match execute(args) {
        Ok(()) => 0,
        Err(error) => {
            eprintln!("release-inventory: {error}");
            2
        }
    }
}

fn execute(args: &[String]) -> Result<()> {
    let mut flags = BTreeMap::new();
    if args.len() % 2 != 0 {
        return Err("requires --repo-root PATH --release PATH --output PATH".into());
    }
    for pair in args.chunks_exact(2) {
        if !["--repo-root", "--release", "--output"].contains(&pair[0].as_str())
            || flags.insert(pair[0].as_str(), pair[1].as_str()).is_some()
        {
            return Err("unknown or duplicate inventory option".into());
        }
    }
    let required = |name| {
        flags
            .get(name)
            .copied()
            .ok_or_else(|| format!("missing {name}"))
    };
    let root = Path::new(required("--repo-root")?)
        .canonicalize()
        .map_err(err)?;
    let release = Path::new(required("--release")?)
        .canonicalize()
        .map_err(err)?;
    let report = audit(&root, &release)?;
    let mut bytes = serde_json::to_vec_pretty(&report).map_err(err)?;
    bytes.push(b'\n');
    fs::write(required("--output")?, bytes).map_err(err)?;
    let mut summaries = ["declarations", "enums", "module_parameter_names"]
        .into_iter()
        .map(|name| (name, &report[name]))
        .collect::<Vec<_>>();
    if let Some(catalogs) = report["catalogs"].as_object() {
        summaries.extend(catalogs.iter().map(|(name, row)| (name.as_str(), row)));
    }
    for (name, row) in summaries {
        println!(
            "{name}: AY {}, upstream {}; missing {}, changed {}, extra {}",
            row["ay_count"],
            row["upstream_count"],
            row["missing"].as_object().map_or(0, |v| v.len()),
            row["changed"].as_object().map_or(0, |v| v.len()),
            row["extra"].as_object().map_or(0, |v| v.len())
        );
    }
    Ok(())
}
fn err(error: impl std::fmt::Display) -> String {
    error.to_string()
}
fn bounded_read(path: &Path, limit: u64) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    File::open(path)
        .map_err(err)?
        .take(limit + 1)
        .read_to_end(&mut bytes)
        .map_err(err)?;
    if bytes.len() as u64 > limit {
        return Err(format!("input exceeds bound: {}", path.display()));
    }
    Ok(bytes)
}
fn text(path: &Path) -> Result<String> {
    String::from_utf8(bounded_read(path, SOURCE_LIMIT)?).map_err(err)
}
fn digest(path: &Path) -> Result<String> {
    let mut file = File::open(path).map_err(err)?;
    let mut h = Sha256::new();
    let mut block = [0; 65536];
    loop {
        let n = file.read(&mut block).map_err(err)?;
        if n == 0 {
            break;
        }
        h.update(&block[..n]);
    }
    Ok(format!("{:x}", h.finalize()))
}

#[cfg(unix)]
struct Process {
    // Taking the handle consumes all authority to signal the numeric group.
    // No code may reap the leader while this option remains populated.
    child: Option<Child>,
}
#[cfg(unix)]
impl Process {
    fn child_mut(&mut self) -> std::io::Result<&mut Child> {
        self.child
            .as_mut()
            .ok_or_else(|| std::io::Error::other("inventory child already consumed"))
    }

    fn exited_unreaped(&self) -> std::io::Result<bool> {
        let child = self
            .child
            .as_ref()
            .ok_or_else(|| std::io::Error::other("inventory child already consumed"))?;
        #[cfg(target_os = "macos")]
        {
            use ay_sys::supervisor::{observe_child_unreaped, UnreapedChildState};
            return Ok(matches!(
                observe_child_unreaped(child, false)?,
                UnreapedChildState::Exited
            ));
        }
        #[cfg(target_os = "linux")]
        {
            loop {
                // SAFETY: initialized POD output, owned positive child PID,
                // documented wait flags. WNOWAIT leaves its PID reserved.
                let (result, info) = unsafe {
                    let mut info: libc::siginfo_t = std::mem::zeroed();
                    let result = libc::waitid(
                        libc::P_PID,
                        child.id(),
                        &mut info,
                        libc::WEXITED | libc::WNOHANG | libc::WNOWAIT,
                    );
                    (result, info)
                };
                if result != 0 {
                    let error = std::io::Error::last_os_error();
                    if error.kind() == std::io::ErrorKind::Interrupted {
                        continue;
                    }
                    return Err(error);
                }
                // SAFETY: successful waitid initialized this siginfo's child
                // status fields, including zero si_pid when no event exists.
                let observed_pid = unsafe { info.si_pid() };
                if observed_pid == 0 {
                    return Ok(false);
                }
                if observed_pid != child.id() as libc::pid_t {
                    return Err(std::io::Error::other("waitid returned unrelated child"));
                }
                return match info.si_code {
                    libc::CLD_EXITED | libc::CLD_KILLED | libc::CLD_DUMPED => Ok(true),
                    _ => Err(std::io::Error::other("unexpected inventory waitid state")),
                };
            }
        }
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        {
            let _ = child;
            Err(std::io::Error::other(
                "non-reaping inventory child observation unavailable",
            ))
        }
    }

    fn terminate_and_reap(&mut self) -> std::io::Result<std::process::ExitStatus> {
        // An unknown state is never quiescence. Observation errors still lead
        // to an attempted group signal while our unreaped leader pins its ID.
        let leader_exited = matches!(self.exited_unreaped(), Ok(true));
        let group_observation = if leader_exited {
            self.child
                .as_ref()
                .map_or(Ok(false), |child| prove_group_quiescent(child.id()))
        } else {
            Ok(false)
        };
        let group_quiescent = matches!(group_observation, Ok(true));
        // Consume authority BEFORE signalling or reaping, including on errors.
        // Drop therefore cannot signal a reused numeric PGID after wait().
        let mut child = self
            .child
            .take()
            .ok_or_else(|| std::io::Error::other("inventory child already consumed"))?;
        if !group_quiescent {
            // SAFETY: this owned process-group leader has never been reaped.
            // Its PID/PGID remains reserved even after WNOWAIT observes exit.
            let result = unsafe { libc::kill(-(child.id() as i32), libc::SIGKILL) };
            if result < 0 {
                let error = std::io::Error::last_os_error();
                // Reap only a positively exited leader: waiting for a running
                // child after signal denial could hang. Never replace denial
                // with a direct-PID permission fallback or an errno-based
                // assertion that the group is absent. Authority stays consumed.
                if leader_exited {
                    let _ = child.wait();
                }
                return Err(std::io::Error::new(
                    error.kind(),
                    format!("owned-group signal failed: {error}; leader exited={leader_exited}; census={group_observation:?}"),
                ));
            }
        }
        child.wait()
    }
}
#[cfg(any(target_os = "macos", all(test, target_os = "linux")))]
fn samples_prove_quiescence(
    first: &ay_sys::supervisor::process_group::ProcessGroupSample,
    second: &ay_sys::supervisor::process_group::ProcessGroupSample,
) -> bool {
    if !first.live_members.is_empty() || !second.live_members.is_empty() {
        return false;
    }
    let exact_identity = |identity: &ay_sys::supervisor::process_group::ProcessIdentity| {
        (
            identity.pid,
            identity.parent,
            identity.group,
            identity.birth,
        )
    };
    let observed_dead = first
        .members
        .iter()
        .map(exact_identity)
        .collect::<std::collections::BTreeSet<_>>();
    second
        .members
        .iter()
        .all(|identity| observed_dead.contains(&exact_identity(identity)))
}

#[cfg(target_os = "macos")]
fn prove_group_quiescent(group: u32) -> std::io::Result<bool> {
    use ay_sys::supervisor::process_group::process_group_sample;
    let first = process_group_sample(group)?;
    if !first.live_members.is_empty() {
        return Ok(false);
    }
    // A fresh complete enumeration closes the first walk's fork/exit race:
    // second-sample identities must all have been observed dead in the first.
    // Successful complete empty samples can establish kernel absence; syscall
    // failures (including ESRCH/EPERM) cannot substitute for either sample.
    let second = process_group_sample(group)?;
    Ok(samples_prove_quiescence(&first, &second))
}

#[cfg(all(unix, not(target_os = "macos")))]
fn prove_group_quiescent(_: u32) -> std::io::Result<bool> {
    Err(std::io::Error::other(
        "native process-group census unavailable",
    ))
}

#[cfg(unix)]
impl Drop for Process {
    fn drop(&mut self) {
        if self.child.is_some() {
            let _ = self.terminate_and_reap();
        }
    }
}
#[cfg(unix)]
fn query(
    program: &Path,
    args: &[OsString],
    input: &[u8],
    timeout: Duration,
    limit: u64,
) -> Result<String> {
    if input.len() > 4096 {
        return Err("inventory stdin exceeds bound".into());
    }
    let stdout = tempfile::NamedTempFile::new().map_err(err)?;
    let stderr = tempfile::NamedTempFile::new().map_err(err)?;
    let mut command = Command::new(program);
    command
        .args(args)
        .stdin(Stdio::piped())
        .stdout(stdout.reopen().map_err(err)?)
        .stderr(stderr.reopen().map_err(err)?)
        .process_group(0);
    // SAFETY: pre_exec performs only async-signal-safe setrlimit, with a
    // stack-local limit; no allocation or locks occur in the child callback.
    unsafe {
        command.pre_exec(|| {
            let bound = libc::rlimit {
                rlim_cur: OUTPUT_LIMIT,
                rlim_max: OUTPUT_LIMIT,
            };
            if libc::setrlimit(libc::RLIMIT_FSIZE, &bound) != 0 {
                return Err(std::io::Error::last_os_error());
            }
            Ok(())
        });
    }
    let mut process = Process {
        child: Some(command.spawn().map_err(err)?),
    };
    let mut writer = ChildPipeWriter::take_from(process.child_mut().map_err(err)?).map_err(err)?;
    // At most 4096 bytes: fits an empty pipe, even if the child never reads.
    writer.write_all(input).map_err(err)?;
    drop(writer);
    let started = Instant::now();
    loop {
        if stdout.as_file().metadata().map_err(err)?.len() > limit
            || stderr.as_file().metadata().map_err(err)?.len() > 1024 * 1024
        {
            return Err(format!("{} exceeded output bound", program.display()));
        }
        if process.exited_unreaped().map_err(err)? {
            break;
        }
        if started.elapsed() >= timeout {
            return Err(format!("{} exceeded deadline", program.display()));
        }
        std::thread::sleep(Duration::from_millis(10));
    }
    // Establish owned-group quiescence or signal while the exited leader still
    // reserves the group ID, then reap. This does not track escaped descendants.
    // Drop holds no signalling authority after cleanup consumes the handle.
    let status = process.terminate_and_reap().map_err(err)?;
    let diagnostic = bounded_read(stderr.path(), 1024 * 1024)?;
    if !status.success() || !diagnostic.is_empty() {
        return Err(format!(
            "{} refused: {status}; {}",
            program.display(),
            String::from_utf8_lossy(&diagnostic)
        ));
    }
    String::from_utf8(bounded_read(stdout.path(), limit)?).map_err(err)
}
#[cfg(not(unix))]
fn query(_: &Path, _: &[OsString], _: &[u8], _: Duration, _: u64) -> Result<String> {
    Err("release inventory requires native POSIX process-group and file-size enforcement".into())
}

fn cli(binary: &Path, args: &[&str]) -> Result<String> {
    query(
        binary,
        &args.iter().map(OsString::from).collect::<Vec<_>>(),
        b"",
        Duration::from_secs(15),
        1024 * 1024,
    )
}

fn constant(node: &Value) -> Result<Option<i64>> {
    if node["kind"] == "ConstantExpr" {
        return node["value"]
            .as_str()
            .ok_or("constant lacks numeric value")?
            .parse()
            .map(Some)
            .map_err(err);
    }
    if let Some(children) = node.get("inner") {
        for child in children.as_array().ok_or("malformed AST children")? {
            if let Some(value) = constant(child)? {
                return Ok(Some(value));
            }
        }
    }
    Ok(None)
}
fn ast_inventory(ast: &Value) -> Result<(Map, Map)> {
    fn insert(map: &mut Map, name: &str, value: Value) -> Result<()> {
        if let Some(old) = map.insert(name.into(), value.clone()) {
            if old != value {
                return Err(format!("conflicting declaration: {name}"));
            }
        }
        Ok(())
    }
    fn visit(node: &Value, functions: &mut Map, enums: &mut Map) -> Result<()> {
        let kind = node["kind"].as_str().ok_or("AST node lacks kind")?;
        if kind == "FunctionDecl" {
            if let Some(name) = node["name"].as_str().filter(|s| s.starts_with("Z3_")) {
                let signature = node["type"]["qualType"]
                    .as_str()
                    .filter(|s| !s.is_empty())
                    .ok_or("function lacks Clang signature")?;
                insert(functions, name, json!(signature))?;
            }
        }
        if kind == "EnumDecl" {
            let mut next = Some(0i64);
            for child in node["inner"].as_array().map(Vec::as_slice).unwrap_or(&[]) {
                if child["kind"] != "EnumConstantDecl" {
                    continue;
                }
                let value = match constant(child)? {
                    Some(value) => value,
                    None if child
                        .get("inner")
                        .is_none_or(|v| v.as_array().is_some_and(Vec::is_empty)) =>
                    {
                        next.ok_or("enum progression overflow")?
                    }
                    None => {
                        return Err("enum initializer has no evaluated Clang ConstantExpr".into())
                    }
                };
                next = value.checked_add(1);
                let name = child["name"].as_str().ok_or("enum constant lacks name")?;
                if name.starts_with("Z3_") {
                    insert(enums, name, json!(value))?;
                }
            }
        }
        if let Some(children) = node.get("inner") {
            for child in children.as_array().ok_or("malformed AST children")? {
                visit(child, functions, enums)?;
            }
        }
        Ok(())
    }
    let mut functions = Map::new();
    let mut enums = Map::new();
    if ast["kind"] != "TranslationUnitDecl" {
        return Err("expected Clang translation unit".into());
    }
    visit(ast, &mut functions, &mut enums)?;
    if functions.is_empty() || enums.is_empty() {
        return Err("empty Clang Z3 inventory".into());
    }
    Ok((functions, enums))
}
pub(crate) fn clang_inventory(include: &Path) -> Result<(Map, Map)> {
    let args = [
        OsString::from("-x"),
        "c".into(),
        "-std=c11".into(),
        "-I".into(),
        include.as_os_str().into(),
        "-Xclang".into(),
        "-ast-dump=json".into(),
        "-fsyntax-only".into(),
        "-".into(),
    ];
    let output = query(
        Path::new("clang"),
        &args,
        b"#include \"z3.h\"\n",
        Duration::from_secs(30),
        OUTPUT_LIMIT,
    )?;
    let ast: Value = serde_json::from_str(&output).map_err(err)?;
    let (functions, mut enums) = ast_inventory(&ast)?;
    // Compatibility headers may expose new enum members as typed object
    // macros without changing the original enum. Ask Clang to evaluate those
    // constants too; parsing replacement text as numbers would miss casts and
    // arithmetic, and would silently count incorrect values as compatible.
    fn enum_types(node: &Value, names: &mut std::collections::BTreeSet<String>) {
        if node["kind"] == "TypedefDecl"
            && node["type"]["qualType"]
                .as_str()
                .is_some_and(|name| name.starts_with("enum "))
        {
            if let Some(name) = node["name"].as_str() {
                names.insert(name.into());
            }
        }
        if let Some(children) = node["inner"].as_array() {
            for child in children {
                enum_types(child, names);
            }
        }
    }
    let mut types = std::collections::BTreeSet::new();
    enum_types(&ast, &mut types);
    let definitions = query(
        Path::new("clang"),
        &[
            "-x".into(),
            "c".into(),
            "-std=c11".into(),
            "-I".into(),
            include.as_os_str().into(),
            "-dM".into(),
            "-E".into(),
            "-".into(),
        ],
        b"#include \"z3.h\"\n",
        Duration::from_secs(30),
        OUTPUT_LIMIT,
    )?;
    let mut aliases = Vec::new();
    for line in definitions.lines() {
        let Some(definition) = line.strip_prefix("#define ") else {
            continue;
        };
        let Some((name, replacement)) = definition.split_once(char::is_whitespace) else {
            continue;
        };
        if !name.starts_with("Z3_") || name.contains('(') {
            continue;
        }
        let mut cast = replacement.trim_start();
        let mut parentheses = 0;
        while let Some(rest) = cast.strip_prefix('(') {
            parentheses += 1;
            cast = rest.trim_start();
        }
        let Some((cast, _)) = cast.split_once(')') else {
            continue;
        };
        if parentheses > 0 && types.contains(cast.trim()) {
            aliases.push(name);
        }
    }
    if !aliases.is_empty() {
        let mut source = String::from("#include \"z3.h\"\nenum {\n");
        for (index, name) in aliases.iter().enumerate() {
            source.push_str(&format!("Z3_AY_INVENTORY_ALIAS_{index} = {name},\n"));
        }
        source.push_str("};\n");
        let evaluated = query(
            Path::new("clang"),
            &args,
            source.as_bytes(),
            Duration::from_secs(30),
            OUTPUT_LIMIT,
        )?;
        let (_, values) = ast_inventory(&serde_json::from_str(&evaluated).map_err(err)?)?;
        for (index, name) in aliases.iter().enumerate() {
            let value = values
                .get(&format!("Z3_AY_INVENTORY_ALIAS_{index}"))
                .ok_or("Clang omitted typed enum macro")?;
            if let Some(previous) = enums.insert((*name).into(), value.clone()) {
                if previous != *value {
                    return Err(format!("conflicting enum macro: {name}"));
                }
            }
        }
    }
    Ok((functions, enums))
}
fn delta(ay: &Map, upstream: &Map) -> Value {
    let missing: Map = upstream
        .iter()
        .filter(|(k, _)| !ay.contains_key(*k))
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    let extra: Map = ay
        .iter()
        .filter(|(k, _)| !upstream.contains_key(*k))
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    let changed: Map = ay
        .iter()
        .filter_map(|(k, v)| {
            upstream
                .get(k)
                .filter(|u| *u != v)
                .map(|u| (k.clone(), json!({"ay":v,"upstream":u})))
        })
        .collect();
    json!({"ay_count":ay.len(),"upstream_count":upstream.len(),"missing":missing,"extra":extra,"changed":changed})
}

// Parse only the generated constant's Rust array grammar. String values use
// JSON-compatible escapes; reject malformed/duplicate/empty entries, not guess.
struct Table<'a> {
    rest: &'a str,
}
impl<'a> Table<'a> {
    fn new(source: &'a str, name: &str) -> Result<Self> {
        let marker = format!("const {name}:");
        let rest = source
            .split_once(&marker)
            .ok_or_else(|| format!("missing table {name}"))?
            .1;
        let rest = rest.split_once("= &[").ok_or("missing table array")?.1;
        Ok(Self { rest })
    }
    fn ws(&mut self) {
        loop {
            self.rest = self.rest.trim_start();
            if self.rest.starts_with("//") {
                self.rest = self.rest.split_once('\n').map_or("", |(_, s)| s);
            } else {
                break;
            }
        }
    }
    fn eat(&mut self, token: &str) -> bool {
        self.ws();
        if let Some(rest) = self.rest.strip_prefix(token) {
            self.rest = rest;
            true
        } else {
            false
        }
    }
    fn require(&mut self, token: &str) -> Result<()> {
        if self.eat(token) {
            Ok(())
        } else {
            Err(format!("expected table token {token}"))
        }
    }
    fn string(&mut self) -> Result<String> {
        self.ws();
        let mut stream = serde_json::Deserializer::from_str(self.rest).into_iter::<String>();
        let value = stream.next().ok_or("missing table string")?.map_err(err)?;
        self.rest = &self.rest[stream.byte_offset()..];
        Ok(value)
    }
    fn finish(&mut self) -> Result<()> {
        self.require(";")
    }
}
enum CatalogKind {
    Pairs,
    Names,
}

fn catalog(source: &str, name: &str, kind: CatalogKind) -> Result<Map> {
    let pairs = matches!(kind, CatalogKind::Pairs);
    let mut table = Table::new(source, name)?;
    let mut map = Map::new();
    while !table.eat("]") {
        if pairs {
            table.require("(")?;
        }
        let key = table.string()?;
        let value = if pairs {
            table.require(",")?;
            let value = table.string()?;
            table.eat(",");
            table.require(")")?;
            value
        } else {
            "accepted-name".into()
        };
        if map.insert(key, json!(value)).is_some() {
            return Err("duplicate catalog entry".into());
        }
        if !table.eat(",") {
            table.require("]")?;
            break;
        }
    }
    table.finish()?;
    if map.is_empty() {
        return Err("empty AY catalog".into());
    }
    Ok(map)
}
pub(crate) fn observed_catalog(output: &str) -> Result<Map> {
    let mut map = Map::new();
    for line in output.lines().filter_map(|s| s.strip_prefix("- ")) {
        let (name, description) = line
            .split_once(' ')
            .ok_or("malformed release catalog entry")?;
        if name.is_empty() || map.insert(name.into(), json!(description)).is_some() {
            return Err("duplicate or empty release catalog entry".into());
        }
    }
    if map.is_empty() {
        return Err("empty release catalog".into());
    }
    Ok(map)
}
fn module_parameters(output: &str) -> Result<Map> {
    let mut module = None;
    let mut map = Map::new();
    for line in output.lines() {
        if let Some(rest) = line.strip_prefix("[module] ") {
            let name = rest
                .split(|c: char| c == ',' || c.is_whitespace())
                .next()
                .filter(|s| !s.is_empty())
                .ok_or("missing module name")?;
            module = Some(name);
        } else if let (Some(module), Some(rest)) = (module, line.strip_prefix("    ")) {
            let (name, tail) = rest.split_once(" (").ok_or("malformed module parameter")?;
            let (kind, suffix) = tail.split_once(')').ok_or("unclosed parameter type")?;
            if name.is_empty()
                || name.chars().any(char::is_whitespace)
                || kind.is_empty()
                || kind.contains('(')
                || (!suffix.is_empty()
                    && !(suffix.starts_with(" (default: ") && suffix.ends_with(')')))
            {
                return Err("malformed module parameter/default".into());
            }
            if map
                .insert(format!("{module}.{name}"), json!("accepted-name"))
                .is_some()
            {
                return Err("duplicate module parameter".into());
            }
        }
    }
    if map.is_empty() {
        return Err("empty reference module parameters".into());
    }
    Ok(map)
}
fn headers(directory: &Path) -> Result<Map> {
    // Include AY's compatibility wrapper, not merely names starting with z3.
    // Relative paths preserve identities when nested headers share a basename.
    let mut result = Map::new();
    let mut pending = vec![directory.to_owned()];
    let mut entries = 0usize;
    while let Some(current) = pending.pop() {
        for entry in fs::read_dir(current).map_err(err)? {
            entries += 1;
            if entries > 10_000 {
                return Err("header traversal exceeds bound".into());
            }
            let entry = entry.map_err(err)?;
            let kind = entry.file_type().map_err(err)?;
            let path = entry.path();
            if kind.is_symlink() {
                return Err("symlink in header input directory".into());
            }
            if kind.is_dir() {
                pending.push(path);
            } else if path.extension().is_some_and(|s| s == "h") {
                if !kind.is_file() {
                    return Err("nonregular header input".into());
                }
                let name = path
                    .strip_prefix(directory)
                    .map_err(err)?
                    .to_str()
                    .ok_or("non UTF-8 header path")?
                    .to_owned();
                result.insert(name, json!(digest(&path)?));
            }
        }
    }
    if result.is_empty() {
        return Err("empty header input set".into());
    }
    Ok(result)
}

fn audit(root: &Path, release: &Path) -> Result<Value> {
    let include = root.join("crates/ay-ffi/include");
    let upstream_include = release.join("include");
    let catalog_path = root.join("crates/ay/src/z3_catalog.rs");
    let parameter_path = root.join("crates/ay/src/z3_params.rs");
    let binary = release.join("bin/z3");
    let (ay_functions, ay_enums) = clang_inventory(&include)?;
    let (up_functions, up_enums) = clang_inventory(&upstream_include)?;
    let source = text(&catalog_path)?;
    let mut catalogs = Map::new();
    let mut outputs = Map::new();
    for (name, flag) in [
        ("TACTICS", "-tactics"),
        ("PROBES", "-probes"),
        ("SIMPLIFIERS", "-simplifiers"),
    ] {
        let output = cli(&binary, &[flag, "-in"])?;
        catalogs.insert(
            name.to_ascii_lowercase(),
            delta(
                &catalog(&source, name, CatalogKind::Pairs)?,
                &observed_catalog(&output)?,
            ),
        );
        outputs.insert(name.to_ascii_lowercase(), json!(output));
    }
    let params = cli(&binary, &["-p"])?;
    let commit = cli(
        Path::new("git"),
        &[
            "-C",
            root.to_str().ok_or("non UTF-8 repository root")?,
            "rev-parse",
            "HEAD",
        ],
    )?;
    let clang = cli(Path::new("clang"), &["--version"])?;
    Ok(json!({
        "schema":"ay-z3-release-inventory/v1",
        "scope":"header functions, enum values, CLI catalog names and descriptions; source/discovery only, no ABI or runtime semantic completion claim",
        "ay_commit":commit.trim(), "clang":clang.lines().next().ok_or("empty Clang identity")?,
        "reference_banner":cli(&binary, &["-version"])?.trim(), "reference_binary_sha256":digest(&binary)?,
        "header_hash_scope":"all local .h files recursively; declarations come from Clang z3.h include graphs",
        "headers":{"ay":headers(&include)?,"upstream":headers(&upstream_include)?},
        "ay_catalog_sha256":digest(&catalog_path)?,"ay_parameter_names_sha256":digest(&parameter_path)?,
        "declarations":delta(&ay_functions,&up_functions),"enums":delta(&ay_enums,&up_enums),
        "catalogs":catalogs,"module_parameter_names":delta(&catalog(&text(&parameter_path)?,"Z3_MODULE_PARAMS",CatalogKind::Names)?,&module_parameters(&params)?),
        "reference_parameter_output":params,"reference_catalog_outputs":outputs
    }))
}

#[cfg(test)]
mod tests;
