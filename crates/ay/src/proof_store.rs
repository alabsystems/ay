// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Where ay's proofs go, and what each proof says it is.
//!
//! A proof ay writes lands in one of two places:
//!
//! - **Beside its input** (the default, for people): `<input>.drat`,
//!   `<input>.alethe` or `<input>.chccert`. [`SIDECAR_PAIRS`] names every pair,
//!   and [`TRANSACTION_LEFTOVERS`] every name a run can leave there when it is
//!   killed mid-write; `ay proof sidecars` prints both, so a disk cleaner reads
//!   them from ay instead of keeping its own copy.
//! - **In a proof store** (`--proof-store DIR`, for ay's own runners):
//!   `<store>/<input sha256>-<ay build>/<input>.<proof>`. The store is tagged
//!   with `CACHEDIR.TAG`, and every transaction file of a run lives inside its
//!   slot, so a run killed at any point leaves nothing beside the corpus.
//!
//! Wherever it lands, a proof carries a label (the extended attribute
//! [`LABEL_ATTRIBUTE`]) written on its own descriptor when the file is
//! created: the maker, its class, the session, the input's name and sha256,
//! ay's build, the device and inode the label was written on, and the command
//! that makes the proof again. Publication adds the proof's own sha256. A label
//! whose device and inode do not match the file it sits on was copied with the
//! file, and explains it without vouching for it. A checker such as Carcara or
//! drat-trim reads the file's bytes and never sees the label.
//!
//! A proof already in a store slot counts for a later run only after it is
//! checked again ([`ProofSlot::check_stored`]): its label must name this
//! input's sha256 and this build, sit on the file's own inode, and record the
//! sha256 its bytes still hash to. A proof that counts is this input's proof
//! from this build, and the later run writes no second copy of it.

use std::fmt;
use std::fs::{self, File};
use std::io::{self, Read as _, Write as _};
use std::path::{Path, PathBuf};

use sha2::{Digest as _, Sha256};

/// The extended attribute every proof's label is written to.
///
/// macOS attribute names have no namespace; Linux requires the `user.` one
/// for an unprivileged writer.
#[cfg(not(target_os = "linux"))]
pub const LABEL_ATTRIBUTE: &str = "com.alab.made";
/// The extended attribute every proof's label is written to.
#[cfg(target_os = "linux")]
pub const LABEL_ATTRIBUTE: &str = "user.com.alab.made";

/// The first line of every label ay writes.
pub const LABEL_SCHEMA: &str = "ay-proof-label-v1";

/// The name of the tag that marks a proof store as a cache.
pub const STORE_TAG_NAME: &str = "CACHEDIR.TAG";

/// The signature line the cache-directory-tag convention requires
/// (<https://bford.info/cachedir/>).
pub const CACHEDIR_TAG_SIGNATURE: &str = "Signature: 8a477f597d28d172789f06886806bc55";

/// One input/proof extension pair: ay writes a default proof for an input
/// named `<B>` with `input_extension` at `<B>.<proof_extension>` beside it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SidecarPair {
    /// The input's extension, matched case-insensitively.
    pub input_extension: &'static str,
    /// The extension appended to the input's whole name.
    pub proof_extension: &'static str,
    /// The proof format written under that name.
    pub format: &'static str,
}

/// Every default proof ay writes beside an input. CHC problems are SMT-LIB
/// files; ay learns that a problem is Horn only after reading it, and then
/// writes `.chccert` instead of `.alethe`.
pub const SIDECAR_PAIRS: &[SidecarPair] = &[
    SidecarPair {
        input_extension: "cnf",
        proof_extension: "drat",
        format: "DRAT",
    },
    SidecarPair {
        input_extension: "dimacs",
        proof_extension: "drat",
        format: "DRAT",
    },
    SidecarPair {
        input_extension: "smt2",
        proof_extension: "alethe",
        format: "Alethe",
    },
    SidecarPair {
        input_extension: "smt2",
        proof_extension: "chccert",
        format: "ay-chc-cert",
    },
    SidecarPair {
        input_extension: "smt",
        proof_extension: "alethe",
        format: "Alethe",
    },
    SidecarPair {
        input_extension: "smt",
        proof_extension: "chccert",
        format: "ay-chc-cert",
    },
];

/// One name ay writes beside a proof `<P>` (itself `<B>.<proof extension>`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProofName {
    /// The name, with `{P}` for the proof's file name, `{pid}` for the
    /// writing process and `{n}` for a per-process nonce.
    pub pattern: &'static str,
    /// `file` or `dir`.
    pub kind: &'static str,
    /// What writes it.
    pub what: &'static str,
}

/// Every name a published proof keeps beside it for as long as it stands.
/// A companion is part of its proof, not a sign of a killed run.
pub const COMPANIONS: &[ProofName] = &[
    ProofName {
        pattern: "{P}.ay-status",
        kind: "file",
        what: "status marker of a default DRAT proof, naming its sha256; labelled as its proof is",
    },
    ProofName {
        pattern: ".{P}.ay-chc.lock",
        kind: "file",
        what: "CHC certificate publication lock, kept for the next publication; labelled as its proof is",
    },
    ProofName {
        pattern: "{P}.chc-obligations-{pid}-{n}",
        kind: "dir",
        what: "CHC replay obligations the certificate names; each file labelled as its proof is",
    },
];

/// Every transaction name ay's proof writers use beside a proof, which a run
/// killed mid-write leaves behind.
pub const TRANSACTION_LEFTOVERS: &[ProofName] = &[
    ProofName {
        pattern: ".{P}.tmp-{pid}-{n}",
        kind: "file",
        what: "Alethe proof or CHC certificate being written",
    },
    ProofName {
        pattern: ".ay-dimacs-proof-{pid}-{n}.stage",
        kind: "file",
        what: "DRAT proof being written",
    },
    ProofName {
        pattern: ".ay-dimacs-proof-{pid}-{n}",
        kind: "dir",
        what: "DRAT proof staging folder",
    },
    ProofName {
        pattern: "{P}.ay-status.lock",
        kind: "file",
        what: "status marker being written; locked while its run lives",
    },
    ProofName {
        pattern: ".{P}.rejected-{pid}-{n}",
        kind: "file",
        what: "a stored proof that failed its check again (proof store only)",
    },
    ProofName {
        pattern: ".{P}.rejected-{pid}-{n}.ay-status",
        kind: "file",
        what: "the status marker of a stored proof set aside (proof store only)",
    },
    ProofName {
        pattern: ".{P}.ay-status.rejected-{pid}-{n}",
        kind: "file",
        what: "a status marker whose run is gone and whose proof is not stored (proof store only)",
    },
    ProofName {
        pattern: ".{P}.ay-status.lock.rejected-{pid}-{n}",
        kind: "file",
        what: "a status transaction lock whose run is gone (proof store only)",
    },
];

/// The status marker a default DRAT proof `<P>` carries beside it, which
/// names that proof's sha256 and moves aside with it.
const STATUS_MARKER_SUFFIX: &str = ".ay-status";

/// The suffix of the status marker's transaction lock.
const STATUS_LOCK_SUFFIX: &str = ".lock";

/// The status a marker carries while it names its proof as current.
const STATUS_CURRENT: &str = "status=current-same-run";

/// What `ay proof sidecars` prints: one tab-separated record per line.
///
/// ```text
/// pair       <input ext>  <proof ext>  <format>
/// companion  <pattern>    <file|dir>   <what>
/// leftover   <pattern>    <file|dir>   <what>
/// label      <attribute>  <schema>
/// store      <tag name>   <signature>
/// ```
#[must_use]
pub fn sidecars_report() -> String {
    let mut out = String::new();
    out.push_str(
        "# ay proof sidecars: what ay writes beside an input <B>; {P} is <B>.<proof ext>\n",
    );
    for pair in SIDECAR_PAIRS {
        out.push_str(&format!(
            "pair\t{}\t{}\t{}\n",
            pair.input_extension, pair.proof_extension, pair.format
        ));
    }
    for (record, names) in [
        ("companion", COMPANIONS),
        ("leftover", TRANSACTION_LEFTOVERS),
    ] {
        for name in names {
            out.push_str(&format!(
                "{record}\t{}\t{}\t{}\n",
                name.pattern, name.kind, name.what
            ));
        }
    }
    out.push_str(&format!("label\t{LABEL_ATTRIBUTE}\t{LABEL_SCHEMA}\n"));
    out.push_str(&format!(
        "store\t{STORE_TAG_NAME}\t{CACHEDIR_TAG_SIGNATURE}\n"
    ));
    out
}

/// The proof extension ay writes beside `input` by default, if any.
#[must_use]
pub fn default_proof_extension(input: &Path) -> Option<&'static str> {
    let extension = input.extension()?.to_str()?.to_ascii_lowercase();
    SIDECAR_PAIRS
        .iter()
        .find(|pair| pair.input_extension == extension)
        .map(|pair| pair.proof_extension)
}

/// Every proof extension ay can write beside `input` (`.alethe` and
/// `.chccert` for an SMT-LIB file).
#[must_use]
pub fn proof_extensions(input: &Path) -> Vec<&'static str> {
    let Some(extension) = input
        .extension()
        .and_then(|extension| extension.to_str())
        .map(str::to_ascii_lowercase)
    else {
        return Vec::new();
    };
    SIDECAR_PAIRS
        .iter()
        .filter(|pair| pair.input_extension == extension)
        .map(|pair| pair.proof_extension)
        .collect()
}

/// ay's build as a store slot names it: `<version>+<commit>`.
#[must_use]
pub fn build_identity() -> &'static str {
    concat!(env!("CARGO_PKG_VERSION"), "+", env!("AY_BUILD_COMMIT"))
}

/// ay's full build stamp, as `ay --version` prints it.
#[must_use]
pub fn build_stamp() -> &'static str {
    env!("AY_BUILD_STAMP")
}

/// Lowercase hex sha256 of the file at `path`.
///
/// # Errors
///
/// Any error opening or reading the file.
pub fn sha256_file(path: &Path) -> io::Result<String> {
    let mut file = File::open(path)?;
    sha256_reader(&mut file)
}

fn sha256_reader(reader: &mut impl io::Read) -> io::Result<String> {
    let mut hasher = Sha256::new();
    let mut buffer = vec![0u8; 1 << 20];
    loop {
        let read = reader.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    Ok(hex(&hasher.finalize()))
}

/// Lowercase hex of `bytes`.
#[must_use]
pub fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(DIGITS[usize::from(byte >> 4)] as char);
        out.push(DIGITS[usize::from(byte & 0x0f)] as char);
    }
    out
}

/// What a proof is derived from: the input file, and where the proof goes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofSubject {
    /// The input the proof refutes.
    pub input: PathBuf,
    /// The input's sha256, when it was already read (a store slot reads it to
    /// name the slot); otherwise it is read when the label is written.
    pub input_sha256: Option<String>,
    /// Where the proof goes.
    pub placement: ProofPlacement,
}

/// Where a proof is written, which decides the class its label claims and
/// what a label failure means.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofPlacement {
    /// At a name a person chose (`--proof`, `--drat`, ...): the person's
    /// file, class `personal`, which no cleaner takes. A filesystem that keeps
    /// no extended attributes leaves it unlabelled.
    Named,
    /// ay's default beside its input, for people: class `cache`, since
    /// solving the input again makes it again. A filesystem that keeps no
    /// extended attributes leaves it unlabelled, as it is unlabelled anywhere
    /// such a filesystem holds it.
    Beside,
    /// In a proof store, whose every proof is labelled `cache`: a label that
    /// cannot be written fails the proof.
    Store,
}

impl ProofPlacement {
    /// The class a label claims for a proof placed here.
    #[must_use]
    pub fn class(self) -> &'static str {
        match self {
            Self::Named => "personal",
            Self::Beside | Self::Store => "cache",
        }
    }
}

impl ProofSubject {
    /// ay's default proof of `input`, written beside it.
    #[must_use]
    pub fn beside(input: &Path) -> Self {
        Self {
            input: input.to_path_buf(),
            input_sha256: None,
            placement: ProofPlacement::Beside,
        }
    }

    /// A proof of `input` at a name a person chose.
    #[must_use]
    pub fn named(input: &Path) -> Self {
        Self {
            input: input.to_path_buf(),
            input_sha256: None,
            placement: ProofPlacement::Named,
        }
    }
}

/// A proof's label: what it is, what made it and from what.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofLabel {
    /// Always `ay`.
    pub maker: String,
    /// The class the label claims for the bytes ([`ProofPlacement::class`]).
    pub class: String,
    /// The aterm session that ran ay, when there was one.
    pub session: Option<String>,
    /// The input's file name (`<B>`).
    pub input: String,
    /// The input's sha256 when the label was written.
    pub input_sha256: String,
    /// ay's build identity (`<version>+<commit>`).
    pub build: String,
    /// ay's full build stamp.
    pub build_stamp: String,
    /// The device the label was written on.
    pub device: u64,
    /// The inode the label was written on.
    pub inode: u64,
    /// The command that makes the proof again.
    pub command: String,
    /// The directory the command ran in, when it could be read.
    pub directory: Option<String>,
    /// The published proof's sha256; absent until publication, so an
    /// unpublished transaction file says so.
    pub proof_sha256: Option<String>,
}

/// A label's text was not one ay writes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LabelParseError(String);

impl fmt::Display for LabelParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "not an {LABEL_SCHEMA} label: {}", self.0)
    }
}

impl std::error::Error for LabelParseError {}

impl ProofLabel {
    /// The label's text: the schema line, then one `key=value` line per field,
    /// with `\` and newlines escaped.
    #[must_use]
    pub fn encode(&self) -> String {
        let mut out = format!("{LABEL_SCHEMA}\n");
        let mut field = |key: &str, value: &str| {
            out.push_str(key);
            out.push('=');
            out.push_str(&escape(value));
            out.push('\n');
        };
        field("maker", &self.maker);
        field("class", &self.class);
        if let Some(session) = &self.session {
            field("session", session);
        }
        field("input", &self.input);
        field("input_sha256", &self.input_sha256);
        field("build", &self.build);
        field("build_stamp", &self.build_stamp);
        field("device", &self.device.to_string());
        field("inode", &self.inode.to_string());
        field("command", &self.command);
        if let Some(directory) = &self.directory {
            field("directory", directory);
        }
        if let Some(proof_sha256) = &self.proof_sha256 {
            field("proof_sha256", proof_sha256);
        }
        out
    }

    /// Parse a label's text.
    ///
    /// # Errors
    ///
    /// The text does not start with [`LABEL_SCHEMA`], a line is not
    /// `key=value`, or a required field is missing or malformed.
    pub fn parse(text: &str) -> Result<Self, LabelParseError> {
        let mut lines = text.lines();
        if lines.next() != Some(LABEL_SCHEMA) {
            return Err(LabelParseError("missing schema line".to_string()));
        }
        let mut fields = std::collections::BTreeMap::new();
        for line in lines {
            let (key, value) = line
                .split_once('=')
                .ok_or_else(|| LabelParseError(format!("line without '=': {line:?}")))?;
            fields.insert(key.to_string(), unescape(value));
        }
        let mut take = |key: &str| {
            fields
                .remove(key)
                .ok_or_else(|| LabelParseError(format!("no {key}")))
        };
        let number = |key: &str, value: String| {
            value
                .parse::<u64>()
                .map_err(|_| LabelParseError(format!("{key} is not a number: {value:?}")))
        };
        Ok(Self {
            maker: take("maker")?,
            class: take("class")?,
            session: take("session").ok(),
            input: take("input")?,
            input_sha256: take("input_sha256")?,
            build: take("build")?,
            build_stamp: take("build_stamp")?,
            device: number("device", take("device")?)?,
            inode: number("inode", take("inode")?)?,
            command: take("command")?,
            directory: take("directory").ok(),
            proof_sha256: take("proof_sha256").ok(),
        })
    }

    /// Whether this label was written on `file`, not copied to it with its
    /// bytes.
    ///
    /// # Errors
    ///
    /// Any error reading the file's metadata.
    pub fn sits_on(&self, file: &File) -> io::Result<bool> {
        let (device, inode) = device_and_inode(file)?;
        Ok(self.device == device && self.inode == inode)
    }
}

fn escape(value: &str) -> String {
    value.replace('\\', "\\\\").replace('\n', "\\n")
}

fn unescape(value: &str) -> String {
    let mut out = String::with_capacity(value.len());
    let mut chars = value.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('n') => out.push('\n'),
                Some(other) => out.push(other),
                None => out.push('\\'),
            }
        } else {
            out.push(c);
        }
    }
    out
}

#[cfg(unix)]
fn device_and_inode(file: &File) -> io::Result<(u64, u64)> {
    use std::os::unix::fs::MetadataExt as _;
    let metadata = file.metadata()?;
    Ok((metadata.dev(), metadata.ino()))
}

#[cfg(not(unix))]
fn device_and_inode(_file: &File) -> io::Result<(u64, u64)> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "proof labels need a device and inode",
    ))
}

/// The command that makes the proof again: this process's own arguments.
fn this_command() -> String {
    let mut command = String::new();
    for (index, argument) in std::env::args_os().enumerate() {
        if index > 0 {
            command.push(' ');
        }
        let argument = argument.to_string_lossy();
        let plain = !argument.is_empty()
            && argument
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || "-_./:=+,@%".contains(c));
        if plain {
            command.push_str(&argument);
        } else {
            command.push('\'');
            command.push_str(&argument.replace('\'', "'\\''"));
            command.push('\'');
        }
    }
    command
}

fn this_directory() -> Option<String> {
    std::env::current_dir()
        .ok()
        .map(|directory| directory.to_string_lossy().into_owned())
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn write_label_attribute(file: &File, label: &ProofLabel) -> io::Result<()> {
    ay_sys::fs::set_xattr(file, LABEL_ATTRIBUTE, label.encode().as_bytes())
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn write_label_attribute(_file: &File, _label: &ProofLabel) -> io::Result<()> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "proof labels are extended attributes, unavailable on this platform",
    ))
}

/// Read the label on the file behind `file`; `None` when it has none.
///
/// # Errors
///
/// Any error reading the attribute, or an attribute that is not a label ay
/// writes.
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub fn read_label(file: &File) -> io::Result<Option<ProofLabel>> {
    let Some(bytes) = ay_sys::fs::get_xattr(file, LABEL_ATTRIBUTE)? else {
        return Ok(None);
    };
    let text = String::from_utf8(bytes)
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "label is not UTF-8"))?;
    ProofLabel::parse(&text)
        .map(Some)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))
}

/// Read the label on the file behind `file`; `None` when it has none.
///
/// # Errors
///
/// Never on this platform, which keeps no labels.
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
pub fn read_label(_file: &File) -> io::Result<Option<ProofLabel>> {
    Ok(None)
}

/// Read the label on the file at `path`, opened read-only.
///
/// # Errors
///
/// Any error opening the file or reading its label.
pub fn read_label_at(path: &Path) -> io::Result<Option<ProofLabel>> {
    read_label(&File::open(path)?)
}

/// Label a proof file at its creation: the maker, class, session, input,
/// build, the device and inode of `file`, and the command that makes it again.
///
/// The label goes on the descriptor, so it stays on the inode through the
/// rename or link that publishes the file. A filesystem without extended
/// attributes leaves a proof beside its input or at a person's name
/// unlabelled; a store proof fails instead.
///
/// # Errors
///
/// Any error hashing the input or writing the label (except as above).
pub fn label_at_creation(file: &File, subject: &ProofSubject) -> io::Result<()> {
    let input_sha256 = match &subject.input_sha256 {
        Some(sha256) => sha256.clone(),
        // A pipe or a device names no content to hash, and reading it again
        // could take bytes or block: its proof stays unlabelled.
        None if !fs::metadata(&subject.input)?.is_file() => return Ok(()),
        None => sha256_file(&subject.input)?,
    };
    let (device, inode) = match device_and_inode(file) {
        Err(error)
            if error.kind() == io::ErrorKind::Unsupported
                && subject.placement != ProofPlacement::Store =>
        {
            return Ok(());
        }
        result => result?,
    };
    let label = ProofLabel {
        maker: "ay".to_string(),
        class: subject.placement.class().to_string(),
        session: std::env::var("ATERM_SESSION_ID")
            .ok()
            .filter(|session| !session.is_empty()),
        input: subject
            .input
            .file_name()
            .map(|name| name.to_string_lossy().into_owned())
            .unwrap_or_default(),
        input_sha256,
        build: build_identity().to_string(),
        build_stamp: build_stamp().to_string(),
        device,
        inode,
        command: this_command(),
        directory: this_directory(),
        proof_sha256: None,
    };
    match write_label_attribute(file, &label) {
        Err(error)
            if error.kind() == io::ErrorKind::Unsupported
                && subject.placement != ProofPlacement::Store =>
        {
            Ok(())
        }
        result => result,
    }
}

/// Complete the label of a proof being published with the proof's own sha256.
/// A file with no label (a proof of standard input, or one on a filesystem
/// that keeps no extended attributes) is left as it is.
///
/// # Errors
///
/// Any error reading or writing the label, except that the filesystem keeps
/// none.
pub fn seal_label(file: &File, proof_sha256: &str) -> io::Result<()> {
    let mut label = match read_label(file) {
        Ok(Some(label)) => label,
        Ok(None) => return Ok(()),
        Err(error) if error.kind() == io::ErrorKind::Unsupported => return Ok(()),
        Err(error) => return Err(error),
    };
    label.proof_sha256 = Some(proof_sha256.to_string());
    write_label_attribute(file, &label)
}

/// Label a companion that stands beside a published proof (its status marker
/// or publication lock), with what the proof is derived from, unless it
/// already carries a label.
///
/// # Errors
///
/// As [`label_at_creation`].
pub fn label_companion(file: &File, subject: &ProofSubject) -> io::Result<()> {
    match read_label(file) {
        Ok(Some(_)) => Ok(()),
        Ok(None) => label_at_creation(file, subject),
        Err(error) if error.kind() == io::ErrorKind::Unsupported => {
            label_at_creation(file, subject)
        }
        Err(error) => Err(error),
    }
}

/// A proof store: `<store>/<input sha256>-<ay build>/`, tagged `CACHEDIR.TAG`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofStore {
    root: PathBuf,
}

impl ProofStore {
    /// Open the store at `root`: a folder ay tagged, or a new or empty one,
    /// which ay creates and tags.
    ///
    /// A store is a cache, which backup tools skip and a disk cleaner may
    /// empty, so ay never makes one of a folder that already holds anything:
    /// a non-empty folder opens only when its `CACHEDIR.TAG` carries the
    /// label ay wrote on it when it made the store. The tag is labelled when
    /// it is created, so a store on a filesystem that keeps no extended
    /// attributes is refused before any proof is written there unlabelled.
    /// Runs opening one store at once take turns on the folder's own lock,
    /// so a new store gets one tag.
    ///
    /// # Errors
    ///
    /// The folder cannot be created or locked, it is not empty and is not a
    /// store ay made, or the filesystem keeps no labels.
    pub fn open(root: &Path) -> io::Result<Self> {
        fs::create_dir_all(root)?;
        let root = fs::canonicalize(root)?;
        let folder = File::open(&root)?;
        folder.lock()?;
        let tag_path = root.join(STORE_TAG_NAME);
        match fs::symlink_metadata(&tag_path) {
            Ok(_) => check_store_tag(&tag_path)?,
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                if fs::read_dir(&root)?.next().is_some() {
                    return Err(io::Error::new(
                        io::ErrorKind::AlreadyExists,
                        format!(
                            "{} is not empty and is not a proof store ay made; a proof store is a new or empty folder",
                            root.display()
                        ),
                    ));
                }
                create_store_tag(&tag_path).map_err(|error| {
                    io::Error::new(
                        error.kind(),
                        format!("proof store {}: {error}", root.display()),
                    )
                })?;
            }
            Err(error) => return Err(error),
        }
        Ok(Self { root })
    }

    /// The store's folder.
    #[must_use]
    pub fn root(&self) -> &Path {
        &self.root
    }

    /// The slot for `input`, created when missing: `<input sha256>-<build>`.
    ///
    /// # Errors
    ///
    /// The input is not a regular file or cannot be read, or the slot cannot
    /// be created.
    pub fn slot(&self, input: &Path) -> io::Result<ProofSlot> {
        // The slot is named before the solver reads the input, so the input
        // must be a file that can be read twice, not a pipe.
        if !fs::metadata(input)?.is_file() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "{} is not a regular file; a proof store names each proof by its input's sha256",
                    input.display()
                ),
            ));
        }
        let input_sha256 = sha256_file(input)?;
        let input_name = input
            .file_name()
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "the input names no file"))?
            .to_os_string();
        let dir = self
            .root
            .join(format!("{input_sha256}-{}", build_identity()));
        match fs::create_dir(&dir) {
            Ok(()) => {}
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                if !fs::symlink_metadata(&dir)?.is_dir() {
                    return Err(io::Error::new(
                        io::ErrorKind::AlreadyExists,
                        format!("{} is not a folder", dir.display()),
                    ));
                }
            }
            Err(error) => return Err(error),
        }
        Ok(ProofSlot {
            dir,
            input: input.to_path_buf(),
            input_name,
            input_sha256,
        })
    }
}

/// Lock a store slot while making or inspecting its transaction names.
/// Writers hold this only until the new status descriptor itself is locked.
///
/// # Errors
///
/// The slot directory cannot be opened or locked.
pub fn lock_slot_directory(dir: &Path) -> io::Result<File> {
    let directory = File::open(dir)?;
    directory.lock()?;
    Ok(directory)
}

/// One input's folder in a proof store.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofSlot {
    dir: PathBuf,
    input: PathBuf,
    input_name: std::ffi::OsString,
    input_sha256: String,
}

/// What a check again found under one proof name in a slot.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StoredProof {
    /// No proof under that name (any that failed its check was set aside).
    Absent,
    /// A run that is still alive holds the name's status transaction: its
    /// proof is not final, and nothing under the name was touched.
    Busy(String),
    /// A proof that passed its check again: this input's proof from this
    /// build.
    Reused(PathBuf),
}

/// A name a check again renamed aside within the slot (never removed).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SetAside {
    /// Where it stood.
    pub name: PathBuf,
    /// Where it now is.
    pub aside: PathBuf,
    /// Why it does not count.
    pub why: String,
}

/// What [`ProofSlot::check_stored`] found and did.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SlotCheck {
    /// The proof under the name.
    pub proof: StoredProof,
    /// What was set aside first.
    pub set_aside: Vec<SetAside>,
}

/// Who holds a transaction file's lock.
enum Holder {
    Absent,
    /// A live run holds it.
    Held,
    /// Nobody: the file, open and locked by this call until it is dropped.
    Free(File),
    /// The name is not a regular file.
    Foreign,
}

/// Take `path`'s lock for a moment, without waiting: a lock this call can
/// take is a lock no live run holds, whatever process id it recorded.
fn holder(path: &Path) -> io::Result<Holder> {
    match fs::symlink_metadata(path) {
        Ok(metadata) if !metadata.is_file() => return Ok(Holder::Foreign),
        Ok(_) => {}
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(Holder::Absent),
        Err(error) => return Err(error),
    }
    let mut options = fs::OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(nix::libc::O_NOFOLLOW | nix::libc::O_NONBLOCK);
    }
    let file = match options.open(path) {
        Ok(file) => file,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(Holder::Absent),
        Err(error) => return Err(error),
    };
    match file.try_lock() {
        Ok(()) => Ok(Holder::Free(file)),
        Err(fs::TryLockError::WouldBlock) => Ok(Holder::Held),
        Err(fs::TryLockError::Error(error)) => Err(error),
    }
}

fn read_text(mut file: &File) -> io::Result<String> {
    let mut text = String::new();
    file.read_to_string(&mut text)?;
    Ok(text)
}

impl ProofSlot {
    /// The slot's folder.
    #[must_use]
    pub fn dir(&self) -> &Path {
        &self.dir
    }

    /// The input's sha256, as the slot's name carries it.
    #[must_use]
    pub fn input_sha256(&self) -> &str {
        &self.input_sha256
    }

    /// Where this input's proof with `proof_extension` goes in the slot.
    #[must_use]
    pub fn proof_path(&self, proof_extension: &str) -> PathBuf {
        let mut name = self.input_name.clone();
        name.push(".");
        name.push(proof_extension);
        self.dir.join(name)
    }

    /// The subject a proof written to this slot is labelled with.
    #[must_use]
    pub fn subject(&self) -> ProofSubject {
        ProofSubject {
            input: self.input.clone(),
            input_sha256: Some(self.input_sha256.clone()),
            placement: ProofPlacement::Store,
        }
    }

    /// Check again the proof stored under `proof_extension`, before it counts.
    ///
    /// While a live run holds the name's status transaction (its lock, or the
    /// marker it renamed the lock to), its proof is not final: the check
    /// touches nothing and says so. Otherwise a stored proof counts when its
    /// label names this input's sha256 and this build, sits on the file's own
    /// device and inode, and records a proof sha256 that the file's bytes
    /// still hash to, and when its status marker, if it has one, names it as
    /// current with that sha256. A stored proof that fails is renamed aside
    /// within the slot with its marker; so are a lock and a marker a dead run
    /// left with no proof, which would stop every later run from publishing.
    /// Nothing is removed.
    ///
    /// # Errors
    ///
    /// Any error reading the slot or renaming a name aside.
    pub fn check_stored(&self, proof_extension: &str) -> io::Result<SlotCheck> {
        let _directory = lock_slot_directory(&self.dir)?;
        self.check_under_lock(proof_extension)
    }

    fn check_under_lock(&self, proof_extension: &str) -> io::Result<SlotCheck> {
        let proof = self.proof_path(proof_extension);
        let marker = suffixed(&proof, STATUS_MARKER_SUFFIX);
        let lock = suffixed(&marker, STATUS_LOCK_SUFFIX);
        let mut set_aside = Vec::new();
        let busy = |why: String, set_aside: Vec<SetAside>| SlotCheck {
            proof: StoredProof::Busy(why),
            set_aside,
        };

        match holder(&lock)? {
            Holder::Absent => {}
            Holder::Held => {
                return Ok(busy(
                    format!("a live run holds {}", lock.display()),
                    set_aside,
                ))
            }
            Holder::Foreign => set_aside.push(self.set_aside(
                &lock,
                "the status transaction lock is not a regular file".to_string(),
            )?),
            Holder::Free(_file) => {
                // A writer locks the slot before creating the name and releases
                // it after locking its descriptor. A free descriptor is therefore
                // abandoned even if its writer died before writing the header.
                set_aside.push(self.set_aside(
                    &lock,
                    "the run that took this status transaction is gone".to_string(),
                )?);
            }
        }

        let marker_text = match holder(&marker)? {
            Holder::Absent => None,
            Holder::Held => {
                return Ok(busy(
                    format!("a live run holds {}", marker.display()),
                    set_aside,
                ))
            }
            Holder::Foreign => {
                set_aside.push(self.set_aside(
                    &marker,
                    "the status marker is not a regular file".to_string(),
                )?);
                None
            }
            Holder::Free(file) => Some(read_text(&file)?),
        };

        let metadata = match fs::symlink_metadata(&proof) {
            Ok(metadata) => metadata,
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                if let Some(text) = marker_text {
                    let status = text
                        .lines()
                        .find(|line| line.starts_with("status="))
                        .unwrap_or("no status")
                        .to_string();
                    set_aside.push(self.set_aside(
                        &marker,
                        format!("its run is gone and left no proof ({status})"),
                    )?);
                }
                return Ok(SlotCheck {
                    proof: StoredProof::Absent,
                    set_aside,
                });
            }
            Err(error) => return Err(error),
        };
        let why = if metadata.is_file() {
            self.why_stored_proof_fails(&proof, marker_text.as_deref())?
        } else {
            Some("it is not a regular file".to_string())
        };
        let Some(why) = why else {
            return Ok(SlotCheck {
                proof: StoredProof::Reused(proof),
                set_aside,
            });
        };
        set_aside.push(self.set_aside_with_marker(&proof, &marker, why)?);
        Ok(SlotCheck {
            proof: StoredProof::Absent,
            set_aside,
        })
    }

    /// Set aside the stored proof under `proof_extension`, which passed its
    /// check again, because this run must make its own (`why`).
    ///
    /// # Errors
    ///
    /// Any error renaming it aside.
    pub fn supersede(&self, proof_extension: &str, why: String) -> io::Result<SetAside> {
        let _directory = lock_slot_directory(&self.dir)?;
        let proof = match self.check_under_lock(proof_extension)?.proof {
            StoredProof::Reused(proof) => proof,
            StoredProof::Busy(why) => return Err(io::Error::new(io::ErrorKind::WouldBlock, why)),
            StoredProof::Absent => return Err(io::Error::from(io::ErrorKind::NotFound)),
        };
        let marker = suffixed(&proof, STATUS_MARKER_SUFFIX);
        self.set_aside_with_marker(&proof, &marker, why)
    }

    fn why_stored_proof_fails(
        &self,
        proof: &Path,
        marker_text: Option<&str>,
    ) -> io::Result<Option<String>> {
        let mut file = File::open(proof)?;
        let label = match read_label(&file) {
            Ok(Some(label)) => label,
            Ok(None) => return Ok(Some("it carries no label".to_string())),
            Err(error) => return Ok(Some(format!("its label cannot be read: {error}"))),
        };
        if label.input_sha256 != self.input_sha256 {
            return Ok(Some(format!(
                "its label names input sha256 {}, not {}",
                label.input_sha256, self.input_sha256
            )));
        }
        if label.build != build_identity() {
            return Ok(Some(format!(
                "its label names build {}, not {}",
                label.build,
                build_identity()
            )));
        }
        if !label.sits_on(&file)? {
            return Ok(Some(
                "its label was written on another file (a copy)".to_string(),
            ));
        }
        let Some(recorded) = label.proof_sha256 else {
            return Ok(Some("its label records no published proof".to_string()));
        };
        let actual = sha256_reader(&mut file)?;
        if actual != recorded {
            return Ok(Some(format!(
                "its bytes hash to {actual}, not the {recorded} its label records"
            )));
        }
        if let Some(text) = marker_text {
            let current = text.lines().any(|line| line == STATUS_CURRENT);
            let names_it = text
                .lines()
                .any(|line| line.strip_prefix("sha256=") == Some(actual.as_str()));
            if !(current && names_it) {
                return Ok(Some(
                    "its status marker does not name it as its run's current proof".to_string(),
                ));
            }
        }
        Ok(None)
    }

    /// Rename `name` aside within the slot as `.<name>.rejected-<pid>-<n>`.
    fn set_aside(&self, name: &Path, why: String) -> io::Result<SetAside> {
        let file_name = name
            .file_name()
            .map(|name| name.to_string_lossy().into_owned())
            .unwrap_or_default();
        let pid = std::process::id();
        let mut nonce = 0u64;
        loop {
            let aside = self
                .dir
                .join(format!(".{file_name}.rejected-{pid}-{nonce}"));
            match rename_noreplace(name, &aside) {
                Ok(()) => {
                    return Ok(SetAside {
                        name: name.to_path_buf(),
                        aside,
                        why,
                    })
                }
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => nonce += 1,
                Err(error) => return Err(error),
            }
        }
    }

    /// Set aside a proof and, beside its new name, the status marker that
    /// describes it: the DRAT writer never replaces a marker, so one left in
    /// place would stop the fresh proof from being published.
    fn set_aside_with_marker(
        &self,
        proof: &Path,
        marker: &Path,
        why: String,
    ) -> io::Result<SetAside> {
        let moved = self.set_aside(proof, why)?;
        let marker_aside = suffixed(&moved.aside, STATUS_MARKER_SUFFIX);
        match rename_noreplace(marker, &marker_aside) {
            Ok(()) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
        Ok(moved)
    }
}

/// `path` with `suffix` appended to its name.
fn suffixed(path: &Path, suffix: &str) -> PathBuf {
    let mut name = path.as_os_str().to_os_string();
    name.push(suffix);
    PathBuf::from(name)
}

/// The label ay writes on a store's tag when it makes the store.
fn store_tag_label(tag: &File) -> io::Result<ProofLabel> {
    let (device, inode) = device_and_inode(tag)?;
    Ok(ProofLabel {
        maker: "ay".to_string(),
        class: "cache".to_string(),
        session: std::env::var("ATERM_SESSION_ID")
            .ok()
            .filter(|session| !session.is_empty()),
        input: String::new(),
        input_sha256: String::new(),
        build: build_identity().to_string(),
        build_stamp: build_stamp().to_string(),
        device,
        inode,
        command: this_command(),
        directory: this_directory(),
        proof_sha256: None,
    })
}

/// Create a new store's tag, labelled before a byte is written. A tag whose
/// label cannot be written is unlinked again: it is this call's own new file,
/// and an unlabelled tag would make the folder look like a stranger's.
fn create_store_tag(tag_path: &Path) -> io::Result<()> {
    let mut tag = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(tag_path)?;
    let written = store_tag_label(&tag)
        .and_then(|label| write_label_attribute(&tag, &label))
        .map_err(|error| io::Error::new(error.kind(), format!("cannot hold proof labels: {error}")))
        .and_then(|()| {
            tag.write_all(
                format!(
                    "{CACHEDIR_TAG_SIGNATURE}\n\
                     # This file is a cache directory tag created by ay: a proof store.\n\
                     # Every proof here is made again by solving its input again.\n\
                     # For information about cache directory tags, see:\n\
                     #\thttps://bford.info/cachedir/\n"
                )
                .as_bytes(),
            )?;
            tag.sync_all()
        });
    if written.is_err() {
        drop(tag);
        let _ = fs::remove_file(tag_path);
    }
    written
}

/// A store's tag must be a cache-directory tag carrying the label ay wrote on
/// that very file: a tag a person placed, another tool's, or one copied with
/// its folder does not make a store.
fn check_store_tag(tag_path: &Path) -> io::Result<()> {
    let not_ours = |why: &str| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "{} exists and is not the tag of a proof store ay made: {why}",
                tag_path.display()
            ),
        )
    };
    if !fs::symlink_metadata(tag_path)?.is_file() {
        return Err(not_ours("it is not a regular file"));
    }
    let tag = File::open(tag_path)?;
    let mut head = Vec::with_capacity(CACHEDIR_TAG_SIGNATURE.len());
    (&tag)
        .take(CACHEDIR_TAG_SIGNATURE.len() as u64)
        .read_to_end(&mut head)?;
    if head != CACHEDIR_TAG_SIGNATURE.as_bytes() {
        return Err(not_ours("it is not a cache directory tag"));
    }
    let label = match read_label(&tag) {
        Ok(Some(label)) => label,
        Ok(None) => return Err(not_ours("it carries no label of ay's")),
        Err(error) => return Err(not_ours(&format!("its label cannot be read: {error}"))),
    };
    if label.maker != "ay" {
        return Err(not_ours(&format!("its label names maker {}", label.maker)));
    }
    if !label.sits_on(&tag)? {
        return Err(not_ours("its label was written on another file (a copy)"));
    }
    Ok(())
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn rename_noreplace(source: &Path, target: &Path) -> io::Result<()> {
    ay_sys::fs::rename_noreplace(source, target)
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn rename_noreplace(source: &Path, target: &Path) -> io::Result<()> {
    if target.exists() {
        return Err(io::Error::from(io::ErrorKind::AlreadyExists));
    }
    fs::rename(source, target)
}

#[cfg(test)]
#[path = "proof_store_tests.rs"]
mod tests;
