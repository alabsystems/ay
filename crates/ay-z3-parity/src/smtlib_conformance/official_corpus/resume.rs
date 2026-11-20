// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

const INTENT: &str = "producer.lock";

/// The stable directory and intent file outlive individual certificate
/// attempts. Hold the same lock through record and receipt publication.
pub(super) struct Campaign {
    pub(super) results: PathBuf,
    pub(super) receipt: PathBuf,
    pub(super) evidence: PathBuf,
    directory: fs::File,
    lock: fs::File,
    receipt_parent: fs::File,
}

impl Campaign {
    pub(super) fn open(
        options: &RunArgs,
        base: &Path,
        contract_sha256: &str,
        evaluator_sha256: &str,
        corpus_sha256: &str,
    ) -> Result<Self, String> {
        let results_relative = future_relative_output(base, &options.results)?;
        let receipt_relative = future_relative_output(base, &options.receipt)?;
        let results = base.join(&results_relative);
        let receipt = base.join(&receipt_relative);
        let evidence = results.with_extension("evidence");
        if results == receipt || results == evidence || receipt.starts_with(&evidence) {
            return Err(
                "official corpus results, receipt and evidence paths must be distinct".into(),
            );
        }
        let intent = serde_json::to_vec(&(
            "ay-official-smtlib-corpus-producer-intent/v1",
            contract_sha256,
            evaluator_sha256,
            corpus_sha256,
            results_relative,
            receipt_relative,
        ))
        .map_err(|error| error.to_string())?;
        let intent_path = evidence.join(INTENT);
        let receipt_parent = open_directory(receipt.parent().ok_or("receipt has no parent")?)?;
        if !options.resume {
            if publication_exists(&results)? || publication_exists(&receipt)? {
                return Err(
                    "official corpus output already exists; use --resume for this campaign".into(),
                );
            }
            let mut builder = fs::DirBuilder::new();
            #[cfg(unix)]
            {
                use std::os::unix::fs::DirBuilderExt;
                builder.mode(0o700);
            }
            builder.create(&evidence).map_err(|error| {
                format!(
                    "create new query evidence directory {}: {error}",
                    evidence.display()
                )
            })?;
            atomic_write_new(&intent_path, &intent)?;
            sync_corpus_directory(results.parent().ok_or("results have no parent")?)?;
        }
        let directory = open_directory(&evidence)?;
        let mut lock = open_regular(&intent_path, true)?;
        lock.try_lock()
            .map_err(|error| format!("acquire official corpus producer lease: {error}"))?;
        let mut observed = Vec::new();
        (&mut lock)
            .take(intent.len() as u64 + 1)
            .read_to_end(&mut observed)
            .map_err(|error| format!("read official corpus producer intent: {error}"))?;
        if observed != intent {
            return Err("official corpus evidence belongs to a different producer, contract, corpus or output".into());
        }
        let campaign = Self {
            results,
            receipt,
            evidence,
            directory,
            lock,
            receipt_parent,
        };
        campaign.check()?;
        if publication_exists(&campaign.receipt)? && !publication_exists(&campaign.results)? {
            return Err("official corpus receipt exists without its results".into());
        }
        Ok(campaign)
    }

    pub(super) fn check(&self) -> Result<(), String> {
        let current = fs::canonicalize(&self.evidence).map_err(|error| error.to_string())?;
        let metadata = fs::symlink_metadata(&self.evidence).map_err(|error| error.to_string())?;
        if current != self.evidence
            || !private_directory(&metadata)
            || !same_inode(
                &metadata,
                &self
                    .directory
                    .metadata()
                    .map_err(|error| error.to_string())?,
            )
        {
            return Err("official corpus evidence directory was replaced or redirected".into());
        }
        let lock =
            fs::symlink_metadata(self.evidence.join(INTENT)).map_err(|error| error.to_string())?;
        if !private_regular(&lock)
            || !same_inode(
                &lock,
                &self.lock.metadata().map_err(|error| error.to_string())?,
            )
        {
            return Err("official corpus producer intent was linked or replaced".into());
        }
        let receipt_parent = self.receipt.parent().ok_or("receipt has no parent")?;
        if fs::canonicalize(receipt_parent).map_err(|error| error.to_string())? != receipt_parent
            || !same_inode(
                &fs::symlink_metadata(receipt_parent).map_err(|error| error.to_string())?,
                &self
                    .receipt_parent
                    .metadata()
                    .map_err(|error| error.to_string())?,
            )
        {
            return Err("official corpus receipt directory was replaced".into());
        }
        Ok(())
    }
}

fn open_directory(path: &Path) -> Result<fs::File, String> {
    let mut options = fs::OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW);
    }
    let file = options.open(path).map_err(|error| {
        format!(
            "open existing official corpus evidence directory {}: {error}",
            path.display()
        )
    })?;
    let metadata = file.metadata().map_err(|error| error.to_string())?;
    if !metadata.is_dir() {
        return Err("official corpus evidence root must be a private directory".into());
    }
    Ok(file)
}

fn private_directory(metadata: &fs::Metadata) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        if metadata.mode() & 0o077 != 0 {
            return false;
        }
    }
    metadata.is_dir()
}

pub(super) fn publication_exists(path: &Path) -> Result<bool, String> {
    match fs::symlink_metadata(path) {
        Ok(metadata) if private_regular(&metadata) => Ok(true),
        Ok(_) => Err(format!(
            "official corpus path is linked or non-regular: {}",
            path.display()
        )),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(format!(
            "inspect official corpus path {}: {error}",
            path.display()
        )),
    }
}

fn private_regular(metadata: &fs::Metadata) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        if metadata.nlink() != 1 {
            return false;
        }
    }
    metadata.is_file()
}

fn same_inode(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        left.dev() == right.dev() && left.ino() == right.ino()
    }
    #[cfg(not(unix))]
    {
        left.created().ok() == right.created().ok()
    }
}

fn open_regular(path: &Path, writable: bool) -> Result<fs::File, String> {
    let mut options = fs::OpenOptions::new();
    options.read(true).write(writable);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
    }
    let file = options
        .open(path)
        .map_err(|error| format!("open {}: {error}", path.display()))?;
    let current = fs::symlink_metadata(path).map_err(|error| error.to_string())?;
    let opened = file.metadata().map_err(|error| error.to_string())?;
    if !private_regular(&current) || !private_regular(&opened) || !same_inode(&current, &opened) {
        return Err(format!(
            "official corpus file is linked, replaced or non-regular: {}",
            path.display()
        ));
    }
    Ok(file)
}

pub(super) fn read_publication(path: &Path, limit: u64) -> Result<Vec<u8>, String> {
    let file = open_regular(path, false)?;
    let length = file.metadata().map_err(|error| error.to_string())?.len();
    if length > limit {
        return Err(format!(
            "official corpus file exceeds the {limit}-byte limit: {}",
            path.display()
        ));
    }
    let mut bytes = Vec::new();
    file.take(limit + 1)
        .read_to_end(&mut bytes)
        .map_err(|error| error.to_string())?;
    if bytes.len() as u64 != length {
        return Err(format!(
            "official corpus file size changed: {}",
            path.display()
        ));
    }
    Ok(bytes)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn options(base: &Path) -> RunArgs {
        RunArgs {
            manifest: base.join("contract.json"),
            corpus_manifest: base.join("corpus.json"),
            receipt: base.join("receipt.json"),
            results: base.join("results.json"),
            ay: None,
            z3: None,
            carcara: None,
            timeout_secs: 10,
            resume: false,
        }
    }

    #[test]
    fn producer_lease_excludes_another_writer_through_result_and_receipt_publication() {
        let directory = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(directory.path()).unwrap();
        let mut options = options(&base);
        let lease = Campaign::open(&options, &base, "contract", "evaluator", "corpus").unwrap();
        options.resume = true;
        assert!(Campaign::open(&options, &base, "contract", "evaluator", "corpus").is_err());
        atomic_write_new(&lease.results, b"published results").unwrap();
        assert!(Campaign::open(&options, &base, "contract", "evaluator", "corpus").is_err());
        drop(lease);

        assert!(Campaign::open(&options, &base, "contract", "different", "corpus").is_err());
        let lease = Campaign::open(&options, &base, "contract", "evaluator", "corpus").unwrap();
        assert_eq!(
            read_publication(&lease.results, 100).unwrap(),
            b"published results"
        );
        assert!(!publication_exists(&lease.receipt).unwrap());
        atomic_write_new(&lease.receipt, b"published receipt").unwrap();
        assert!(Campaign::open(&options, &base, "contract", "evaluator", "corpus").is_err());
        drop(lease);
        fs::remove_file(&options.results).unwrap();
        assert!(Campaign::open(&options, &base, "contract", "evaluator", "corpus").is_err());
        assert_eq!(fs::read(&options.receipt).unwrap(), b"published receipt");
    }

    #[cfg(unix)]
    #[test]
    fn resume_rejects_alien_evidence_directories_symlinks_and_hardlinks() {
        use std::os::unix::fs::symlink;

        let directory = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(directory.path()).unwrap();
        let mut options = options(&base);
        let evidence = options.results.with_extension("evidence");
        fs::create_dir(&evidence).unwrap();
        let alien = evidence.join("records.jsonl");
        fs::write(&alien, b"external checkpoint").unwrap();
        assert!(Campaign::open(&options, &base, "contract", "evaluator", "corpus").is_err());
        options.resume = true;
        assert!(Campaign::open(&options, &base, "contract", "evaluator", "corpus").is_err());
        assert_eq!(fs::read(&alien).unwrap(), b"external checkpoint");
        let renamed = base.join("foreign");
        fs::rename(&evidence, &renamed).unwrap();
        symlink(&renamed, &evidence).unwrap();
        assert!(Campaign::open(&options, &base, "contract", "evaluator", "corpus").is_err());
        assert_eq!(
            fs::read(renamed.join("records.jsonl")).unwrap(),
            b"external checkpoint"
        );
        fs::hard_link(renamed.join("records.jsonl"), &options.results).unwrap();
        assert!(publication_exists(&options.results).is_err());
    }
}
