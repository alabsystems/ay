// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn hash_file(file: &mut File) -> io::Result<(u64, Sha256Digest)> {
    file.seek(SeekFrom::Start(0))?;
    let mut hasher = Sha256::new();
    let mut len = 0_u64;
    let mut buffer = vec![0_u8; 64 * 1024];
    loop {
        let read = file.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        len = len
            .checked_add(read as u64)
            .ok_or_else(|| io::Error::other("DIMACS proof length overflow"))?;
        hasher.update(&buffer[..read]);
    }
    Ok((len, hasher.finalize().into()))
}

impl RetainedDimacsPublication {
    fn capture(
        mut descriptor: File,
        path: PathBuf,
        label: &'static str,
        expected: Option<PublishedDimacsProof>,
        invalidation: DimacsPublicationInvalidation,
    ) -> io::Result<Self> {
        let invalidation_descriptor = match descriptor.try_clone() {
            Ok(clone) => clone,
            Err(error) => {
                return Err(dimacs_invalidation_error(
                    error,
                    invalidate_dimacs_descriptor(&descriptor, invalidation),
                    label,
                ));
            }
        };
        let captured = (|| -> io::Result<Self> {
            let identity = regular_single_link_identity(&descriptor, &path)?;
            let (len, sha256) = hash_file(&mut descriptor)?;
            if let Some(expected) = expected {
                if identity != expected.identity || len != expected.len || sha256 != expected.sha256
                {
                    return Err(io::Error::other(format!(
                        "retained {label} descriptor does not match its same-run publication seal"
                    )));
                }
            }
            let mut visible = open_dimacs_regular_file(&path)?;
            if regular_single_link_identity(&visible, &path)? != identity {
                return Err(io::Error::other(format!(
                    "{label} path '{}' does not name its retained same-run descriptor",
                    path.display()
                )));
            }
            let (visible_len, visible_sha256) = hash_file(&mut visible)?;
            if visible_len != len || visible_sha256 != sha256 {
                return Err(io::Error::other(format!(
                    "{label} path '{}' changed while publication authority was captured",
                    path.display()
                )));
            }
            Ok(Self {
                descriptor,
                path,
                identity,
                len,
                sha256,
                label,
                invalidation,
            })
        })();
        match captured {
            Ok(publication) => Ok(publication),
            Err(error) => Err(dimacs_invalidation_error(
                error,
                invalidate_dimacs_descriptor(&invalidation_descriptor, invalidation),
                label,
            )),
        }
    }

    fn validate(&mut self) -> io::Result<()> {
        if regular_single_link_identity(&self.descriptor, &self.path)? != self.identity {
            return Err(io::Error::other(format!(
                "retained {} descriptor identity changed",
                self.label
            )));
        }
        let (descriptor_len, descriptor_sha256) = hash_file(&mut self.descriptor)?;
        if descriptor_len != self.len || descriptor_sha256 != self.sha256 {
            return Err(io::Error::other(format!(
                "retained {} descriptor bytes changed",
                self.label
            )));
        }
        let mut visible = open_dimacs_regular_file(&self.path)?;
        if regular_single_link_identity(&visible, &self.path)? != self.identity {
            return Err(io::Error::other(format!(
                "{} path '{}' was replaced",
                self.label,
                self.path.display()
            )));
        }
        let (visible_len, visible_sha256) = hash_file(&mut visible)?;
        if visible_len != self.len || visible_sha256 != self.sha256 {
            return Err(io::Error::other(format!(
                "{} path '{}' changed after authorization",
                self.label,
                self.path.display()
            )));
        }
        Ok(())
    }

    fn invalidate_exact(&self) -> io::Result<()> {
        invalidate_dimacs_descriptor(&self.descriptor, self.invalidation)
    }
}

#[cfg(target_os = "linux")]
fn publish_dimacs_descriptor_noreplace(descriptor: &File, target: &Path) -> io::Result<()> {
    use std::os::fd::AsRawFd as _;

    let empty_path_error = match nix::unistd::linkat(
        Some(descriptor.as_raw_fd()),
        Path::new(""),
        None,
        target,
        nix::fcntl::AtFlags::AT_EMPTY_PATH,
    ) {
        Ok(()) => return Ok(()),
        Err(error) => error,
    };
    if !matches!(
        empty_path_error,
        nix::errno::Errno::ENOENT | nix::errno::Errno::EPERM | nix::errno::Errno::EACCES
    ) {
        return Err(io::Error::from_raw_os_error(empty_path_error as i32));
    }

    // Ordinary unprivileged processes commonly lack CAP_DAC_READ_SEARCH,
    // which Linux requires for AT_EMPTY_PATH. /proc/self/fd exposes the same
    // already-authenticated descriptor; AT_SYMLINK_FOLLOW follows that procfs
    // link and `linkat` still fails with EEXIST instead of replacing `target`.
    let descriptor_path = PathBuf::from(format!("/proc/self/fd/{}", descriptor.as_raw_fd()));
    nix::unistd::linkat(
        None,
        descriptor_path.as_path(),
        None,
        target,
        nix::fcntl::AtFlags::AT_SYMLINK_FOLLOW,
    )
    .map_err(|proc_error| {
        let proc_error = io::Error::from_raw_os_error(proc_error as i32);
        io::Error::new(
            proc_error.kind(),
            format!(
                "descriptor publication failed via AT_EMPTY_PATH ({empty_path_error}) and /proc/self/fd ({proc_error})"
            ),
        )
    })
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn rename_dimacs_noreplace(source: &Path, target: &Path) -> io::Result<()> {
    #[cfg(test)]
    if let Some(raw_os_error) = take_injected_dimacs_rename_noreplace_error() {
        return Err(io::Error::from_raw_os_error(raw_os_error));
    }
    ay_sys::fs::rename_noreplace(source, target)
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn move_dimacs_proof_to_private_quarantine(source: &Path, target: &Path) -> io::Result<()> {
    // Never remove a public pathname unless the same platform can atomically
    // restore a quarantined replacement without clobbering another object.
    // Unsupported platforms fail before mutating either pathname.
    rename_dimacs_noreplace(source, target)
}

fn invalidate_dimacs_descriptor(
    descriptor: &File,
    invalidation: DimacsPublicationInvalidation,
) -> io::Result<()> {
    let tombstone: &[u8] = match invalidation {
        DimacsPublicationInvalidation::Empty => b"",
        // Empty DRAT/LRAT can certify an input that already contains the empty
        // clause. These tombstones are syntactically invalid in their declared
        // encodings: text has a non-numeric unterminated record; binary has a
        // non-UTF-8 byte that is neither an `a` nor `d` record marker.
        DimacsPublicationInvalidation::Proof { binary: false } => b"invalidated-by-ay\n",
        DimacsPublicationInvalidation::Proof { binary: true } => b"\x80",
    };
    descriptor.set_len(0)?;
    let mut writer = descriptor;
    writer.seek(SeekFrom::Start(0))?;
    writer.write_all(tombstone)?;
    descriptor.sync_all()
}

fn dimacs_invalidation_error(
    operation_error: io::Error,
    invalidation: io::Result<()>,
    label: &str,
) -> io::Error {
    match invalidation {
        Ok(()) => operation_error,
        Err(invalidation_error) => io::Error::other(format!(
            "{operation_error}; exact {label} descriptor invalidation also failed: {invalidation_error}"
        )),
    }
}

fn remove_authenticated_visible_file(
    path: &Path,
    descriptor: &File,
    identity: ProofFileIdentity,
    label: &str,
    invalidation: DimacsPublicationInvalidation,
) -> io::Result<bool> {
    remove_authenticated_visible_file_body(AuthenticatedRemoval {
        path,
        descriptor,
        identity,
        label,
        invalidation,
    })
}
