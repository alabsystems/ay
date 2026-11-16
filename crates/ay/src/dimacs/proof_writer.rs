// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn proof_output_writer(file: File) -> BufWriter<File> {
    BufWriter::with_capacity(PROOF_OUTPUT_BUFFER_CAPACITY, file)
}

/// The file under a proof's write buffer. For a fast-publication generation it
/// hashes exactly the bytes each `write(2)` accepted, in offset order, off the
/// writing thread (see `ProofHash`), so the seal can bind the proof to its
/// digest without reading it back.
///
/// Only `write` and `flush` are implemented: `write_all` and `write_vectored`
/// default to `write`, so an unaccepted suffix is never hashed.
struct HashingProofFile {
    file: File,
    hash: Option<ProofHash>,
    len: u64,
    guard: ProofSpaceGuard,
}

impl Write for HashingProofFile {
    fn write(&mut self, buffer: &[u8]) -> io::Result<usize> {
        // The disk reserve and the optional ceiling stop the proof here, before
        // the bytes land, and reach the solver as any other write error does.
        self.guard.check(self.len, buffer.len())?;
        let written = self.file.write(buffer)?;
        if let Some(hash) = &mut self.hash {
            hash.update(&buffer[..written]);
        }
        self.len += written as u64;
        Ok(written)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.file.flush()?;
        // The solver flushes at each inprocessing boundary, which is the look
        // at the disk that does not depend on how fast the proof is growing.
        self.guard.probe_now(self.len)
    }
}

impl HashingProofFile {
    /// The digest of the whole file, if this writer wrote all of it: the
    /// descriptor's offset and the file's length both equal the bytes hashed,
    /// so nothing else wrote, truncated or rewound it.
    fn finish(mut self) -> Option<StreamedDimacsProofDigest> {
        let hash = self.hash.take()?;
        let offset = self.file.stream_position().ok()?;
        let len = self.file.metadata().ok()?.len();
        if offset != self.len || len != self.len {
            return None;
        }
        Some(StreamedDimacsProofDigest {
            len: self.len,
            sha256: hash.finish()?,
        })
    }
}

/// The solver's buffered proof sink, which never completes an abandoned proof.
///
/// Once its generation is abandoned (a run that will not answer, see
/// proof_custody.rs) it writes nothing more, and dropping it discards the
/// buffered bytes instead of flushing them, as `BufWriter`'s own drop would.
/// A live fast-publication sink records its digest in the custody when it is
/// dropped after a clean final flush.
struct ProofWriteBuffer {
    /// `Some` until drop.
    writer: Option<BufWriter<HashingProofFile>>,
    custody: Arc<DimacsProofCustody>,
}

impl ProofWriteBuffer {
    fn new(file: File, custody: Arc<DimacsProofCustody>, guard: ProofSpaceGuard) -> Self {
        let file = HashingProofFile {
            file,
            hash: custody.fast_publication.then(ProofHash::start),
            len: 0,
            guard,
        };
        Self {
            writer: Some(BufWriter::with_capacity(PROOF_OUTPUT_BUFFER_CAPACITY, file)),
            custody,
        }
    }

    fn live(&mut self) -> Option<&mut BufWriter<HashingProofFile>> {
        if self.custody.is_abandoned() {
            return None;
        }
        self.writer.as_mut()
    }
}

impl Write for ProofWriteBuffer {
    fn write(&mut self, buffer: &[u8]) -> io::Result<usize> {
        match self.live() {
            Some(writer) => writer.write(buffer),
            None => Ok(buffer.len()),
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        match self.live() {
            Some(writer) => writer.flush(),
            None => Ok(()),
        }
    }
}

impl Drop for ProofWriteBuffer {
    fn drop(&mut self) {
        let Some(writer) = self.writer.take() else {
            return;
        };
        if self.custody.is_abandoned() {
            // Unwritten bytes and descriptor are dropped; nothing is flushed.
            drop(writer.into_parts());
            return;
        }
        // The one final flush `BufWriter`'s own drop would make. A failed one
        // records no digest, and the seal falls back to reading the proof.
        match writer.into_inner() {
            Ok(file) => {
                if let Some(digest) = file.finish() {
                    if !self.custody.is_abandoned() {
                        self.custody.record_streamed_digest(digest);
                    }
                }
            }
            Err(unflushed) => drop(unflushed.into_inner().into_parts()),
        }
    }
}

enum SolverDimacsProofWriter {
    Required(ProofWriteBuffer),
    Optional {
        writer: ProofWriteBuffer,
        path: String,
        failed: Arc<AtomicBool>,
    },
}

impl Write for SolverDimacsProofWriter {
    fn write(&mut self, buffer: &[u8]) -> io::Result<usize> {
        match self {
            Self::Required(writer) => writer.write(buffer),
            Self::Optional {
                writer,
                path,
                failed,
            } => {
                if failed.load(Ordering::Acquire) {
                    return Ok(buffer.len());
                }
                #[cfg(all(test, target_os = "linux"))]
                if take_injected_optional_dimacs_writer_failure() {
                    safe_eprintln!(
                        "c Warning: optional synthesized DIMACS proof {path} stopped recording after an injected write failure; solver verdict remains authoritative"
                    );
                    failed.store(true, Ordering::Release);
                    return Ok(buffer.len());
                }
                match writer.write_all(buffer) {
                    Ok(()) => Ok(buffer.len()),
                    Err(error) => {
                        safe_eprintln!(
                            "c Warning: optional synthesized DIMACS proof {path} stopped recording after a write failure: {error}; solver verdict remains authoritative"
                        );
                        failed.store(true, Ordering::Release);
                        Ok(buffer.len())
                    }
                }
            }
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        match self {
            Self::Required(writer) => writer.flush(),
            Self::Optional {
                writer,
                path,
                failed,
            } => {
                if failed.load(Ordering::Acquire) {
                    return Ok(());
                }
                if let Err(error) = writer.flush() {
                    safe_eprintln!(
                        "c Warning: optional synthesized DIMACS proof {path} failed to flush: {error}; solver verdict remains authoritative"
                    );
                    failed.store(true, Ordering::Release);
                }
                Ok(())
            }
        }
    }
}

fn solver_proof_output_writer(
    file: File,
    proof: &ProofConfig,
) -> io::Result<SolverDimacsProofWriter> {
    let writer = ProofWriteBuffer::new(
        file,
        owned_dimacs_proof_custody(&proof.path)?,
        ProofSpaceGuard::for_proof(&proof.path),
    );
    if synthesized_default_dimacs_proof_is_optional(proof) {
        Ok(SolverDimacsProofWriter::Optional {
            writer,
            path: proof.path.clone(),
            failed: owned_dimacs_proof_write_failure_flag(&proof.path)?,
        })
    } else {
        Ok(SolverDimacsProofWriter::Required(writer))
    }
}

/// The solver's proof writer never completes the proof of a run that will not
/// answer (2026-09-13): once the generation is abandoned, its buffered bytes
/// are dropped instead of flushed and nothing more is written. These run the
/// real sink over a real file, because only a real file shows what a
/// `BufWriter` drop writes; every ay-sat proof test uses an in-memory sink.
#[cfg(all(test, any(target_os = "linux", target_os = "macos", windows)))]
mod proof_write_buffer_tests {
    use super::*;

    fn required_drat_proof(dir: &Path) -> ProofConfig {
        ProofConfig {
            path: dir.join("proof.drat").to_string_lossy().into_owned(),
            format: ProofFormat::Drat,
            binary: false,
            artifact_path: None,
            is_temp: false,
            synthesized_default: false,
            format_was_explicit: true,
        }
    }

    /// The bytes on disk behind the generation, whatever its name.
    fn inode_len(custody: &DimacsProofCustody) -> u64 {
        custody
            .descriptor
            .metadata()
            .expect("stat the proof inode")
            .len()
    }

    /// Reserve the proof and wrap the production sink in a DRAT writer.
    fn production_writer(proof: &ProofConfig) -> (ProofOutput, Arc<DimacsProofCustody>) {
        let file = create_configured_dimacs_proof_file(proof).expect("reserve proof");
        let custody = owned_dimacs_proof_custody(&proof.path).expect("proof custody");
        let sink = solver_proof_output_writer(file, proof).expect("production proof sink");
        (ProofOutput::drat_text(sink), custody)
    }

    /// 1000 unit additions, `1 0\n` each: 4000 bytes, well inside the 1 MiB
    /// buffer, so none has reached the file yet.
    const BUFFERED_STEPS: usize = 1000;
    const BUFFERED_BYTES: u64 = 4000;

    fn add_units(output: &mut ProofOutput, steps: usize) {
        let unit = [Literal::positive(Variable::new(0))];
        for _ in 0..steps {
            output.add(&unit, &[]).expect("proof step");
        }
    }

    #[test]
    fn an_abandoned_proof_writer_drops_its_buffer_instead_of_flushing_it() {
        let dir = tempfile::tempdir().expect("tempdir");
        let proof = required_drat_proof(dir.path());
        let (mut output, custody) = production_writer(&proof);
        add_units(&mut output, BUFFERED_STEPS);
        assert_eq!(inode_len(&custody), 0, "the steps are still buffered");

        assert!(custody.abandon());
        // More than the buffer holds: a live writer would have to write.
        add_units(&mut output, 400_000);
        assert_eq!(
            inode_len(&custody),
            0,
            "an abandoned writer writes nothing more"
        );
        output
            .flush()
            .expect("an abandoned writer's flush is a no-op");
        assert_eq!(
            inode_len(&custody),
            0,
            "an abandoned writer's flush writes nothing"
        );
        drop(output);
        assert_eq!(
            inode_len(&custody),
            0,
            "dropping an abandoned writer must discard its buffer, not flush it"
        );
        remove_owned_dimacs_proof(&proof.path).expect("settle the generation");
        assert!(!Path::new(&proof.path).exists());
    }

    /// A fast-publication writer records the SHA-256 of exactly the bytes it
    /// put in the file, the last buffered ones included.
    #[test]
    fn a_fast_publication_writer_records_the_digest_of_every_byte_it_wrote() {
        let dir = tempfile::tempdir().expect("tempdir");
        let proof = required_drat_proof(dir.path());
        let mut reservation = None;
        let file = create_owned_dimacs_proof_file_with_status(
            &proof.path,
            &mut reservation,
            DimacsPublicationInvalidation::Proof { binary: false },
            true,
        )
        .expect("reserve a fast-publication proof");
        let custody = owned_dimacs_proof_custody(&proof.path).expect("proof custody");
        let sink = solver_proof_output_writer(file, &proof).expect("production proof sink");
        let mut output = ProofOutput::drat_text(sink);
        add_units(&mut output, BUFFERED_STEPS);
        drop(output);

        let digest = custody
            .streamed_digest()
            .expect("a live fast writer records its digest");
        assert_eq!(digest.len, BUFFERED_BYTES);
        let mut bytes = Vec::new();
        (&custody.descriptor)
            .seek(SeekFrom::Start(0))
            .expect("rewind");
        (&custody.descriptor)
            .read_to_end(&mut bytes)
            .expect("read the proof");
        assert_eq!(bytes.len() as u64, BUFFERED_BYTES);
        assert_eq!(
            digest.sha256,
            sha256_digest(&bytes),
            "the digest is the file's"
        );
        remove_owned_dimacs_proof(&proof.path).expect("settle the generation");
    }

    /// An abandoned fast writer records nothing, and neither does a writer
    /// outside the fast path.
    #[test]
    fn only_a_live_fast_publication_writer_records_a_digest() {
        for fast in [true, false] {
            let dir = tempfile::tempdir().expect("tempdir");
            let proof = required_drat_proof(dir.path());
            let mut reservation = None;
            let file = create_owned_dimacs_proof_file_with_status(
                &proof.path,
                &mut reservation,
                DimacsPublicationInvalidation::Proof { binary: false },
                fast,
            )
            .expect("reserve proof");
            let custody = owned_dimacs_proof_custody(&proof.path).expect("proof custody");
            let mut output =
                ProofOutput::drat_text(solver_proof_output_writer(file, &proof).expect("sink"));
            add_units(&mut output, BUFFERED_STEPS);
            if fast {
                assert!(custody.abandon());
            }
            drop(output);
            assert!(custody.streamed.get().is_none(), "fast={fast}");
            remove_owned_dimacs_proof(&proof.path).expect("settle the generation");
        }
    }

    /// The control: the same writer, not abandoned, flushes its buffer when
    /// dropped. Without it the test above could pass on a writer that never
    /// wrote anything.
    #[test]
    fn a_live_proof_writer_still_flushes_its_buffer_when_dropped() {
        let dir = tempfile::tempdir().expect("tempdir");
        let proof = required_drat_proof(dir.path());
        let (mut output, custody) = production_writer(&proof);
        add_units(&mut output, BUFFERED_STEPS);
        assert_eq!(inode_len(&custody), 0, "the steps are still buffered");
        drop(output);
        assert_eq!(
            inode_len(&custody),
            BUFFERED_BYTES,
            "a live writer's drop flushes what it buffered"
        );
        remove_owned_dimacs_proof(&proof.path).expect("settle the generation");
    }
}
