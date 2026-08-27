// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn proof_output_writer(file: File) -> BufWriter<File> {
    BufWriter::with_capacity(PROOF_OUTPUT_BUFFER_CAPACITY, file)
}

enum SolverDimacsProofWriter {
    Required(BufWriter<File>),
    Optional {
        writer: BufWriter<File>,
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
                #[cfg(test)]
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
    let writer = proof_output_writer(file);
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
