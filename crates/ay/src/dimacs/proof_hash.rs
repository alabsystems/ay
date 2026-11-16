// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Bytes per chunk the proof hash worker takes, and how many full chunks may
/// wait for it. The queue bounds the proof bytes held in memory and what the
/// seal waits for at the end: a few milliseconds of hashing.
const PROOF_HASH_CHUNK: usize = PROOF_OUTPUT_BUFFER_CAPACITY;
const PROOF_HASH_QUEUE: usize = 4;

/// The SHA-256 of a fast-publication proof, taken off the thread that writes
/// it (2026-09-13). Hashing on the solver thread cost 166e1e5a's 2.73 GB proof
/// about 5 s of search at the portable SHA-256's 0.55 GB/s.
///
/// The writer copies the bytes each `write(2)` accepted into chunks and hands
/// full chunks, in order, to one worker thread through a bounded queue. The
/// worker hashes them and hands the buffers back for reuse, so the solver
/// thread pays a copy instead of the hash. If the worker cannot start, the
/// bytes are hashed inline as before. If it dies, no digest is recorded and
/// the seal reads the proof back once.
enum ProofHash {
    Inline(Sha256),
    Worker(ProofHashWorker),
}

impl ProofHash {
    fn start() -> Self {
        match ProofHashWorker::spawn() {
            Some(worker) => Self::Worker(worker),
            None => Self::Inline(Sha256::new()),
        }
    }

    fn update(&mut self, bytes: &[u8]) {
        match self {
            Self::Inline(hasher) => {
                note_proof_bytes_hashed(bytes.len());
                hasher.update(bytes);
            }
            Self::Worker(worker) => worker.update(bytes),
        }
    }

    /// The digest of every byte passed to `update`, or `None` if the worker
    /// failed. Waits for the worker to hash what is still queued.
    fn finish(self) -> Option<Sha256Digest> {
        match self {
            Self::Inline(hasher) => Some(hasher.finalize().into()),
            Self::Worker(worker) => worker.finish(),
        }
    }
}

struct ProofHashWorker {
    /// Accepted bytes not yet handed to the worker; at most one chunk.
    pending: Vec<u8>,
    /// `None` once closed.
    chunks: Option<std::sync::mpsc::SyncSender<Vec<u8>>>,
    /// Emptied chunks the worker hands back.
    spares: std::sync::mpsc::Receiver<Vec<u8>>,
    /// `None` once joined.
    worker: Option<std::thread::JoinHandle<Sha256Digest>>,
    /// A chunk could not be handed over: the worker is gone.
    failed: bool,
}

impl ProofHashWorker {
    fn spawn() -> Option<Self> {
        #[cfg(test)]
        let fault = PROOF_HASH_FAULT.with(|fault| fault.replace(ProofHashFault::None));
        #[cfg(test)]
        if fault == ProofHashFault::NoWorker {
            return None;
        }
        let (chunks, queue) = std::sync::mpsc::sync_channel::<Vec<u8>>(PROOF_HASH_QUEUE);
        let (spare, spares) = std::sync::mpsc::channel::<Vec<u8>>();
        let worker = std::thread::Builder::new()
            .name("ay-proof-hash".to_owned())
            .spawn(move || {
                let mut hasher = Sha256::new();
                #[cfg(test)]
                let mut index = 0;
                #[cfg_attr(
                    test,
                    expect(
                        clippy::explicit_counter_loop,
                        reason = "the index selects a test fault; production hashing must not maintain a counter"
                    )
                )]
                for mut chunk in queue {
                    #[cfg(test)]
                    {
                        if fault == ProofHashFault::WorkerDiesBeforeChunk(index) {
                            std::panic::resume_unwind(Box::new(
                                "proof hash worker fault injected by a test",
                            ));
                        }
                        index += 1;
                    }
                    note_proof_bytes_hashed(chunk.len());
                    hasher.update(&chunk);
                    chunk.clear();
                    // The writer may be gone already; the chunk is then freed.
                    let _ = spare.send(chunk);
                }
                hasher.finalize().into()
            })
            .ok()?;
        Some(Self {
            pending: Vec::with_capacity(PROOF_HASH_CHUNK),
            chunks: Some(chunks),
            spares,
            worker: Some(worker),
            failed: false,
        })
    }

    fn update(&mut self, mut bytes: &[u8]) {
        while !bytes.is_empty() && !self.failed {
            let take = (PROOF_HASH_CHUNK - self.pending.len()).min(bytes.len());
            self.pending.extend_from_slice(&bytes[..take]);
            bytes = &bytes[take..];
            if self.pending.len() == PROOF_HASH_CHUNK {
                self.hand_over();
            }
        }
    }

    /// Queue the pending chunk, blocking while the queue is full.
    fn hand_over(&mut self) {
        let next = self
            .spares
            .try_recv()
            .unwrap_or_else(|_| Vec::with_capacity(PROOF_HASH_CHUNK));
        let full = std::mem::replace(&mut self.pending, next);
        let queued = self
            .chunks
            .as_ref()
            .is_some_and(|chunks| chunks.send(full).is_ok());
        self.failed |= !queued;
    }

    fn finish(mut self) -> Option<Sha256Digest> {
        if !self.pending.is_empty() && !self.failed {
            self.hand_over();
        }
        drop(self.chunks.take());
        let digest = self.worker.take()?.join().ok()?;
        (!self.failed).then_some(digest)
    }
}

impl Drop for ProofHashWorker {
    /// An abandoned or failed writer: close the queue and wait for the worker,
    /// which hashes at most the few chunks still queued.
    fn drop(&mut self) {
        drop(self.chunks.take());
        if let Some(worker) = self.worker.take() {
            let _ = worker.join();
        }
    }
}

/// A fault a test arms for the next proof hash its thread starts.
#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProofHashFault {
    None,
    /// The worker thread cannot be started.
    NoWorker,
    /// The worker dies before it hashes the chunk with this index.
    WorkerDiesBeforeChunk(usize),
}

#[cfg(test)]
thread_local! {
    static PROOF_HASH_FAULT: std::cell::Cell<ProofHashFault> =
        const { std::cell::Cell::new(ProofHashFault::None) };
    static PROOF_BYTES_HASHED_ON_THIS_THREAD: std::cell::Cell<u64> =
        const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn arm_proof_hash_fault(fault: ProofHashFault) {
    PROOF_HASH_FAULT.with(|armed| armed.set(fault));
}

/// Proof bytes this thread has hashed, inline or as a worker.
#[cfg(test)]
fn proof_bytes_hashed_on_this_thread() -> u64 {
    PROOF_BYTES_HASHED_ON_THIS_THREAD.with(std::cell::Cell::get)
}

#[inline]
fn note_proof_bytes_hashed(_len: usize) {
    #[cfg(test)]
    PROOF_BYTES_HASHED_ON_THIS_THREAD.with(|hashed| hashed.set(hashed.get() + _len as u64));
}
