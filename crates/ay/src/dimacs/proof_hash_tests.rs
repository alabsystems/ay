// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The fast-publication proof hash runs off the thread that writes the proof
//! (2026-09-13); see `ProofHash`. The negative control for "off the thread" is
//! the inline fallback, which these tests force: then every byte is hashed on
//! the writing thread and its counter says so.

use super::*;

/// `len` bytes that differ from one position to the next.
fn pattern(len: usize, seed: usize) -> Vec<u8> {
    (0..len).map(|i| ((i * 31 + seed) % 251) as u8).collect()
}

fn sha256_of(pieces: &[Vec<u8>]) -> Sha256Digest {
    let mut hasher = Sha256::new();
    for piece in pieces {
        hasher.update(piece);
    }
    hasher.finalize().into()
}

fn pieces_of(sizes: &[usize]) -> Vec<Vec<u8>> {
    sizes
        .iter()
        .enumerate()
        .map(|(seed, &len)| pattern(len, seed))
        .collect()
}

/// Write sizes around every chunk boundary: empty, one byte short of a chunk
/// and one past it, exactly one chunk, several chunks in one write, and many
/// small writes.
fn boundary_cases() -> Vec<Vec<usize>> {
    let chunk = PROOF_HASH_CHUNK;
    vec![
        vec![],
        vec![0],
        vec![1],
        vec![chunk - 1, 1],
        vec![chunk],
        vec![chunk + 1],
        vec![chunk - 1, 2, chunk - 1],
        vec![3 * chunk + 5],
        vec![37; 100_000],
        vec![0, chunk, 0, 7, chunk * 2, 0],
    ]
}

#[test]
fn every_chunk_boundary_hashes_to_the_digest_of_the_bytes() {
    for fault in [ProofHashFault::None, ProofHashFault::NoWorker] {
        for sizes in boundary_cases() {
            let pieces = pieces_of(&sizes);
            arm_proof_hash_fault(fault);
            let mut hash = ProofHash::start();
            assert_eq!(
                matches!(hash, ProofHash::Inline(_)),
                fault == ProofHashFault::NoWorker
            );
            for piece in &pieces {
                hash.update(piece);
            }
            assert_eq!(
                hash.finish(),
                Some(sha256_of(&pieces)),
                "{fault:?}, write sizes {:?}",
                &sizes[..sizes.len().min(4)]
            );
        }
    }
}

/// Reserve a fast-publication generation and write `pieces` through the
/// production sink, dropping it so it records its digest.
fn write_through_the_sink(
    path: &str,
    pieces: &[Vec<u8>],
    fault: ProofHashFault,
) -> Arc<DimacsProofCustody> {
    let mut reservation = None;
    let file = create_owned_dimacs_proof_file_with_status(
        path,
        &mut reservation,
        DimacsPublicationInvalidation::Proof { binary: false },
        true,
    )
    .expect("reserve a fast-publication proof");
    let custody = owned_dimacs_proof_custody(path).expect("registered custody");
    assert!(custody.fast_publication);
    arm_proof_hash_fault(fault);
    let mut sink =
        ProofWriteBuffer::new(file, Arc::clone(&custody), ProofSpaceGuard::for_proof(path));
    for piece in pieces {
        sink.write_all(piece).expect("proof bytes");
    }
    sink.flush().expect("final flush");
    drop(sink);
    custody
}

/// The seal-latency follow-up (2026-09-13): the thread that writes the proof,
/// the solver's, copies its bytes and hashes none of them, and the digest is
/// still that of every byte written. Forcing the inline fallback shows the
/// counter would have seen them.
#[test]
fn the_writing_thread_copies_proof_bytes_but_never_hashes_them() {
    // 3.5 MB: small writes into the 1 MiB buffer, then one write past its
    // capacity, which the buffer passes straight through, then more small ones.
    let mut sizes = vec![41; 20_000];
    sizes.push(PROOF_OUTPUT_BUFFER_CAPACITY * 2 + 3);
    sizes.extend(std::iter::repeat_n(13, 40_000));
    let pieces = pieces_of(&sizes);
    let total: u64 = pieces.iter().map(|piece| piece.len() as u64).sum();
    for fault in [ProofHashFault::None, ProofHashFault::NoWorker] {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("proof.out");
        let path_text = path.to_str().expect("UTF-8 path");
        let before = proof_bytes_hashed_on_this_thread();
        let custody = write_through_the_sink(path_text, &pieces, fault);
        let hashed_here = proof_bytes_hashed_on_this_thread() - before;
        let digest = custody
            .streamed_digest()
            .expect("the writer recorded its digest");
        assert_eq!(digest.len, total);
        assert_eq!(digest.sha256, sha256_of(&pieces), "{fault:?}");
        match fault {
            ProofHashFault::None => {
                assert_eq!(hashed_here, 0, "the writing thread hashed proof bytes")
            }
            _ => assert_eq!(
                hashed_here, total,
                "the inline fallback hashes on the writing thread"
            ),
        }
        let published = seal_owned_dimacs_proof(path_text).expect("seal");
        assert_eq!(
            published.sha256,
            sha256_of(&[std::fs::read(&path).expect("read proof")])
        );
    }
}

/// A worker that dies leaves no digest, not a wrong one: the proof is still
/// written whole, and the seal falls back to reading it back once.
#[test]
fn a_proof_hash_worker_that_dies_records_no_digest() {
    let pieces = pieces_of(&[PROOF_HASH_CHUNK * 3 + 11]);
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.out");
    let path_text = path.to_str().expect("UTF-8 path");
    let custody =
        write_through_the_sink(path_text, &pieces, ProofHashFault::WorkerDiesBeforeChunk(1));
    assert_eq!(custody.streamed_digest(), None);
    let passes = whole_file_hash_passes();
    let published = seal_owned_dimacs_proof(path_text).expect("seal by reading the proof back");
    assert_eq!(whole_file_hash_passes() - passes, 1);
    assert_eq!(published.len, pieces[0].len() as u64);
    assert_eq!(published.sha256, sha256_of(&pieces));
    assert_eq!(std::fs::read(&path).expect("read proof"), pieces[0]);
}
