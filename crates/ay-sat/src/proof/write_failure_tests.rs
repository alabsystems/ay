// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A full disk under every proof surface: the writers latch, and the first OS
//! error is kept so `ay solve` can name the cause (2026-09-12).

use super::*;
use crate::literal::Variable;
use std::io::{self, Write};

/// A sink on a full disk: every write fails with ENOSPC.
struct NoSpaceLeft;

impl Write for NoSpaceLeft {
    fn write(&mut self, _buf: &[u8]) -> io::Result<usize> {
        Err(io::Error::from_raw_os_error(libc::ENOSPC))
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// Every proof surface keeps the FIRST write failure a full disk produced,
/// with its OS error, after the format writer latches and goes silent: that is
/// what lets `ay solve` name the cause instead of panicking (2026-09-12).
#[test]
fn test_proof_writers_keep_the_first_enospc() {
    let x0 = Literal::positive(Variable(0));
    for (name, mut output) in [
        ("veripb", ProofOutput::veripb(NoSpaceLeft)),
        ("drat_text", ProofOutput::drat_text(NoSpaceLeft)),
        ("drat_binary", ProofOutput::drat_binary(NoSpaceLeft)),
        ("lrat_text", ProofOutput::lrat_text(NoSpaceLeft, 1)),
        ("lrat_binary", ProofOutput::lrat_binary(NoSpaceLeft, 1)),
    ] {
        let error = output
            .add(&[x0], &[])
            .expect_err("a proof write on a full disk fails");
        assert_eq!(error.raw_os_error(), Some(libc::ENOSPC), "{name}");
        assert!(output.has_io_error(), "{name}: the writer must latch");
        let kept = output.first_io_error().expect("the first error is kept");
        assert_eq!(kept.raw_os_error, Some(libc::ENOSPC), "{name}");
        assert!(
            kept.message.contains("No space left on device"),
            "{name}: {}",
            kept.message
        );
        assert!(
            output.add(&[x0.negated()], &[]).is_ok(),
            "{name}: later writes are silent no-ops after the latch"
        );
        assert_eq!(
            output.first_io_error().map(|kept| kept.raw_os_error),
            Some(Some(libc::ENOSPC)),
            "{name}: the kept error survives the latch"
        );
        assert!(output.into_inner().is_err(), "{name}");
    }
}

/// A sink that fails with each scripted error in turn, then with EIO.
struct ScriptedFailures(std::collections::VecDeque<io::Error>);

impl Write for ScriptedFailures {
    fn write(&mut self, _buf: &[u8]) -> io::Result<usize> {
        Err(self
            .0
            .pop_front()
            .unwrap_or_else(|| io::Error::from_raw_os_error(libc::EIO)))
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// `BoxedWriter` keeps the first real failure: `Interrupted` is not one, and
/// a later, different error never replaces it.
#[test]
fn test_boxed_writer_keeps_the_first_real_failure() {
    let mut sink = BoxedWriter::new(ScriptedFailures(
        [
            io::Error::from(io::ErrorKind::Interrupted),
            io::Error::from_raw_os_error(libc::ENOSPC),
        ]
        .into(),
    ));
    let kind = sink.write(b"a").map_err(|error| error.kind());
    assert_eq!(kind, Err(io::ErrorKind::Interrupted));
    assert!(sink.first_error().is_none(), "Interrupted is not a failure");
    let errno = |result: io::Result<usize>| result.map_err(|error| error.raw_os_error());
    assert_eq!(errno(sink.write(b"a")), Err(Some(libc::ENOSPC)));
    assert_eq!(errno(sink.write(b"a")), Err(Some(libc::EIO)));
    let kept = sink.first_error().expect("the first failure is kept");
    assert_eq!(kept.raw_os_error, Some(libc::ENOSPC));
    assert_eq!(kept.kind, io::ErrorKind::StorageFull);
}
