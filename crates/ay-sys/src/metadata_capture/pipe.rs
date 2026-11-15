// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded native pipe drainage. Every reader is cancelled and joined; an
//! inherited writer outside the owned group cannot strand a detached thread.
use std::io::{self, Read};
use std::sync::{
    atomic::{AtomicBool, Ordering},
    mpsc, Arc,
};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

pub const DEFAULT_OUTPUT_BYTES: usize = 64 * 1024;

struct Drain {
    bytes: Vec<u8>,
    truncated: bool,
    unreadable: bool,
}

pub struct PipeCaptureEvidence {
    pub text: String,
    pub incomplete: bool,
    pub error: Option<String>,
}

pub struct BoundedPipeCapture {
    receiver: mpsc::Receiver<Drain>,
    cancel: Arc<AtomicBool>,
    exceeded: Arc<AtomicBool>,
    reader: Option<JoinHandle<()>>,
}

impl BoundedPipeCapture {
    #[cfg(unix)]
    pub fn start(reader: impl Into<std::os::fd::OwnedFd>) -> io::Result<Self> {
        Self::with_limit(reader, DEFAULT_OUTPUT_BYTES)
    }

    /// Takes an owned native child pipe. Nonblocking mode applies to this read
    /// endpoint; producer writes retain their ordinary blocking semantics.
    #[cfg(unix)]
    pub fn with_limit(reader: impl Into<std::os::fd::OwnedFd>, limit: usize) -> io::Result<Self> {
        use std::os::{fd::AsRawFd as _, unix::fs::FileTypeExt as _};
        let mut reader = std::fs::File::from(reader.into());
        let kind = reader.metadata()?.file_type();
        if !kind.is_fifo() && !kind.is_socket() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "metadata reader must be an owned native pipe or socket",
            ));
        }
        if limit == 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "metadata output limit must be positive",
            ));
        }
        let fd = reader.as_raw_fd();
        // SAFETY: reader retains this valid native descriptor throughout both
        // integer-only fcntl calls. No pointer or borrowed descriptor escapes.
        let result = unsafe {
            let flags = libc::fcntl(fd, libc::F_GETFL);
            if flags < 0 {
                -1
            } else {
                libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK)
            }
        };
        if result < 0 {
            return Err(io::Error::last_os_error());
        }
        let mut bytes = Vec::new();
        bytes.try_reserve_exact(limit).map_err(|error| {
            io::Error::other(format!("metadata output reservation refused: {error}"))
        })?;
        let (sender, receiver) = mpsc::channel();
        let cancel = Arc::new(AtomicBool::new(false));
        let exceeded = Arc::new(AtomicBool::new(false));
        let reader_cancel = Arc::clone(&cancel);
        let reader_exceeded = Arc::clone(&exceeded);
        let handle = std::thread::Builder::new()
            .name("ay-metadata-pipe".into())
            .spawn(move || {
                let mut chunk = [0u8; 8192];
                let mut truncated = false;
                let mut unreadable = false;
                loop {
                    if reader_cancel.load(Ordering::Acquire) {
                        unreadable = true;
                        break;
                    }
                    match reader.read(&mut chunk) {
                        Ok(0) => break,
                        Ok(count) => {
                            let retained = count.min(limit.saturating_sub(bytes.len()));
                            bytes.extend_from_slice(&chunk[..retained]);
                            if retained < count {
                                truncated = true;
                                reader_exceeded.store(true, Ordering::Release);
                            }
                        }
                        Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
                        Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                            std::thread::sleep(Duration::from_millis(5))
                        }
                        Err(_) => {
                            unreadable = true;
                            break;
                        }
                    }
                }
                let _ = sender.send(Drain {
                    bytes,
                    truncated,
                    unreadable,
                });
            })?;
        Ok(Self {
            receiver,
            cancel,
            exceeded,
            reader: Some(handle),
        })
    }

    #[cfg(not(unix))]
    pub fn start<R: Read + Send + 'static>(_reader: R) -> io::Result<Self> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "bounded native metadata pipe capture unavailable",
        ))
    }

    pub fn limit_breached(&self) -> bool {
        self.exceeded.load(Ordering::Acquire)
    }

    fn receive_until(&mut self, deadline: Instant) -> io::Result<Drain> {
        let remaining = deadline.checked_duration_since(Instant::now());
        let result = remaining
            .ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::TimedOut,
                    "metadata capture deadline exceeded",
                )
            })
            .and_then(|remaining| {
                self.receiver.recv_timeout(remaining).map_err(|error| {
                    io::Error::new(
                        if matches!(error, mpsc::RecvTimeoutError::Timeout) {
                            io::ErrorKind::TimedOut
                        } else {
                            io::ErrorKind::BrokenPipe
                        },
                        format!("metadata pipe capture did not finish: {error}"),
                    )
                })
            });
        if result.is_err() {
            self.cancel.store(true, Ordering::Release);
        }
        if let Some(reader) = self.reader.take() {
            reader
                .join()
                .map_err(|_| io::Error::other("metadata pipe reader panicked"))?;
        }
        let drained = result?;
        if Instant::now() >= deadline {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "metadata capture completed after its original deadline",
            ));
        }
        Ok(drained)
    }

    pub fn finish_bytes_until(
        mut self,
        label: &str,
        stream: &str,
        deadline: Instant,
    ) -> io::Result<Vec<u8>> {
        let drained = self.receive_until(deadline)?;
        if drained.truncated || drained.unreadable {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("{label}: {stream} exceeded its metadata capture limit or was unreadable"),
            ));
        }
        Ok(drained.bytes)
    }

    pub fn finish(self, label: &str, stream: &str) -> io::Result<String> {
        // Existing benchmark callers have a separate post-exit drain allowance.
        // Metadata execution uses finish_bytes_until with its ORIGINAL deadline.
        String::from_utf8(self.finish_bytes_until(
            label,
            stream,
            Instant::now() + Duration::from_secs(5),
        )?)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))
    }

    /// Failure evidence only. Incomplete bytes never qualify a solver answer.
    pub fn finish_evidence(mut self) -> PipeCaptureEvidence {
        match self.receive_until(Instant::now() + Duration::from_secs(5)) {
            Ok(drained) => {
                let invalid_utf8 = std::str::from_utf8(&drained.bytes).is_err();
                let incomplete = drained.truncated || drained.unreadable || invalid_utf8;
                PipeCaptureEvidence {
                    text: String::from_utf8_lossy(&drained.bytes).into_owned(),
                    incomplete,
                    error: incomplete.then(|| {
                        format!(
                            "capture truncated={}, unreadable={}, invalid_utf8={invalid_utf8}",
                            drained.truncated, drained.unreadable
                        )
                    }),
                }
            }
            Err(error) => PipeCaptureEvidence {
                text: String::new(),
                incomplete: true,
                error: Some(error.to_string()),
            },
        }
    }
}

impl Drop for BoundedPipeCapture {
    fn drop(&mut self) {
        self.cancel.store(true, Ordering::Release);
        if let Some(reader) = self.reader.take() {
            let _ = reader.join();
        }
    }
}
