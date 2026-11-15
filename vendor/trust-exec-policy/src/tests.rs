use super::*;

#[test]
fn native_limit_range() {
    assert!(FootprintLimit::new(0).is_err());
    assert!(FootprintLimit::new(i32::MAX as u32 + 1).is_err());
    assert_eq!(FootprintLimit::new(64).unwrap().mib(), 64);
}

#[cfg(target_os = "macos")]
mod macos {
    use std::ffi::CString;
    use std::os::unix::ffi::OsStrExt;
    use std::time::{Duration, Instant};

    use super::*;

    #[test]
    fn bounded_payload() {
        let Some(mode) = std::env::var_os("TRUST_EXEC_POLICY_PAYLOAD") else {
            return;
        };
        if mode == "seal" || mode == "nested-seal" {
            seal_payload(mode == "nested-seal");
        }
        // Bounded even if the OS does not enforce the requested policy. Touch
        // private pages rather than counting a lazily mapped virtual allocation.
        let mut pages = vec![0_u8; 128 * 1024 * 1024];
        for page in pages.chunks_mut(4096) {
            page[0] = 1;
        }
        std::hint::black_box(&pages);
        std::thread::sleep(Duration::from_millis(250));
    }

    fn seal_payload(nested: bool) -> ! {
        assert!(!fork_denied(std::process::id()).unwrap());
        if nested {
            ExecutionSeal::NoFork.install_current().unwrap();
            assert!(fork_denied(std::process::id()).unwrap());
        }
        match ExecutionSeal::NoForkOrExec.install_current() {
            Ok(()) => {}
            Err(error) if nested => {
                eprintln!("native nested execution seal refused: {error}");
                std::process::exit(73);
            }
            Err(error) => panic!("direct execution seal refused: {error}"),
        }
        assert!(fork_denied(std::process::id()).unwrap());
        // SAFETY: the child path only calls _exit. Any unexpected positive fork
        // remains our original child and is positively reaped before failure.
        let child = unsafe { libc::fork() };
        if child == 0 {
            // SAFETY: no Rust runtime operation is performed in the fork child.
            unsafe { libc::_exit(99) };
        }
        if child > 0 {
            let mut status = 0;
            loop {
                // SAFETY: our original unreaped child, no concurrent waiter.
                let waited = unsafe { libc::waitpid(child, &mut status, 0) };
                if waited == child {
                    break;
                }
                if waited < 0 && io::Error::last_os_error().kind() != io::ErrorKind::Interrupted {
                    break;
                }
            }
            panic!("fixed seal allowed an actual fork");
        }
        assert_eq!(io::Error::last_os_error().raw_os_error(), Some(libc::EPERM));
        let arguments = [c"true".as_ptr(), std::ptr::null()];
        // SAFETY: static absolute image and complete argv. A broken policy only
        // replaces this owned test child; exit0 then differs from expected72.
        assert_eq!(
            unsafe { libc::execv(c"/usr/bin/true".as_ptr(), arguments.as_ptr()) },
            -1
        );
        assert_eq!(io::Error::last_os_error().raw_os_error(), Some(libc::EPERM));
        std::process::exit(72);
    }

    #[test]
    fn actual_direct_execution_seal() -> io::Result<()> {
        let status = run_payload(None, "seal")?;
        assert!(
            libc::WIFEXITED(status) && libc::WEXITSTATUS(status) == 72,
            "seal payload status {status}"
        );
        Ok(())
    }

    #[test]
    fn actual_nested_execution_seal_is_positive_or_refused() -> io::Result<()> {
        let status = run_payload(None, "nested-seal")?;
        assert!(libc::WIFEXITED(status));
        let code = libc::WEXITSTATUS(status);
        assert!(
            code == 72 || code == 73,
            "nested seal payload status {status}"
        );
        eprintln!(
            "native nested execution seal: {}",
            if code == 72 {
                "installed and enforced"
            } else {
                "explicitly refused"
            }
        );
        Ok(())
    }

    struct Attributes(libc::posix_spawnattr_t);

    impl Attributes {
        fn new() -> io::Result<Self> {
            let mut raw = std::mem::MaybeUninit::uninit();
            // SAFETY: writable native attribute storage; success initializes it.
            let result = unsafe { libc::posix_spawnattr_init(raw.as_mut_ptr()) };
            if result != 0 {
                return Err(io::Error::from_raw_os_error(result));
            }
            // SAFETY: the successful initializer filled this native object.
            Ok(Self(unsafe { raw.assume_init() }))
        }
    }

    impl Drop for Attributes {
        fn drop(&mut self) {
            // SAFETY: initialized, exclusively owned object destroyed exactly once.
            unsafe { libc::posix_spawnattr_destroy(&mut self.0) };
        }
    }

    fn run(limit: Option<FootprintLimit>) -> io::Result<i32> {
        run_payload(limit, "memory")
    }

    fn run_payload(limit: Option<FootprintLimit>, mode: &str) -> io::Result<i32> {
        retained_wait()?;
        let image = CString::new(std::env::current_exe()?.as_os_str().as_bytes())?;
        let args = [
            image.clone(),
            CString::new("--exact")?,
            CString::new("tests::macos::bounded_payload")?,
        ];
        let mut argv = args
            .iter()
            .map(|v| v.as_ptr().cast_mut())
            .collect::<Vec<_>>();
        argv.push(std::ptr::null_mut());
        let mut environment = std::env::vars_os()
            .filter(|(key, _)| key != "TRUST_EXEC_POLICY_PAYLOAD")
            .map(|(key, value)| {
                let mut bytes = key.as_bytes().to_vec();
                bytes.push(b'=');
                bytes.extend_from_slice(value.as_bytes());
                CString::new(bytes)
            })
            .collect::<Result<Vec<_>, _>>()?;
        environment.push(CString::new(format!("TRUST_EXEC_POLICY_PAYLOAD={mode}"))?);
        let mut envp = environment
            .iter()
            .map(|v| v.as_ptr().cast_mut())
            .collect::<Vec<_>>();
        envp.push(std::ptr::null_mut());
        let mut attributes = Attributes::new()?;
        if let Some(limit) = limit {
            // SAFETY: initialized exclusive object retained through native spawn.
            unsafe { limit.prepare(&mut attributes.0)? };
        }
        let mut pid = 0;
        // SAFETY: complete NUL-terminated argv/env arrays and image live through
        // the call; no file actions. A successful call creates our actual child.
        let result = unsafe {
            libc::posix_spawn(
                &mut pid,
                image.as_ptr(),
                std::ptr::null(),
                &attributes.0,
                argv.as_ptr(),
                envp.as_ptr(),
            )
        };
        if result != 0 {
            return Err(io::Error::from_raw_os_error(result));
        }
        let deadline = Instant::now() + Duration::from_secs(10);
        loop {
            let mut status = 0;
            // SAFETY: pid is our unreaped original child; WNOHANG retains its
            // identity until a positive wait. No observed PID is adopted here.
            let waited = unsafe { libc::waitpid(pid, &mut status, libc::WNOHANG) };
            if waited == pid {
                return Ok(status);
            }
            if waited < 0 {
                let error = io::Error::last_os_error();
                if error.kind() == io::ErrorKind::Interrupted {
                    continue;
                }
                // Lost wait ownership must never become numeric signal authority.
                return Err(error);
            }
            if Instant::now() >= deadline {
                // SAFETY: the preceding wait retained the unreaped child anchor;
                // default SIGCHLD is checked before either child is launched.
                unsafe { libc::kill(pid, libc::SIGKILL) };
                loop {
                    // SAFETY: same unreaped original child, no concurrent waiter.
                    let reaped = unsafe { libc::waitpid(pid, &mut status, 0) };
                    if reaped == pid {
                        break;
                    }
                    if reaped < 0 && io::Error::last_os_error().kind() != io::ErrorKind::Interrupted
                    {
                        break;
                    }
                }
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "bounded policy child deadline",
                ));
            }
            std::thread::sleep(Duration::from_millis(5));
        }
    }

    fn retained_wait() -> io::Result<()> {
        let mut disposition = std::mem::MaybeUninit::<libc::sigaction>::uninit();
        // SAFETY: query-only sigaction writes initialized native storage.
        if unsafe { libc::sigaction(libc::SIGCHLD, std::ptr::null(), disposition.as_mut_ptr()) }
            != 0
        {
            return Err(io::Error::last_os_error());
        }
        // SAFETY: successful query initialized the complete object.
        let disposition = unsafe { disposition.assume_init() };
        if disposition.sa_sigaction != libc::SIG_DFL
            || disposition.sa_flags & libc::SA_NOCLDWAIT != 0
        {
            return Err(io::Error::other(
                "test requires retained original-child wait ownership",
            ));
        }
        Ok(())
    }

    #[test]
    fn actual_final_exec_footprint_policy() -> io::Result<()> {
        let baseline = run(None)?;
        assert!(libc::WIFEXITED(baseline) && libc::WEXITSTATUS(baseline) == 0);
        let limited = run(Some(FootprintLimit::new(32)?))?;
        assert!(
            libc::WIFSIGNALED(limited),
            "fatal footprint policy not enforced: {limited}"
        );
        Ok(())
    }
}
