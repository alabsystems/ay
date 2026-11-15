//! Policy preparation for a native final exec, shared by retained hosts and clients.
//!
//! This leaf neither launches a process nor grants resources. Successful attribute
//! preparation does not prove that any child executed with the policy. The launch
//! owner must retain the actual child, identify the final image, and preserve the
//! policy across its lifetime; a subsequent exec requires separate qualification.

use std::io;
use std::num::NonZeroU32;

#[cfg(target_os = "macos")]
mod seal;
#[cfg(target_os = "macos")]
pub use seal::{ExecutionSeal, fork_denied};

/// Apple's `spawn.h` defines the initialized attribute handle as `void *`.
/// Its storage is owned by the native initializer, not by this library.
#[cfg(target_os = "macos")]
pub type SpawnAttributes = *mut std::ffi::c_void;

/// Equal active/inactive fatal physical-footprint limits, in whole MiB.
/// This is not an RSS or address-space limit.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FootprintLimit(NonZeroU32);

impl FootprintLimit {
    pub fn new(mib: u32) -> io::Result<Self> {
        let value = NonZeroU32::new(mib).filter(|v| v.get() <= i32::MAX as u32);
        value.map(Self).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                "footprint MiB outside native range",
            )
        })
    }

    pub fn mib(self) -> u32 {
        self.0.get()
    }

    /// Prepare Apple's active and inactive fatal-footprint spawn attributes.
    /// Does not set SETEXEC, suspend flags, signal policy, or process grouping.
    ///
    /// # Safety
    /// `attributes` must reference an initialized, exclusively borrowed native
    /// `posix_spawnattr_t` for the complete call. The caller owns its destruction.
    #[cfg(target_os = "macos")]
    pub unsafe fn prepare(self, attributes: &mut SpawnAttributes) -> io::Result<()> {
        type Setter = unsafe extern "C" fn(
            *mut SpawnAttributes,
            libc::c_short,
            libc::c_int,
            libc::c_int,
            libc::c_int,
        ) -> libc::c_int;
        // SAFETY: a static NUL-terminated symbol name and the process-global dyld
        // handle; resolving a symbol does not call it or alter spawn attributes.
        let symbol = unsafe {
            libc::dlsym(
                libc::RTLD_DEFAULT,
                c"posix_spawnattr_setjetsam_ext".as_ptr(),
            )
        };
        if symbol.is_null() {
            return Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "native footprint policy unavailable",
            ));
        }
        // SAFETY: Apple's libsyscall declares exactly this setter ABI. No guessed
        // attribute layout is read or written here; the OS setter owns it.
        let setter: Setter = unsafe { std::mem::transmute(symbol) };
        let mib = self.mib() as libc::c_int;
        // SAFETY: caller guarantees a live exclusively owned initialized object;
        // the validated positive MiB values fit the ABI. 0x04/0x08 are Apple's
        // active/inactive fatal flags; the setter supplies JETSAM_SET internally.
        let result = unsafe { setter(attributes, 0x04 | 0x08, 0, mib, mib) };
        if result == 0 {
            Ok(())
        } else {
            Err(io::Error::from_raw_os_error(result))
        }
    }
}

#[cfg(test)]
mod tests;
