// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `cmd_pb` to preserve private item DefPaths.

fn prepare_pb_process(proof_tap_legacy: bool) -> std::time::Instant {
    if proof_tap_legacy {
        PROOF_TAP_LEGACY.store(true, Ordering::Relaxed);
    }
    apply_memory_limit();
    std::time::Instant::now()
}

fn proof_temp_path(proof_path: &Path) -> PathBuf {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|duration| duration.as_nanos())
        .unwrap_or(0);
    let mut temp_path = proof_path.to_path_buf();
    let temp_extension = proof_path
        .extension()
        .map(|extension| {
            format!(
                "{}.tmp-{}-{nonce}",
                extension.to_string_lossy(),
                std::process::id()
            )
        })
        .unwrap_or_else(|| format!("tmp-{}-{nonce}", std::process::id()));
    temp_path.set_extension(temp_extension);
    temp_path
}
