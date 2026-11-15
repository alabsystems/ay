// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked decoding for the existing best-effort memory observation API.
//! Unknown/malformed samples use that API's explicit fallback, not saturation.

#[cfg(any(target_os = "linux", test))]
pub(super) fn linux_available_bytes(contents: &str) -> Option<usize> {
    let mut available = None;
    for line in contents.lines() {
        let Some((key, value)) = line.split_once(':') else {
            continue;
        };
        if key != "MemAvailable" {
            continue;
        }
        if available.is_some() {
            return None;
        }
        let mut fields = value.split_whitespace();
        let number = fields.next()?;
        if !number.bytes().all(|byte| byte.is_ascii_digit())
            || fields.next()? != "kB"
            || fields.next().is_some()
        {
            return None;
        }
        let kib = number.parse::<u64>().ok()?;
        available = Some(usize::try_from(kib.checked_mul(1024)?).ok()?);
    }
    available
}

#[cfg(any(target_os = "macos", test))]
pub(super) fn mac_available_bytes(
    words: &[u32],
    returned_count: u32,
    page_size: Option<u64>,
) -> Option<usize> {
    let returned_count = usize::try_from(returned_count).ok()?;
    if returned_count < 3 || returned_count > words.len() {
        return None;
    }
    // system_available_bytes historically uses 4096 when sysconf fails.
    // Retain that compatibility policy without claiming a fresh page-size read.
    let page_size = page_size.unwrap_or(4096);
    if page_size == 0 {
        return None;
    }
    let pages = u64::from(words[0]).checked_add(u64::from(words[2]))?;
    usize::try_from(pages.checked_mul(page_size)?).ok()
}

#[cfg(test)]
mod tests;
