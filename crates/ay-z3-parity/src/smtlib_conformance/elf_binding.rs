// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Read-only ELF64 binding checks for the Linux stock C/C++ consumers.
//! No loader or executable inspection helper runs untrusted binaries here.

use super::*;

const MAX_ELF_BYTES: u64 = 256 * 1024 * 1024;
const MAX_DYNAMIC_BYTES: u64 = 64 * 1024;
const MAX_STRING_BYTES: u64 = 16 * 1024 * 1024;

#[derive(Clone, Debug)]
struct Dynamic {
    kind: u16,
    machine: u16,
    needed: Vec<String>,
    soname: Option<String>,
    rpath: Option<String>,
    runpath: Option<String>,
}

#[derive(Clone, Copy)]
struct Segment {
    offset: u64,
    address: u64,
    size: u64,
}

fn bytes(data: &[u8], offset: u64, length: u64) -> Result<&[u8], String> {
    let end = offset.checked_add(length).ok_or("ELF offset overflow")?;
    let start = usize::try_from(offset).map_err(|_| "ELF offset exceeds host size")?;
    let end = usize::try_from(end).map_err(|_| "ELF range exceeds host size")?;
    data.get(start..end)
        .ok_or_else(|| "ELF range exceeds file".to_string())
}

fn word16(data: &[u8], offset: u64) -> Result<u16, String> {
    Ok(u16::from_le_bytes(
        bytes(data, offset, 2)?.try_into().map_err(|_| "ELF u16")?,
    ))
}

fn word32(data: &[u8], offset: u64) -> Result<u32, String> {
    Ok(u32::from_le_bytes(
        bytes(data, offset, 4)?.try_into().map_err(|_| "ELF u32")?,
    ))
}

fn word64(data: &[u8], offset: u64) -> Result<u64, String> {
    Ok(u64::from_le_bytes(
        bytes(data, offset, 8)?.try_into().map_err(|_| "ELF u64")?,
    ))
}

fn one(slot: &mut Option<u64>, value: u64) -> Result<(), String> {
    if slot.replace(value).is_some() {
        return Err("duplicate singleton ELF dynamic tag".to_string());
    }
    Ok(())
}

fn string(table: &[u8], offset: u64) -> Result<String, String> {
    let offset = usize::try_from(offset).map_err(|_| "ELF string offset exceeds host size")?;
    let rest = table
        .get(offset..)
        .ok_or("ELF string offset exceeds table")?;
    let end = rest
        .iter()
        .position(|byte| *byte == 0)
        .ok_or("unterminated ELF string")?;
    let text = std::str::from_utf8(&rest[..end]).map_err(|_| "ELF loader string is not UTF-8")?;
    if text.is_empty() || text.chars().any(char::is_control) {
        return Err("empty or control-bearing ELF loader string".to_string());
    }
    Ok(text.to_string())
}

fn parse(data: &[u8]) -> Result<Dynamic, String> {
    if bytes(data, 0, 4)? != b"\x7fELF"
        || bytes(data, 4, 3)? != [2, 1, 1]
        || !matches!(bytes(data, 7, 1)?[0], 0 | 3)
        || word32(data, 20)? != 1
    {
        return Err("stock consumer requires little-endian Linux ELF64".to_string());
    }
    let kind = word16(data, 16)?;
    let machine = word16(data, 18)?;
    if !matches!(kind, 2 | 3)
        || !matches!(machine, 62 | 183)
        || word16(data, 52)? != 64
        || word16(data, 54)? != 56
    {
        return Err("unsupported ELF type, machine or header layout".to_string());
    }
    let count = u64::from(word16(data, 56)?);
    if count == 0 || count > 512 {
        return Err("unsupported ELF program-header population".to_string());
    }
    let start = word64(data, 32)?;
    let mut loads = Vec::new();
    let mut dynamic = None;
    for index in 0..count {
        let offset = start
            .checked_add(index * 56)
            .ok_or("ELF program-header overflow")?;
        let header = bytes(data, offset, 56)?;
        let segment = Segment {
            offset: word64(header, 8)?,
            address: word64(header, 16)?,
            size: word64(header, 32)?,
        };
        if segment.size > word64(header, 40)? {
            return Err("ELF segment file size exceeds memory size".to_string());
        }
        bytes(data, segment.offset, segment.size)?;
        match word32(header, 0)? {
            1 => loads.push(segment),
            2 => {
                if dynamic.replace(segment).is_some() {
                    return Err("multiple ELF dynamic segments".to_string());
                }
            }
            _ => {}
        }
    }
    let dynamic = dynamic.ok_or("ELF has no dynamic segment")?;
    if dynamic.size == 0 || dynamic.size > MAX_DYNAMIC_BYTES || dynamic.size % 16 != 0 {
        return Err("invalid or excessive ELF dynamic segment".to_string());
    }
    let mut strtab = None;
    let mut strsz = None;
    let mut soname = None;
    let mut rpath = None;
    let mut runpath = None;
    let mut needed = Vec::new();
    let mut terminated = false;
    for entry in bytes(data, dynamic.offset, dynamic.size)?.chunks_exact(16) {
        let tag = word64(entry, 0)?;
        let value = word64(entry, 8)?;
        match tag {
            0 => {
                terminated = true;
                break;
            }
            1 => needed.push(value),
            5 => one(&mut strtab, value)?,
            10 => one(&mut strsz, value)?,
            14 => one(&mut soname, value)?,
            15 => one(&mut rpath, value)?,
            29 => one(&mut runpath, value)?,
            _ => {}
        }
    }
    if !terminated {
        return Err("unterminated ELF dynamic segment".to_string());
    }
    let address = strtab.ok_or("ELF has no dynamic string table")?;
    let size = strsz.ok_or("ELF has no dynamic string-table size")?;
    if size == 0 || size > MAX_STRING_BYTES {
        return Err("excessive ELF dynamic string table".to_string());
    }
    let tables = loads
        .iter()
        .filter_map(|segment| {
            let relative = address.checked_sub(segment.address)?;
            (relative.checked_add(size)? <= segment.size).then_some((segment, relative))
        })
        .collect::<Vec<_>>();
    let [(segment, relative)] = tables.as_slice() else {
        return Err("ELF dynamic string table has no unique file-backed mapping".to_string());
    };
    let offset = segment
        .offset
        .checked_add(*relative)
        .ok_or("ELF string-table offset overflow")?;
    let table = bytes(data, offset, size)?;
    Ok(Dynamic {
        kind,
        machine,
        needed: needed
            .into_iter()
            .map(|offset| string(table, offset))
            .collect::<Result<_, _>>()?,
        soname: soname.map(|offset| string(table, offset)).transpose()?,
        rpath: rpath.map(|offset| string(table, offset)).transpose()?,
        runpath: runpath.map(|offset| string(table, offset)).transpose()?,
    })
}

fn validate_binding(binary: &Dynamic, library: &Dynamic, selected: &Path) -> Result<(), String> {
    if library.kind != 3 || binary.machine != library.machine {
        return Err("ELF consumer/provider type or machine mismatch".to_string());
    }
    let selected_text = selected.to_str().ok_or("ELF provider path is not UTF-8")?;
    if !selected.is_absolute() {
        return Err("ELF provider path is not absolute".to_string());
    }
    let basename = selected
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or("ELF provider has no filename")?;
    let install_name = library.soname.as_deref().unwrap_or(basename);
    let matches = binary
        .needed
        .iter()
        .filter(|needed| needed.as_str() == selected_text || needed.as_str() == install_name)
        .collect::<Vec<_>>();
    let [dependency] = matches.as_slice() else {
        return Err(
            "ELF consumer must require exactly one authenticated provider dependency".to_string(),
        );
    };
    // Basenames detect colliding foreign dependencies only; they never grant
    // acceptance to a path that was not selected above by exact identity.
    let install_basename = Path::new(install_name).file_name();
    if binary.needed.iter().any(|needed| {
        needed.as_str() != dependency.as_str()
            && (Path::new(needed).file_name() == Some(std::ffi::OsStr::new(basename))
                || Path::new(needed).file_name() == install_basename)
    }) {
        return Err("ELF consumer also requires a colliding foreign provider".to_string());
    }
    if dependency.as_str() == selected_text {
        return Ok(());
    }
    if dependency.as_str() != basename || install_name != basename {
        return Err("ELF SONAME cannot resolve to the authenticated staged filename".to_string());
    }
    if binary.runpath.is_some() {
        return Err("ELF provider binding must not rely on DT_RUNPATH".to_string());
    }
    let rpath = binary
        .rpath
        .as_deref()
        .ok_or("ELF provider binding has no private DT_RPATH")?;
    let paths = rpath.split(':').collect::<Vec<_>>();
    let directory = selected.parent().ok_or("ELF provider has no parent")?;
    if paths.first().map(|path| Path::new(path)) != Some(directory)
        || paths
            .iter()
            .any(|path| path.is_empty() || !Path::new(path).is_absolute())
    {
        return Err(
            "ELF provider must resolve through the first absolute private DT_RPATH entry"
                .to_string(),
        );
    }
    Ok(())
}

pub(super) fn validate(binary: &Path, library: &Path) -> Result<(), String> {
    let library =
        fs::canonicalize(library).map_err(|error| format!("resolve ELF provider: {error}"))?;
    let provider = parse(&read_bounded_bytes(
        &library,
        MAX_ELF_BYTES,
        "ELF provider",
        true,
    )?)?;
    let consumer = parse(&read_bounded_bytes(
        binary,
        MAX_ELF_BYTES,
        "ELF consumer",
        true,
    )?)?;
    validate_binding(&consumer, &provider, &library)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn image(
        kind: u16,
        soname: Option<&str>,
        needed: &[&str],
        rpath: Option<&str>,
        runpath: Option<&str>,
    ) -> Vec<u8> {
        let mut data = vec![0u8; 2048];
        data[..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
        data[16..18].copy_from_slice(&kind.to_le_bytes());
        data[18..20].copy_from_slice(&62u16.to_le_bytes());
        data[20..24].copy_from_slice(&1u32.to_le_bytes());
        data[32..40].copy_from_slice(&64u64.to_le_bytes());
        data[52..54].copy_from_slice(&64u16.to_le_bytes());
        data[54..56].copy_from_slice(&56u16.to_le_bytes());
        data[56..58].copy_from_slice(&2u16.to_le_bytes());
        let mut table = vec![0];
        let mut entries = Vec::<(u64, u64)>::new();
        for (tag, value) in needed
            .iter()
            .map(|value| (1, *value))
            .chain(soname.map(|value| (14, value)))
            .chain(rpath.map(|value| (15, value)))
            .chain(runpath.map(|value| (29, value)))
        {
            entries.push((tag, table.len() as u64));
            table.extend_from_slice(value.as_bytes());
            table.push(0);
        }
        entries.extend([(5, 0x400000 + 0x300), (10, table.len() as u64), (0, 0)]);
        for (index, (tag, value)) in entries.iter().enumerate() {
            let offset = 0x100 + index * 16;
            data[offset..offset + 8].copy_from_slice(&tag.to_le_bytes());
            data[offset + 8..offset + 16].copy_from_slice(&value.to_le_bytes());
        }
        data[0x300..0x300 + table.len()].copy_from_slice(&table);
        for (offset, kind, file_offset, address, size) in [
            (64usize, 1u32, 0u64, 0x400000u64, data.len() as u64),
            (120, 2, 0x100, 0x400100, (entries.len() * 16) as u64),
        ] {
            data[offset..offset + 4].copy_from_slice(&kind.to_le_bytes());
            data[offset + 8..offset + 16].copy_from_slice(&file_offset.to_le_bytes());
            data[offset + 16..offset + 24].copy_from_slice(&address.to_le_bytes());
            data[offset + 32..offset + 40].copy_from_slice(&size.to_le_bytes());
            data[offset + 40..offset + 48].copy_from_slice(&size.to_le_bytes());
        }
        data
    }

    #[test]
    fn private_rpath_and_exact_absolute_dependencies_bind_the_selected_bytes() {
        let provider = parse(&image(3, Some("libay_ffi.so"), &[], None, None)).unwrap();
        let selected = Path::new("/private/with spaces/libay_ffi.so");
        let relative = parse(&image(
            3,
            None,
            &["libay_ffi.so", "libc.so.6"],
            Some("/private/with spaces:/usr/lib"),
            None,
        ))
        .unwrap();
        validate_binding(&relative, &provider, selected).unwrap();
        let absolute = parse(&image(
            2,
            None,
            &["/private/with spaces/libay_ffi.so"],
            None,
            None,
        ))
        .unwrap();
        validate_binding(&absolute, &provider, selected).unwrap();
    }

    #[test]
    fn soname_mismatch_runpath_and_ambient_search_never_pass() {
        let selected = Path::new("/private/libay_ffi-renamed.so");
        let provider = parse(&image(3, Some("libay_ffi.so"), &[], None, None)).unwrap();
        let mismatch = parse(&image(3, None, &["libay_ffi.so"], Some("/private"), None)).unwrap();
        assert!(validate_binding(&mismatch, &provider, selected).is_err());
        let selected = Path::new("/private/libay_ffi.so");
        for (needed, rpath, runpath) in [
            (vec!["libay_ffi.so"], None, Some("/private")),
            (vec!["libay_ffi.so"], Some("/usr/lib:/private"), None),
            (vec!["libay_ffi.so"], Some("/private:"), None),
            (vec!["libay_ffi.so", "libay_ffi.so"], Some("/private"), None),
            (vec!["/foreign/libay_ffi.so"], Some("/private"), None),
            (
                vec!["/private/libay_ffi.so", "/foreign/libay_ffi.so"],
                None,
                None,
            ),
        ] {
            let consumer = parse(&image(3, None, &needed, rpath, runpath)).unwrap();
            assert!(validate_binding(&consumer, &provider, selected).is_err());
        }
    }

    #[test]
    fn malformed_elf_tables_fail_without_executing_the_file() {
        let original = image(3, Some("libz3.so"), &[], None, None);
        for (offset, value) in [(4usize, 1u8), (5, 2), (54, 0), (0x11f, 255)] {
            let mut damaged = original.clone();
            damaged[offset] = value;
            assert!(parse(&damaged).is_err(), "offset {offset}");
        }
        assert!(parse(&original[..100]).is_err());
        let mut machine_mismatch = parse(&original).unwrap();
        machine_mismatch.machine = 183;
        let consumer = parse(&image(3, None, &["libz3.so"], Some("/private"), None)).unwrap();
        assert!(
            validate_binding(&consumer, &machine_mismatch, Path::new("/private/libz3.so")).is_err()
        );
    }
}
