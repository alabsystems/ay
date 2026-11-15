//! Helper functions for parser that can be reused for new parsers.

use spire_enum::prelude::{delegate_impl, delegated_enum};
use std::{
    fs::File,
    io::{self, BufRead, BufReader, Lines, Read},
    path::Path,
};

use crate::error::ParserError;

/// Type of compression of encoding of file.
pub enum Encoding {
    /// No compression or encoding.
    Plain,
    Zstd,
    Gzip,
    Xz,
    // maybe more ...
}

impl Encoding {
    /// Determine the encoding from the file name extension.
    pub fn from_path(path: &Path) -> Self {
        match path.extension().and_then(|e| e.to_str()) {
            Some(ext) if ext.eq_ignore_ascii_case("zst") => Self::Zstd,
            Some(ext) if ext.eq_ignore_ascii_case("zstd") => Self::Zstd,
            Some(ext) if ext.eq_ignore_ascii_case("gzip") => Self::Gzip,
            Some(ext) if ext.eq_ignore_ascii_case("gz") => Self::Gzip,
            Some(ext) if ext.eq_ignore_ascii_case("xz") => Self::Xz,
            _ => Self::Plain,
        }
    }
}

/// A reader of file that might be compressed.
///
/// If the file is compressed, then the reader wraps a decoder decoding the compressed file.
#[delegated_enum]
pub enum MaybeCompressed<R: Read> {
    Plain(BufReader<R>),
    Zstd(BufReader<zstd::stream::read::Decoder<'static, BufReader<R>>>),
    Gzip(BufReader<flate2::read::GzDecoder<BufReader<R>>>),
    Xz(BufReader<xz2::read::XzDecoder<BufReader<R>>>),
}

#[delegate_impl]
impl<R: Read> Read for MaybeCompressed<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize>;
}

#[delegate_impl]
impl<R: Read> BufRead for MaybeCompressed<R> {
    fn fill_buf(&mut self) -> io::Result<&[u8]>;
    fn consume(&mut self, amt: usize);
}

/// Get an iterator over the lines at the file with path `filename`.
pub fn get_lines<P: AsRef<Path>>(filename: P) -> Result<Lines<MaybeCompressed<File>>, ParserError> {
    Ok(open_maybe_compressed(filename)?.0.lines())
}

/// Turn one item of a [`Lines`] iterator into a [`Result<String, ParserError>`].
///
/// [`std::io::BufRead::lines`] yields `Err` both for lines that are not valid
/// UTF-8 and for genuine I/O failures (including failures surfaced only while
/// decompressing a [`MaybeCompressed`] stream). Callers **must not** stop
/// iterating on such an error (as `map_while(Result::ok)` does): the remaining
/// lines of the file would then be discarded without a word, so a proof would
/// be checked against only a prefix of the formula. Use this helper to attach
/// the file name and line number and propagate the error instead.
#[inline]
pub fn read_line<P>(
    line: std::io::Result<String>,
    filename: P,
    line_number: usize,
) -> Result<String, ParserError>
where
    P: AsRef<Path>,
{
    line.map_err(|source| ParserError::LineReadError {
        filename: filename.as_ref().to_string_lossy().to_string(),
        line: line_number,
        source,
    })
}

impl<R: Read> MaybeCompressed<R> {
    pub fn encoding(&self) -> Encoding {
        match self {
            Self::Plain(_) => Encoding::Plain,
            Self::Zstd(_) => Encoding::Zstd,
            Self::Gzip(_) => Encoding::Gzip,
            Self::Xz(_) => Encoding::Xz,
        }
    }
}

/// Open a file that might be compressed using the automatically detected decoder for the compression format.
pub fn open_maybe_compressed<P: AsRef<Path>>(
    filename: P,
) -> Result<(MaybeCompressed<File>, Option<u64>), ParserError> {
    let filename = filename.as_ref();
    let file = File::open(filename).map_err(ParserError::from)?;
    match Encoding::from_path(filename) {
        Encoding::Plain => {
            let file_size = file.metadata().unwrap().len();
            Ok((
                MaybeCompressed::Plain(BufReader::new(file)),
                Some(file_size),
            ))
        }
        Encoding::Zstd => {
            let decoder = zstd::stream::read::Decoder::new(file)?;
            Ok((MaybeCompressed::Zstd(BufReader::new(decoder)), None))
        }
        Encoding::Gzip => {
            let decoder = flate2::read::GzDecoder::new(BufReader::new(file));
            Ok((MaybeCompressed::Gzip(BufReader::new(decoder)), None))
        }
        Encoding::Xz => {
            let decoder = xz2::read::XzDecoder::new(BufReader::new(file));
            Ok((MaybeCompressed::Xz(BufReader::new(decoder)), None))
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::io::{Error, ErrorKind};

    #[test]
    fn read_line_passes_through_a_successful_line() {
        let line = read_line(Ok("1 2 0".to_string()), "t.cnf", 3).expect("should be Ok");
        assert_eq!(line, "1 2 0");
    }

    /// A genuine mid-file I/O error (here: a hardware-style `Other` error, with
    /// no UTF-8 involvement) must be turned into a [`ParserError`], preserving
    /// the underlying [`std::io::Error`] so the cause is reportable.
    #[test]
    fn read_line_propagates_an_io_error() {
        let source = Error::other("simulated device failure");
        match read_line(Err(source), "t.cnf", 41) {
            Ok(line) => panic!("an I/O error must not be turned into a line: {line:?}"),
            Err(ParserError::LineReadError {
                filename,
                line,
                source,
            }) => {
                assert_eq!(filename, "t.cnf");
                assert_eq!(line, 41);
                assert_eq!(source.kind(), ErrorKind::Other);
                assert!(source.to_string().contains("simulated device failure"));
            }
            Err(e) => panic!("expected LineReadError, got: {e:?}"),
        }
    }

    /// `BufRead::lines()` reports non-UTF-8 input as `ErrorKind::InvalidData`;
    /// that error must be propagated the same way.
    #[test]
    fn read_line_propagates_an_invalid_utf8_error() {
        let source = Error::new(ErrorKind::InvalidData, "stream did not contain valid UTF-8");
        assert!(matches!(
            read_line(Err(source), "t.opb", 0),
            Err(ParserError::LineReadError { .. })
        ));
    }
}
