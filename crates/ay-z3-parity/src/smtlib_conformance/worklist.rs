use serde::Serialize;
use std::fs;
use std::io::{self, BufWriter, Write};
use std::path::{self, Path, PathBuf};
use tempfile::NamedTempFile;

pub(super) struct Worklist {
    destination: PathBuf,
    writer: Option<BufWriter<NamedTempFile>>,
    rows: usize,
}

impl Worklist {
    pub(super) fn stage(path: &Path, header: &impl Serialize) -> Result<Self, String> {
        let destination = path::absolute(path).map_err(|error| {
            format!("cannot resolve worklist path {} ({error})", path.display())
        })?;
        match fs::symlink_metadata(&destination) {
            Ok(_) => {
                return Err(format!(
                    "worklist already exists at {}",
                    destination.display()
                ))
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => {
                return Err(format!(
                    "cannot inspect worklist path {} ({error})",
                    destination.display()
                ));
            }
        }
        let directory = destination
            .parent()
            .ok_or_else(|| format!("worklist path has no parent at {}", destination.display()))?;
        let file = tempfile::Builder::new()
            .prefix(".ay-z3-worklist-")
            .tempfile_in(directory)
            .map_err(|error| {
                format!("cannot stage worklist {} ({error})", destination.display())
            })?;
        let mut worklist = Self {
            destination,
            writer: Some(BufWriter::new(file)),
            rows: 0,
        };
        worklist.writer = Some(worklist.stage_line(header)?);
        Ok(worklist)
    }

    pub(super) fn append(&mut self, row: &impl Serialize) -> Result<(), String> {
        let writer = self.stage_line(row)?;
        self.rows = self
            .rows
            .checked_add(1)
            .ok_or_else(|| format!("too many rows in worklist {}", self.destination.display()))?;
        self.writer = Some(writer);
        Ok(())
    }

    pub(super) fn rows(&self) -> usize {
        self.rows
    }

    pub(super) fn publish(mut self, trailer: &impl Serialize) -> Result<(), String> {
        let staged_file = self.stage_line(trailer)?.into_inner().map_err(|error| {
            format!(
                "cannot flush worklist {} ({})",
                self.destination.display(),
                error.error()
            )
        })?;
        staged_file.as_file().sync_all().map_err(|error| {
            format!(
                "cannot sync worklist {} ({error})",
                self.destination.display()
            )
        })?;
        staged_file
            .persist_noclobber(&self.destination)
            .map_err(|error| {
                format!(
                    "cannot publish worklist {} ({})",
                    self.destination.display(),
                    error.error
                )
            })?;
        Ok(())
    }

    fn stage_line(&mut self, row: &impl Serialize) -> Result<BufWriter<NamedTempFile>, String> {
        // Dropping the writer on any error removes a stage with a partially written row.
        let mut writer = self.writer.take().ok_or_else(|| {
            format!(
                "worklist staging has failed at {}",
                self.destination.display()
            )
        })?;
        serde_json::to_writer(&mut writer, row)
            .map_err(io::Error::other)
            .and_then(|()| writer.write_all(b"\n"))
            .map_err(|error| {
                format!(
                    "cannot write worklist {} ({error})",
                    self.destination.display()
                )
            })?;
        Ok(writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::ser::{Error as _, SerializeSeq as _};
    use serde_json::{json, Value};

    #[test]
    fn dropping_unpublished_worklist_removes_the_stage() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("work.jsonl");
        let mut worklist = Worklist::stage(&path, &json!({"header": true})).unwrap();
        worklist.append(&"x".repeat(128 * 1024)).unwrap();
        assert!(!path.exists());
        assert_eq!(fs::read_dir(directory.path()).unwrap().count(), 1);

        drop(worklist);

        assert_eq!(fs::read_dir(directory.path()).unwrap().count(), 0);
    }

    #[test]
    fn publishing_exposes_a_complete_json_line_for_each_record() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("work.jsonl");
        let header = json!({"header": "input"});
        let first = json!({"case": "x".repeat(128 * 1024)});
        let second = json!({"case": "text\nwith a newline"});
        let trailer = json!({"rows": 2});
        let mut worklist = Worklist::stage(&path, &header).unwrap();
        assert_eq!(worklist.rows(), 0);
        worklist.append(&first).unwrap();
        worklist.append(&second).unwrap();
        assert_eq!(worklist.rows(), 2);
        assert!(!path.exists());

        worklist.publish(&trailer).unwrap();

        let content = fs::read_to_string(&path).unwrap();
        assert!(content.ends_with('\n'));
        let records: Vec<Value> = content
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .collect();
        assert_eq!(records, [header, first, second, trailer]);
        assert_eq!(fs::read_dir(directory.path()).unwrap().count(), 1);
    }

    #[test]
    fn competing_publication_preserves_the_winners_bytes() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("work.jsonl");
        let mut first = Worklist::stage(&path, &"first header").unwrap();
        let mut second = Worklist::stage(&path, &"second header").unwrap();
        first.append(&"first row").unwrap();
        second.append(&"second row").unwrap();

        first.publish(&"first trailer").unwrap();
        let winner = fs::read(&path).unwrap();
        assert!(second.publish(&"second trailer").is_err());

        assert_eq!(fs::read(&path).unwrap(), winner);
        assert!(Worklist::stage(&path, &"third header").is_err());
        assert_eq!(fs::read_dir(directory.path()).unwrap().count(), 1);
    }

    #[test]
    fn partial_serialization_prevents_publication() {
        struct FailingRow;

        impl Serialize for FailingRow {
            fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                let mut sequence = serializer.serialize_seq(None)?;
                sequence.serialize_element(&"partially written row")?;
                Err(S::Error::custom("injected serialization failure"))
            }
        }

        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("work.jsonl");
        let mut worklist = Worklist::stage(&path, &"header").unwrap();

        assert!(worklist.append(&FailingRow).is_err());
        assert_eq!(worklist.rows(), 0);
        assert!(worklist.publish(&"trailer").is_err());

        assert_eq!(fs::read_dir(directory.path()).unwrap().count(), 0);
    }
}
