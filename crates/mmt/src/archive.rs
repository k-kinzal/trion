//! MMT archives (doc/language/namespaces.md on narration bases and documents;
//! `api/archives/Archive.scala`, `api/utils/File.scala` `readPropertiesFromString`).
//!
//! An archive is a directory with a manifest `META-INF/MANIFEST.MF` and the
//! sources in the folder `source`. The manifest is read as MMT reads it: each
//! line is trimmed; lines starting with `//` are ignored; a line with a colon
//! after a non-empty key defines the key, and a key given twice has its
//! values joined by a space. The keys used here are `id`, `narration-base`
//! (the document URI of a source file is the narration base followed by the
//! file's path relative to `source`), `ns`/`source-base` and `dependencies`
//! (separated by commas or whitespace). All `.mmt` files below `source` are
//! read, skipping the folders `.svn`, `.mmt` and `.git` as MMT does; the key
//! `ignore` is not supported and is reported as unsupported if present.
//!
//! The theories of all archives given to [`Library::load_archives`] are
//! elaborated in dependency order rather than file order: a theory that
//! includes a theory, or uses a meta-theory, of another file causes that
//! theory to be elaborated first, like MMT's build does through its
//! dependency management. A dependency of an archive that is not given is
//! reported in [`ArchiveLoad::missing_dependencies`]; it is an error only if
//! a theory refers to something from it.
//!
//! Folders reached through symbolic links are read once: a link back to a
//! folder that is already being read is skipped, so a cycle of links ends.
//! Without a narration base, the document URI of a file is its `file:` URI
//! (see [`Uri::from_file_path`]).

use std::collections::HashSet;
use std::fs;
use std::path::{Path as FsPath, PathBuf};

use crate::error::{Error, ErrorKind, Result};
use crate::library::{Elaboration, Library};
use crate::syntax::Document;
use crate::uri::{DPath, MPath, Uri};

/// The properties of a manifest in order.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Manifest {
    properties: Vec<(String, String)>,
}

impl Manifest {
    /// Reads a manifest as `readPropertiesFromString` does.
    pub fn parse(s: &str) -> Manifest {
        let mut m = Manifest::default();
        for line in s.split('\n') {
            let t = line.trim();
            if t.starts_with("//") {
                continue;
            }
            if let Some(p) = t.find(':') {
                if p == 0 {
                    continue;
                }
                let key = t[..p].trim().to_string();
                let value = t[p + 1..].trim().to_string();
                match m.properties.iter_mut().find(|(k, _)| *k == key) {
                    Some((_, v)) => {
                        v.push(' ');
                        v.push_str(&value);
                    }
                    None => m.properties.push((key, value)),
                }
            }
        }
        m
    }

    /// Key and value pairs in the order of first occurrence.
    pub fn properties(&self) -> impl Iterator<Item = (&str, &str)> {
        self.properties.iter().map(|(k, v)| (k.as_str(), v.as_str()))
    }

    /// The value of a key.
    pub fn get(&self, key: &str) -> Option<&str> {
        self.properties.iter().find(|(k, _)| k == key).map(|(_, v)| v.as_str())
    }

    /// The archive id.
    pub fn id(&self) -> Option<&str> {
        self.get("id")
    }

    /// The narration base.
    pub fn narration_base(&self) -> Option<Uri> {
        self.get("narration-base").map(Uri::parse)
    }

    /// The ids of the archives this one depends on.
    pub fn dependencies(&self) -> Vec<String> {
        self.get("dependencies").map(|d| d.replace(',', " ").split_whitespace().map(str::to_string).collect()).unwrap_or_default()
    }
}

/// An archive on disk.
#[derive(Clone, Debug)]
pub struct Archive {
    root: PathBuf,
    manifest: Manifest,
}

impl Archive {
    /// Opens the archive at a root directory.
    pub fn open(root: impl AsRef<FsPath>) -> Result<Archive> {
        let root = root.as_ref().to_path_buf();
        let mf = root.join("META-INF").join("MANIFEST.MF");
        let text = fs::read_to_string(&mf).map_err(|e| Error::new(ErrorKind::Archive, format!("cannot read {}: {e}", mf.display())))?;
        let manifest = Manifest::parse(&text);
        if manifest.id().is_none() {
            return Err(Error::new(ErrorKind::Archive, format!("{} has no id", mf.display())));
        }
        if manifest.get("ignore").is_some() {
            return Err(Error::new(ErrorKind::Unsupported, format!("{}: the manifest key ignore is not supported", mf.display())));
        }
        Ok(Archive { root, manifest })
    }

    /// The root directory.
    pub fn root(&self) -> &FsPath {
        &self.root
    }

    /// The manifest.
    pub fn manifest(&self) -> &Manifest {
        &self.manifest
    }

    /// The archive id.
    pub fn id(&self) -> &str {
        self.manifest.id().unwrap_or_default()
    }

    /// The `.mmt` files below `source`, as paths relative to `source`, sorted.
    pub fn source_files(&self) -> Result<Vec<Vec<String>>> {
        let cannot = |p: &FsPath, e: std::io::Error| Error::new(ErrorKind::Archive, format!("cannot read {}: {e}", p.display()));
        let mut out = Vec::new();
        let src = self.root.join("source");
        let mut visited: HashSet<PathBuf> = HashSet::new();
        let mut stack: Vec<(PathBuf, Vec<String>)> = vec![(src, Vec::new())];
        while let Some((dir, prefix)) = stack.pop() {
            let real = fs::canonicalize(&dir).map_err(|e| cannot(&dir, e))?;
            if !visited.insert(real) {
                continue;
            }
            for e in fs::read_dir(&dir).map_err(|e| cannot(&dir, e))? {
                let e = e.map_err(|e| cannot(&dir, e))?;
                let name = e.file_name().to_string_lossy().into_owned();
                let p = e.path();
                let mut rel = prefix.clone();
                rel.push(name.clone());
                if p.is_dir() {
                    if ![".svn", ".mmt", ".git"].contains(&name.as_str()) {
                        stack.push((p, rel));
                    }
                } else if name.ends_with(".mmt") {
                    out.push(rel);
                }
            }
        }
        out.sort();
        Ok(out)
    }

    /// The document URI of a source file.
    pub fn document_uri(&self, rel: &[String]) -> Result<DPath> {
        let base = self.manifest.narration_base().unwrap_or_else(|| Uri::from_file_path(&self.root));
        Ok(DPath::new(base)?.slash(rel))
    }
}

/// The result of loading archives.
#[derive(Debug, Default)]
pub struct ArchiveLoad {
    files: Vec<(PathBuf, Vec<MPath>)>,
    missing_dependencies: Vec<(String, String)>,
    errors: Vec<Error>,
}

impl ArchiveLoad {
    /// The files read, with the theories each one added.
    pub fn files(&self) -> &[(PathBuf, Vec<MPath>)] {
        &self.files
    }

    /// Dependencies named in a manifest that were not given, as (archive, dependency).
    pub fn missing_dependencies(&self) -> &[(String, String)] {
        &self.missing_dependencies
    }

    /// All errors, attributed to files.
    pub fn errors(&self) -> &[Error] {
        &self.errors
    }
}

impl Library {
    /// Reads and elaborates the sources of archives (see the module documentation).
    pub fn load_archives(&mut self, archives: &[Archive]) -> ArchiveLoad {
        let mut out = ArchiveLoad::default();
        let ids: Vec<&str> = archives.iter().map(Archive::id).collect();
        for a in archives {
            for d in a.manifest.dependencies() {
                if !ids.contains(&d.as_str()) {
                    out.missing_dependencies.push((a.id().to_string(), d));
                }
            }
        }
        let mut units: Vec<(usize, Vec<usize>)> = Vec::new();
        for a in archives {
            let files = match a.source_files() {
                Ok(f) => f,
                Err(e) => {
                    out.errors.push(e);
                    continue;
                }
            };
            for rel in files {
                let path = rel.iter().fold(a.root.join("source"), |p, s| p.join(s));
                let text = match fs::read_to_string(&path) {
                    Ok(t) => t,
                    Err(e) => {
                        out.errors.push(Error::new(ErrorKind::Archive, format!("cannot read {}: {e}", path.display())));
                        continue;
                    }
                };
                let doc = match Document::parse_with_limits(&text, self.limits()) {
                    Ok(d) => d,
                    Err(e) => {
                        out.errors.push(e.in_file(&path));
                        out.files.push((path, vec![]));
                        continue;
                    }
                };
                let base = match a.document_uri(&rel) {
                    Ok(b) => b,
                    Err(e) => {
                        out.errors.push(e.in_file(&path));
                        continue;
                    }
                };
                let us = self.register_document(&doc, &base, Some(&path), &mut out.errors);
                units.push((out.files.len(), us));
                out.files.push((path, vec![]));
            }
        }
        for (fi, us) in units {
            for u in us {
                match self.load_unit(u) {
                    Ok(ps) => out.files[fi].1.extend(ps),
                    Err(e) => out.errors.push(e),
                }
            }
        }
        out
    }

    /// Reads a single source file with a document URI and reports like [`Library::add_source`].
    pub fn load_file(&mut self, path: impl AsRef<FsPath>, base: &DPath) -> Elaboration {
        let path = path.as_ref();
        match fs::read_to_string(path) {
            Ok(t) => self.add_source(&t, base, Some(path)),
            Err(e) => {
                let mut out = Elaboration::default();
                out.push_error(Error::new(ErrorKind::Archive, format!("cannot read {}: {e}", path.display())));
                out
            }
        }
    }
}
