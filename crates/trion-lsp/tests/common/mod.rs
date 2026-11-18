#![allow(dead_code)]

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;
use tempfile::TempDir;

pub const MANIFEST: &str = "[package]\nname = \"p\"\n";

/// A project on disk, removed when dropped.
///
/// A test writes only what it is about. Every `.trion` file without a
/// `namespace` block is wrapped in one named after its package, and each
/// package without an entry file gets one that includes all of its files.
pub struct Fixture {
    pub dir: TempDir,
}

/// The value of `name = "..."` in the `[package]` table of a manifest.
fn package_name(manifest: &str) -> Option<String> {
    let table = manifest.split("[package]").nth(1)?;
    let line = table.lines().find(|l| l.trim_start().starts_with("name"))?;
    Some(line.split_once('=')?.1.trim().trim_matches('"').to_string())
}

fn has_entry_field(manifest: &str) -> bool {
    manifest.lines().any(|l| l.trim_start().starts_with("entry"))
}

/// Wraps statements in a namespace block of the package.
pub fn wrap(package: &str, text: &str) -> String {
    let first = text.lines().map(str::trim_start).find(|l| !l.is_empty() && !l.starts_with("//")).unwrap_or_default();
    if ["namespace ", "package ", "include "].iter().any(|k| first.starts_with(k)) {
        return text.to_string();
    }
    format!("namespace {package}\n{text}\n")
}

impl Fixture {
    pub fn new(files: &[(&str, &str)]) -> Self {
        Self::build(files, true)
    }

    /// Writes the files exactly as given.
    pub fn raw(files: &[(&str, &str)]) -> Self {
        Self::build(files, false)
    }

    fn build(files: &[(&str, &str)], complete: bool) -> Self {
        let fixture = Self { dir: tempfile::tempdir().unwrap() };
        if !complete {
            for (path, text) in files {
                fixture.write(path, text);
            }
            return fixture;
        }
        // The directory of each package, longest first, so that the nearest wins.
        let mut packages: Vec<(String, String, bool)> = files
            .iter()
            .filter(|(p, _)| Path::new(p).file_name().is_some_and(|n| n == "trion.toml"))
            .map(|(p, text)| {
                let dir = Path::new(p).parent().unwrap().to_string_lossy().into_owned();
                (dir, package_name(text).unwrap_or_else(|| "main".to_string()), has_entry_field(text))
            })
            .collect();
        packages.sort_by_key(|(dir, _, _)| std::cmp::Reverse(dir.len()));
        let owner = |path: &str| packages.iter().find(|(dir, _, _)| dir.is_empty() || path.starts_with(&format!("{dir}/"))).cloned();
        let mut includes: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for (path, text) in files {
            if !path.ends_with(".trion") {
                fixture.write(path, text);
                continue;
            }
            let package = owner(path);
            let name = package.as_ref().map_or("main".to_string(), |(_, n, _)| n.clone());
            fixture.write(path, &wrap(&name, text));
            if let Some((dir, _, _)) = package {
                let relative = if dir.is_empty() { path.to_string() } else { path[dir.len() + 1..].to_string() };
                includes.entry(dir).or_default().push(relative);
            }
        }
        for (dir, name, has_entry) in &packages {
            let entry = if dir.is_empty() { "trion.trion".to_string() } else { format!("{dir}/trion.trion") };
            if *has_entry || files.iter().any(|(p, _)| *p == entry) {
                continue;
            }
            let mut text = format!("package {name} edition \"test\"\n");
            for file in includes.get(dir).into_iter().flatten() {
                text.push_str(&format!("include \"{file}\"\n"));
            }
            fixture.write(&entry, &text);
        }
        fixture
    }

    pub fn path(&self) -> &Path {
        self.dir.path()
    }

    pub fn write(&self, path: &str, text: &str) {
        let full = self.path().join(path);
        fs::create_dir_all(full.parent().unwrap()).unwrap();
        fs::write(full, text).unwrap();
    }

    pub fn read(&self, path: &str) -> String {
        fs::read_to_string(self.path().join(path)).unwrap()
    }
}
