//! Loads a package: `trion.toml`, its entry file, and every included file.

use serde::Deserialize;
use std::collections::{BTreeMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use trion_language::document::{Document, SourceDecl};
use trion_language::{parse_document, Diagnostic, Package, ParsedFile, SpecRef, SpecSet, VocabularyMode};

pub const MANIFEST: &str = "trion.toml";
/// The entry file of a package that does not name one.
pub const DEFAULT_ENTRY: &str = "trion.trion";

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PackageSection {
    pub name: String,
    #[serde(default)]
    pub entry: Option<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Dependency {
    pub path: String,
}

#[derive(Debug, Clone, Deserialize, Default)]
#[serde(deny_unknown_fields)]
pub struct VocabularySection {
    #[serde(default)]
    pub mode: Option<String>,
}

/// How `trion verify` verifies the package. A command-line argument takes
/// the place of the field that it names.
#[derive(Debug, Clone, Deserialize, Default)]
#[serde(deny_unknown_fields, rename_all = "kebab-case")]
pub struct VerifySection {
    /// The number of moments of each trace that is examined.
    pub trace_length: Option<usize>,
    /// The number of individuals of each type that statements about
    /// individuals are read over.
    pub scope: Option<usize>,
    /// The number of decisions that one solver query may make.
    pub decision_limit: Option<u64>,
    /// Checks the properties of the reading: context independence, relation
    /// locality, order independence and round trip.
    #[serde(default)]
    pub properties: bool,
    /// Decides the package again with each bound raised, and reports an
    /// outcome that depends on the bounds.
    #[serde(default)]
    pub stability: bool,
    /// The directory that the queries of the result are written into as
    /// SMT-LIB, for another solver.
    pub smt: Option<String>,
    /// The command of the external prover that is asked the queries of the
    /// result, in place of `["z3", "-in"]`: it reads SMT-LIB on its standard
    /// input.
    #[serde(default)]
    pub prover: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Manifest {
    pub package: PackageSection,
    #[serde(default)]
    pub dependencies: BTreeMap<String, Dependency>,
    #[serde(default)]
    pub vocabulary: VocabularySection,
    #[serde(default)]
    pub verify: VerifySection,
}

#[derive(Debug)]
pub struct Project {
    pub root: PathBuf,
    pub manifest: Manifest,
    pub set: SpecSet,
    pub diagnostics: Vec<Diagnostic>,
    /// Every declared source with a local copy, from any package.
    pub sources: Vec<LoadedSource>,
    /// The path of each file, by the label that diagnostics use.
    pub files: BTreeMap<String, PathBuf>,
}

/// A source declaration with the directory of the file that declares it.
#[derive(Debug, Clone)]
pub struct LoadedSource {
    pub decl: SourceDecl,
    pub dir: PathBuf,
}

fn read_manifest(dir: &Path) -> Result<Manifest, String> {
    let path = dir.join(MANIFEST);
    let text = fs::read_to_string(&path).map_err(|e| format!("cannot read {}: {e}", path.display()))?;
    toml::from_str(&text).map_err(|e| format!("invalid {}: {e}", path.display()))
}

pub fn find_manifest_dir(start: &Path) -> Option<PathBuf> {
    start.ancestors().find(|d| d.join(MANIFEST).is_file()).map(Path::to_path_buf)
}

/// Unsaved editor contents, by canonical path.
pub type Overlay = BTreeMap<PathBuf, String>;

struct LoadedFile {
    label: String,
    path: PathBuf,
    parsed: ParsedFile,
}

struct Loader<'a> {
    project_root: &'a Path,
    overlay: &'a Overlay,
    loaded: Vec<LoadedFile>,
    seen: HashSet<PathBuf>,
    diags: Vec<Diagnostic>,
}

impl Loader<'_> {
    fn at(&self, file: &str, line: usize, text: &str) -> SpecRef {
        SpecRef { id: format!("{file}:{line}"), file: file.to_string(), line, text: text.to_string() }
    }

    fn label(&self, path: &Path) -> String {
        path.strip_prefix(self.project_root).unwrap_or(path).to_string_lossy().into_owned()
    }

    fn read(&self, path: &Path) -> Option<String> {
        self.overlay.get(path).cloned().or_else(|| fs::read_to_string(path).ok())
    }

    /// Loads a file and what it includes, each canonical file once.
    fn load(&mut self, path: &Path, stack: &mut Vec<PathBuf>) {
        if !self.seen.insert(path.to_path_buf()) {
            return;
        }
        let label = self.label(path);
        let Some(text) = self.read(path) else {
            self.diags.push(Diagnostic::error("MISSING_SOURCE", format!("cannot read {label}"), vec![self.at(&label, 0, &label)]));
            return;
        };
        let (parsed, diags) = parse_document(&text, &label);
        self.diags.extend(diags);
        stack.push(path.to_path_buf());
        // Pre-order: a file comes before the files it includes.
        let includes = parsed.includes.clone();
        self.loaded.push(LoadedFile { label: label.clone(), path: path.to_path_buf(), parsed });
        for include in &includes {
            let target = path.parent().unwrap_or(path).join(&include.path);
            let at = self.at(&label, include.line, &format!("include \"{}\"", include.path));
            let Ok(canonical) = target.canonicalize() else {
                if self.overlay.contains_key(&target) {
                    self.load(&target, stack);
                } else {
                    self.diags.push(Diagnostic::error("MISSING_SOURCE", format!("the included file {} cannot be read", include.path), vec![at]));
                }
                continue;
            };
            if stack.contains(&canonical) {
                self.diags.push(Diagnostic::error("INCLUDE_CYCLE", format!("{} includes a file that includes it", include.path), vec![at]));
                continue;
            }
            self.load(&canonical, stack);
        }
        stack.pop();
    }
}

struct RawPackage {
    name: String,
    is_root: bool,
    dir: PathBuf,
    files: Vec<LoadedFile>,
}

fn load_package_files(dir: &Path, manifest: &Manifest, project_root: &Path, overlay: &Overlay, diags: &mut Vec<Diagnostic>) -> Vec<LoadedFile> {
    let entry = dir.join(manifest.package.entry.as_deref().unwrap_or(DEFAULT_ENTRY));
    let entry_label = entry.strip_prefix(project_root).unwrap_or(&entry).to_string_lossy().into_owned();
    let Ok(canonical) = entry.canonicalize() else {
        let at = SpecRef { id: entry_label.clone(), file: entry_label.clone(), line: 0, text: entry_label.clone() };
        diags.push(Diagnostic::error("MISSING_SOURCE", format!("the entry file {entry_label} cannot be read"), vec![at]));
        return Vec::new();
    };
    let mut loader = Loader { project_root, overlay, loaded: Vec::new(), seen: HashSet::new(), diags: Vec::new() };
    loader.load(&canonical, &mut Vec::new());
    diags.append(&mut loader.diags);
    let files = loader.loaded;
    // A package declaration belongs to the entry file alone.
    for file in &files {
        let is_entry = file.path == canonical;
        let at = SpecRef { id: file.label.clone(), file: file.label.clone(), line: 1, text: file.label.clone() };
        match (&file.parsed.package, is_entry) {
            (None, true) => diags.push(Diagnostic::error("package-missing", "the entry file begins with a package declaration", vec![at])),
            (Some(decl), true) if decl.name != manifest.package.name => diags.push(Diagnostic::error("package-mismatch", format!("the entry file declares package `{}`, and {MANIFEST} names `{}`", decl.name, manifest.package.name), vec![at])),
            (Some(_), false) => diags.push(Diagnostic::error("package-in-include", "an included file has no package declaration of its own", vec![at])),
            _ => {}
        }
    }
    // Include order is the reading order: the entry file's includes first.
    files
}

fn first_component(name: &str) -> &str {
    name.split('.').next().unwrap_or(name)
}

/// Follows `use` declarations and loads only the dependencies they reach.
#[allow(clippy::too_many_arguments)]
fn collect_dependencies(owner: &Manifest, root: &Path, dir: &Path, files: &[LoadedFile], seen: &mut HashSet<PathBuf>, names: &mut BTreeMap<String, String>, out: &mut Vec<RawPackage>, diags: &mut Vec<Diagnostic>, overlay: &Overlay) -> Result<(), String> {
    for doc in files.iter().flat_map(|f| &f.parsed.documents) {
        for import in &doc.imports {
            let name = first_component(&import.name);
            if name == owner.package.name {
                continue;
            }
            let Some(dep) = owner.dependencies.get(name) else {
                let at = SpecRef { id: format!("{}:{}", import.file, import.line), file: import.file.clone(), line: import.line, text: format!("use {}", import.name) };
                diags.push(Diagnostic::error("unresolved-import", format!("`{name}` is not this package and is not listed under [dependencies] in {MANIFEST}"), vec![at]));
                continue;
            };
            let dep_dir = dir.join(&dep.path);
            let canonical = dep_dir.canonicalize().map_err(|e| format!("cannot resolve the path {} of dependency `{name}`: {e}", dep_dir.display()))?;
            if !seen.insert(canonical) {
                continue;
            }
            let manifest = read_manifest(&dep_dir)?;
            names.insert(name.to_string(), manifest.package.name.clone());
            let dep_files = load_package_files(&dep_dir, &manifest, root, overlay, diags);
            collect_dependencies(&manifest, root, &dep_dir, &dep_files, seen, names, out, diags, overlay)?;
            out.push(RawPackage { name: manifest.package.name.clone(), is_root: false, dir: dep_dir, files: dep_files });
        }
    }
    Ok(())
}

fn vocabulary_mode(manifest: &Manifest, diags: &mut Vec<Diagnostic>) -> VocabularyMode {
    match manifest.vocabulary.mode.as_deref() {
        None | Some("inferred") => VocabularyMode::Inferred,
        Some("declared") => VocabularyMode::Declared,
        Some(other) => {
            diags.push(Diagnostic::error("manifest-vocabulary-mode", format!("[vocabulary] mode `{other}` does not exist (inferred, declared)"), vec![]));
            VocabularyMode::Inferred
        }
    }
}

/// A namespace name as the analysis reads it: the root package's own prefix
/// is implied, and every other package keeps its name.
fn local_namespace(package: &str, is_root: bool, name: &str) -> String {
    if !is_root {
        return name.to_string();
    }
    match name.strip_prefix(package) {
        Some("") => String::new(),
        Some(rest) if rest.starts_with('.') => rest[1..].to_string(),
        _ => name.to_string(),
    }
}

fn normalize_document(doc: &mut Document, package: &str, is_root: bool, names: &BTreeMap<String, String>, require_prefix: bool, diags: &mut Vec<Diagnostic>) {
    if require_prefix && first_component(&doc.namespace) != package {
        let at = SpecRef { id: doc.file.clone(), file: doc.file.clone(), line: 0, text: format!("namespace {}", doc.namespace) };
        diags.push(Diagnostic::error("namespace-package", format!("the namespace `{}` does not begin with the package name `{package}`", doc.namespace), vec![at]));
    }
    doc.namespace = local_namespace(package, is_root, &doc.namespace);
    for import in &mut doc.imports {
        let first = first_component(&import.name);
        let renamed = match names.get(first) {
            Some(real) => format!("{real}{}", &import.name[first.len()..]),
            None => import.name.clone(),
        };
        import.namespace = local_namespace(package, is_root, &renamed);
    }
}

/// Loads a project from a path. A `.trion` file limits the project to that file.
pub fn load(path: &Path) -> Result<Project, String> {
    load_with(path, &Overlay::new())
}

/// Loads a project, reading open files from the overlay instead of disk.
pub fn load_with(path: &Path, overlay: &Overlay) -> Result<Project, String> {
    let target = path.canonicalize().map_err(|e| format!("cannot resolve {}: {e}", path.display()))?;
    let single_file = target.is_file().then(|| target.clone());
    let base = if target.is_file() { target.parent().unwrap_or(&target).to_path_buf() } else { target.clone() };
    let found = find_manifest_dir(&base);
    let (root, manifest) = match &found {
        Some(dir) => (dir.clone(), read_manifest(dir)?),
        None if single_file.is_some() => (base.clone(), Manifest { package: PackageSection { name: "main".to_string(), entry: None }, dependencies: BTreeMap::new(), vocabulary: VocabularySection::default(), verify: VerifySection::default() }),
        None => return Err(format!("no {MANIFEST} found from {}", base.display())),
    };

    let mut diagnostics = Vec::new();
    let mode = vocabulary_mode(&manifest, &mut diagnostics);
    let root_files = match &single_file {
        Some(file) => {
            let label = file.strip_prefix(&root).unwrap_or(file).to_string_lossy().into_owned();
            let text = match overlay.get(file) {
                Some(text) => text.clone(),
                None => fs::read_to_string(file).map_err(|e| format!("cannot read {}: {e}", file.display()))?,
            };
            let (parsed, diags) = parse_document(&text, &label);
            diagnostics.extend(diags);
            vec![LoadedFile { label, path: file.clone(), parsed }]
        }
        None => load_package_files(&root, &manifest, &root, overlay, &mut diagnostics),
    };
    let mut deps = Vec::new();
    let mut seen = HashSet::new();
    seen.insert(root.clone());
    let mut names = BTreeMap::new();
    collect_dependencies(&manifest, &root, &root, &root_files, &mut seen, &mut names, &mut deps, &mut diagnostics, overlay)?;
    let mut raw = vec![RawPackage { name: manifest.package.name.clone(), is_root: true, dir: root.clone(), files: root_files }];
    raw.extend(deps);

    let mut packages = Vec::new();
    let mut sources = Vec::new();
    let mut files = BTreeMap::new();
    for pkg in raw {
        let mut documents = Vec::new();
        for file in pkg.files {
            files.insert(file.label.clone(), file.path.clone());
            let file_dir = file.path.parent().unwrap_or(&pkg.dir).to_path_buf();
            let require_prefix = !(pkg.is_root && single_file.is_some());
            for mut doc in file.parsed.documents {
                // A use of an unknown package is reported once, as unresolved-import.
                doc.imports.retain(|i| {
                    let first = first_component(&i.name);
                    first == pkg.name || names.contains_key(first)
                });
                normalize_document(&mut doc, &pkg.name, pkg.is_root, &names, require_prefix, &mut diagnostics);
                sources.extend(doc.sources.iter().filter(|s| s.path.is_some()).map(|decl| LoadedSource { decl: decl.clone(), dir: file_dir.clone() }));
                documents.push(doc);
            }
        }
        packages.push(Package { name: pkg.name, is_root: pkg.is_root, documents });
    }
    Ok(Project { root, manifest, set: SpecSet { packages, vocabulary_mode: mode }, diagnostics, sources, files })
}

impl Project {
    /// Every specification, in the root package and in its dependencies.
    pub fn all_specs(&self) -> impl Iterator<Item = &trion_language::Spec> {
        self.set.packages.iter().flat_map(|p| &p.documents).flat_map(|d| &d.specs)
    }

    pub fn root_specs(&self) -> impl Iterator<Item = &trion_language::Spec> {
        self.set.packages.iter().filter(|p| p.is_root).flat_map(|p| &p.documents).flat_map(|d| &d.specs)
    }

    /// The revision of the package: the digest of its specification files.
    /// It is the identity that a revision reference names.
    pub fn revision(&self) -> String {
        crate::digest::hash_files(self.files.values().cloned())
    }
}
