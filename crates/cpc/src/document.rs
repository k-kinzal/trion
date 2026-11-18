//! Self-contained proof documents that Ethos can check.
//!
//! cvc5's proof is not checkable on its own: it uses the symbols and rules of
//! the CPC signature without including it. cvc5's
//! `contrib/get-ethos-checker` (tag cvc5-1.4.2) makes it checkable with the
//! script `cpc_gen.sh`, which prints
//!
//! ```text
//! (include "$SIG_DIR/Cpc.eo")
//! (include "$SIG_DIR/expert/CpcExpert.eo")
//! ```
//!
//! and then the output of `cvc5 --dump-proofs ...` without its first two
//! lines and its last line (`tail -n +3 | head -n -1`), that is, without the
//! `unsat` and the parentheses around the proof. [`ProofDocument`] is the same
//! document built from a parsed proof instead of from lines:
//!
//! - its header is the same `include`s ([`Variant::Expert`], as in
//!   `cpc_gen.sh`) or only `Cpc.eo` ([`Variant::Cpc`]), with the signature
//!   directory given by the caller;
//! - its body is the commands of one proof, printed by `eunoia` (the layout
//!   of cvc5's text is not kept; the commands are). The body can come from
//!   cvc5 ([`ProofDocument::from_cvc5_output`], one document per proof) or be
//!   any script the caller builds ([`ProofDocument::new`]).
//!
//! The declarations of the problem's symbols are in cvc5's proof unless cvc5
//! runs with `--proof-print-reference`. With that option the proof omits them
//! and the document must instead name the original SMT-LIB problem with
//! `(reference "<file>")` ([`ProofDocument::with_reference`]); Ethos then
//! reads the declarations from the problem and also checks that every
//! `assume` is one of its assertions (manual "Validation Proofs via Reference
//! Inputs"). [`ProofDocument::write`] writes such a document together with the
//! problem text it references.
//!
//! Nothing here checks a proof: the crate reads and writes the format, and
//! whether a document is a well-formed and valid CPC proof is for Ethos to
//! say (the tests run Ethos on every document they build).

use std::fmt;
use std::io;
use std::path::{Component, Path, PathBuf};

use eunoia::{Command, Script, StrLit, Term};

use crate::output::{read_proofs, OutputError, Proof, SessionOptions};

/// Which part of the CPC signature a document includes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Variant {
    /// `Cpc.eo`: the calculus of cvc5 under its safe options.
    Cpc,
    /// `Cpc.eo` and `expert/CpcExpert.eo`: also the experimental theories and
    /// rules. This is what `contrib/get-ethos-checker` includes in every proof.
    Expert,
}

impl Variant {
    /// The entry files of the variant, relative to the signature directory, in
    /// the order in which they are included.
    pub fn entry_points(self) -> &'static [&'static str] {
        match self {
            Variant::Cpc => &["Cpc.eo"],
            Variant::Expert => &["Cpc.eo", "expert/CpcExpert.eo"],
        }
    }
}

impl fmt::Display for Variant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Variant::Cpc => "CPC",
            Variant::Expert => "CPC expert",
        })
    }
}

/// A proof document: the includes of the signature, optionally a reference
/// to the problem, and the commands of one proof. Every value prints to a
/// document that `eunoia` reads back.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofDocument {
    signature_dir: String,
    variant: Variant,
    includes: Vec<StrLit>,
    reference: Option<StrLit>,
    body: Script,
}

/// A document that cannot be built or written.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum DocumentError {
    /// cvc5's output cannot be read.
    Output(OutputError),
    /// A path that a string literal cannot hold: it has a character outside ASCII.
    NotAscii(String),
    /// A reference or file name that is not a plain relative path inside the
    /// document's directory (absolute, or with `..`, or empty).
    OutsideDirectory(String),
    /// A reference was requested for a proof that declares symbols itself;
    /// Ethos would bind them a second time and the assumptions would no longer
    /// be the reference's assertions. Such proofs come from cvc5 without
    /// `--proof-print-reference`.
    DeclaresSymbols(String),
}

impl fmt::Display for DocumentError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DocumentError::Output(e) => write!(f, "{e}"),
            DocumentError::NotAscii(p) => write!(f, "a path in an include or reference must be ASCII: {p:?}"),
            DocumentError::OutsideDirectory(p) => write!(f, "{p:?} is not a relative path inside the document's directory"),
            DocumentError::DeclaresSymbols(s) => write!(f, "the proof declares `{s}` itself, so it cannot reference the problem (run cvc5 with --proof-print-reference)"),
        }
    }
}

impl std::error::Error for DocumentError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            DocumentError::Output(e) => Some(e),
            _ => None,
        }
    }
}

fn declared_name(c: &Command) -> Option<String> {
    match c {
        Command::DeclareConst { name, .. } | Command::DeclareParameterizedConst { name, .. } | Command::DeclareSort { name, .. } | Command::DeclareDatatype { name, .. } => Some(name.as_str().to_string()),
        Command::DeclareDatatypes(dts) => dts.first().map(|(n, _, _)| n.as_str().to_string()),
        _ => None,
    }
}

fn ascii(s: &str) -> Result<StrLit, DocumentError> {
    StrLit::new(s).map_err(|_| DocumentError::NotAscii(s.to_string()))
}

/// Whether `p` is a non-empty relative path made of plain names only.
fn inside(p: &str) -> bool {
    let path = Path::new(p);
    !p.is_empty() && path.components().all(|c| matches!(c, Component::Normal(_) | Component::CurDir)) && path.components().any(|c| matches!(c, Component::Normal(_)))
}

impl ProofDocument {
    /// A document whose body is `body`, including the signature of `variant`
    /// from `signature_dir` (absolute, or relative to the document's
    /// directory). Refused: a directory that is not ASCII.
    ///
    /// ```
    /// use cpc::{ProofDocument, Variant};
    /// let body = eunoia::parse_script("(assume @p1 false)")?;
    /// let doc = ProofDocument::new("/opt/cvc5/proofs/eo/cpc", Variant::Cpc, body)?;
    /// assert_eq!(doc.to_string(), "(include \"/opt/cvc5/proofs/eo/cpc/Cpc.eo\")\n(assume @p1 false)\n");
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn new(signature_dir: &str, variant: Variant, body: Script) -> Result<ProofDocument, DocumentError> {
        ascii(signature_dir)?;
        let dir = signature_dir.trim_end_matches('/');
        let includes = variant.entry_points().iter().map(|e| ascii(&format!("{dir}/{e}"))).collect::<Result<_, _>>()?;
        Ok(ProofDocument { signature_dir: signature_dir.to_string(), variant, includes, reference: None, body })
    }

    /// The document of a proof read from cvc5's output.
    pub fn from_proof(proof: Proof, signature_dir: &str, variant: Variant) -> Result<ProofDocument, DocumentError> {
        ProofDocument::new(signature_dir, variant, proof.into_script())
    }

    /// One document per proof in cvc5's output for `commands` (see
    /// [`read_proofs`]).
    pub fn from_cvc5_output(output: &str, commands: &[smtlib::Command], options: SessionOptions, signature_dir: &str, variant: Variant) -> Result<Vec<ProofDocument>, DocumentError> {
        ascii(signature_dir)?;
        let proofs = read_proofs(output, commands, options).map_err(DocumentError::Output)?;
        proofs.into_iter().map(|p| ProofDocument::from_proof(p, signature_dir, variant)).collect()
    }

    /// The same document, referencing the SMT-LIB problem `file`, a relative
    /// path inside the document's directory. Refused: a path that is not
    /// ASCII, is absolute or has `..`; a proof that declares symbols itself.
    pub fn with_reference(mut self, file: &str) -> Result<ProofDocument, DocumentError> {
        let lit = ascii(file)?;
        if !inside(file) {
            return Err(DocumentError::OutsideDirectory(file.to_string()));
        }
        if let Some(name) = self.body.commands().iter().find_map(declared_name) {
            return Err(DocumentError::DeclaresSymbols(name));
        }
        self.reference = Some(lit);
        Ok(self)
    }

    /// The signature directory, as given.
    pub fn signature_dir(&self) -> &str {
        &self.signature_dir
    }

    /// The variant whose entry points are included.
    pub fn variant(&self) -> Variant {
        self.variant
    }

    /// The SMT-LIB problem named by `reference`, if any.
    pub fn reference(&self) -> Option<&str> {
        self.reference.as_ref().map(StrLit::as_str)
    }

    /// The commands of the proof.
    pub fn body(&self) -> &Script {
        &self.body
    }

    /// The commands before the proof: the includes and the reference.
    pub fn header(&self) -> Vec<Command> {
        let mut out: Vec<Command> = self.includes.iter().cloned().map(Command::Include).collect();
        if let Some(r) = &self.reference {
            out.push(Command::Reference { file: r.clone(), normalize: None });
        }
        out
    }

    /// The whole document as a script.
    pub fn to_script(&self) -> Script {
        let mut script = Script::new(self.header());
        script.append(self.body.clone());
        script
    }

    /// Whether the proof has neither an assumption nor a step (`ethos_check.sh`
    /// warns "Empty proof" in that case).
    pub fn is_empty(&self) -> bool {
        !self.body.commands().iter().any(|c| matches!(c, Command::Assume { .. } | Command::AssumePush { .. } | Command::Step(_) | Command::StepPop(_)))
    }

    /// Whether the last step claims `false` as its conclusion. This is what
    /// the proof says, not a check that it holds (Ethos's
    /// `--require-proof-of-false` checks that).
    pub fn claims_false(&self) -> bool {
        match self.body.commands().iter().rev().find(|c| matches!(c, Command::Step(_) | Command::StepPop(_))) {
            Some(Command::Step(s)) => matches!(&s.conclusion, Some(Term::Symbol(x)) if x.as_str() == "false"),
            _ => false,
        }
    }

    /// Writes the document to `dir/file_name`. A document with a reference
    /// needs the problem's SMT-LIB text, which is written to the referenced
    /// file in `dir`; a document without one ignores `problem`. Refused, with
    /// [`io::ErrorKind::InvalidInput`]: a `file_name` that is not a plain
    /// relative path inside `dir`.
    pub fn write(&self, dir: &Path, file_name: &str, problem: Option<&str>) -> io::Result<PathBuf> {
        if !inside(file_name) {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, DocumentError::OutsideDirectory(file_name.to_string())));
        }
        if let Some(r) = &self.reference {
            let text = problem.ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "a document with a reference needs the problem text"))?;
            std::fs::write(dir.join(r.as_str()), text)?;
        }
        let path = dir.join(file_name);
        std::fs::write(&path, self.to_string())?;
        Ok(path)
    }
}

impl fmt::Display for ProofDocument {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for c in self.header() {
            writeln!(f, "{c}")?;
        }
        write!(f, "{}", self.body)
    }
}
