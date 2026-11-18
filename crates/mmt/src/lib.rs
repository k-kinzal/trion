//! # mmt: reading and writing the MMT language
//!
//! This crate reads and writes the language of MMT v27.0.0: the surface
//! syntax of `.mmt` files and archives, MMT URIs, OpenMath-style objects,
//! objects read and written by the notations that theories declare, and
//! literals. It is written in Rust with the standard library only and needs
//! no JVM.
//!
//! It models the grammar and what reading needs, nothing more: objects can
//! only be read with the notations in scope, so the library elaborates
//! theories (meta-theories, includes, the declarations before an object) to
//! know them. It does not type-check, does not check that a symbol exists
//! before it is used, and knows no theory of its own: LF's notations come
//! from the theories the caller loads (for example the MMT/urtheories
//! archive). Static validity is MMT's business; run `mmt.jar` on the output
//! where it matters.
//!
//! ```
//! use mmt::{Library, uri::DPath};
//!
//! // MMT's brackets are the constant `brackets` of `http://cds.omdoc.org/mmt?mmt`
//! let src = "namespace http://cds.omdoc.org/mmt❚
//! theory mmt =
//!   brackets # ( 1 ) prec -1000005❙
//! ❚
//! namespace http://example.org/logic❚
//! import m http://cds.omdoc.org/mmt❚
//! theory Logic =
//!   include m?mmt❙
//!   and # 1 ∧ 2 prec 10❙
//!   true❙
//! ❚";
//! let mut lib = Library::new();
//! let base: DPath = "http://example.org/logic.mmt".parse()?;
//! let read = lib.add_source(src, &base, None);
//! assert!(read.is_ok(), "{:?}", read.errors());
//!
//! let logic = "http://example.org/logic?Logic".parse()?;
//! let scope = lib.object_scope(&logic)?;
//! let object = scope.parse("true ∧ (true ∧ true)")?;
//! assert_eq!(object.term().to_string(), "(and true (and true true))");
//! assert_eq!(scope.print(&object)?, "true ∧ (true ∧ true)");
//!
//! // whole theories print as a document that reads back as the same theories
//! let mmt = "http://cds.omdoc.org/mmt?mmt".parse()?;
//! let text = lib.print_theories(&[mmt, logic.clone()])?;
//! let mut again = Library::new();
//! assert!(again.add_source(&text, &base, None).is_ok());
//! assert_eq!(again.theory(&logic), lib.theory(&logic));
//! # Ok::<(), mmt::Error>(())
//! ```
//!
//! ## Specification
//!
//! - Title: the MMT language, as implemented by the MMT system.
//! - Version: MMT v27.0.0 (release tag `v27.0.0` of <https://github.com/UniFormal/MMT>,
//!   the jar `mmt.jar` of that release).
//! - Documentation: <https://uniformal.github.io/doc/language/> (the files
//!   `doc/language/*.md` of the documentation site: delimiters, namespaces,
//!   uris, modules, declarations, objects, literals, implicit). Where the
//!   documentation is silent or disagrees with the implementation, the Scala
//!   sources of v27.0.0 decide, and the module documentation names the files
//!   (`mmt-api/src/main/info/kwarc/mmt/api/...` written `api/...`). One
//!   disagreement is recorded in the tests: the metadata examples of
//!   declarations.md and modules.md use module URIs as keys, which MMT
//!   rejects (`tests/doc_examples.rs`).
//!
//! ## Pinned versions used by the tests
//!
//! The tests that compare with MMT or read the real MMT/urtheories expect
//! these in the repository's `.tools` directory, are ignored by default, and
//! say what they need when they are run without it:
//!
//! - `.tools/mmt.jar`: MMT v27.0.0, run with `.tools/bin/java` (only in
//!   `tests/differential.rs`, as an oracle; never by the crate);
//! - `.tools/urtheories`: the archive MMT/urtheories
//!   (<https://gl.mathhub.info/MMT/urtheories>) at commit
//!   8bc91e38df43decdd55b1eda471c4d7b9c75dfdd.
//!
//! No file of either is part of this crate.
//!
//! ## Modules and the parts of the specification they implement
//!
//! - [`syntax`]: delimiters.md, namespaces.md (interpretation instructions),
//!   modules.md (theories, nesting, metadata), declarations.md (constants,
//!   components, includes, rules, metadata); `api/parser/Reader.scala`,
//!   `api/parser/StructureParser.scala`.
//! - [`uri`]: uris.md, namespaces.md; `api/Path.scala`, `api/utils/URI.scala`,
//!   `api/Namespace.scala`.
//! - [`term`]: objects.md; `api/objects/Obj.scala`.
//! - [`notation`]: declarations.md, section Notations; `api/notations/*.scala`.
//! - [`rules`]: declarations.md, section Rules; literals.md; the rules that
//!   change reading (`api/symbols/RuleConstant.scala`,
//!   `api/parser/LexerExtension.scala`, `api/uom/StandardLiterals.scala`).
//! - [`library`]: modules.md (scope of a declaration, meta-theories,
//!   includes, nested theories), implicit.md (includes compose
//!   transitively); the object reader (`api/parser/Scanner.scala`,
//!   `ActiveNotation.scala`, `NotationBasedParser.scala`,
//!   `api/notations/NotationExtension.scala`, `Pragmatics.scala`) and the
//!   printer, its inverse ([`Library::print_theories`], [`ObjectScope::print`]).
//! - [`archive`]: namespaces.md (documents and narration bases);
//!   `api/archives/Archive.scala`, `api/utils/File.scala`.
//! - [`error`]: errors as values, with positions `line:column`.
//!
//! ## The supported subset
//!
//! Supported:
//!
//! - Documents with the instructions `namespace` (absolute or relative),
//!   `import PREFIX URI`, `fixmeta URI` and `rule URI` (a document rule; only
//!   its lexer extension has an effect, as in MMT); comments `//` and opaque
//!   text `/T`; the four delimiters in Unicode and ASCII.
//! - Theories with an optional meta-theory, nested theories, `include` of a
//!   named theory (transitively, with cycle detection), `rule` declarations,
//!   `meta` and `tag` metadata.
//! - Constants with the components type `:`, definiens `=`, notation `#`,
//!   presentation notation `##` (kept, not used), aliases `@`, `role`,
//!   `meta`, `tag` and comments; the keyword `constant`.
//! - MMT URIs and CURIEs, resolved as `Path.parse` resolves them; name
//!   resolution of single names over the visible theories.
//! - Objects: symbols, modules, variables, applications, bindings with typed
//!   or defined variables, and literals. Reading by the notations in scope
//!   (mixfix notations with arguments, sequence arguments, implicit
//!   arguments, bound variables and variable sequences, `%n`, `%iD`, `%D`,
//!   `%R`, `%w`, precedences, `meta`), default application, qualified
//!   identifiers with MMT's heuristics, `_` holes, free variables, and LF's
//!   higher-order abstract syntax (the rule `LFHOAS`).
//! - Literals through rules: `Realize` of a type with `StandardString`,
//!   `StandardInt`, `StandardNat`, `StandardPositive` or `StandardBool`;
//!   `StandardStringInterpolation`; `MMTURILexer` (`☞URI`);
//!   `NotationRealizedType` (`nt"…"`). Integers have any size; the crate
//!   does no arithmetic.
//! - Archives: the manifest, the sources below `source`, dependencies, and
//!   elaboration in dependency order across files and archives.
//! - Printing of objects and theories, checked by reading back.
//!
//! Rejected with an error of kind [`ErrorKind::Unsupported`]: views,
//! morphisms, structures, implicit and total links, `realize`, defined
//! includes and includes of non-theories, theory parameters and defined
//! theories, `document` and `ref`, sections, derived declarations, patterns
//! and instances, `link` and narrative metadata, opaque formats other than
//! `/T`, component URIs, label arguments (OML) in notations, arguments
//! before bound variables in notations, `%L` and `%%fixity` notations,
//! notations of bound variables, ambiguous notations (MMT's `oneOf` terms,
//! resolved by type checking), and the lexer extensions listed in [`rules`]
//! that MMT has and this crate does not. Every other rule is accepted and
//! has no effect on reading.
//!
//! ## Limits and robustness
//!
//! Reading and printing never panic on any input and never overflow the
//! stack: nesting (of theories in a document, of notations in an object,
//! and the depth of a term added or printed) is bounded by [`Limits`], and
//! text beyond it is an error of kind [`ErrorKind::Limit`]. The default
//! depth is safe on a thread with a 2 MiB stack in an unoptimized build (the
//! default stack of a Rust test thread); the crate spawns no thread. A
//! caller who needs deeper nesting raises the limit and runs the library on
//! a thread with a larger stack. Reading is linear in the length of the text
//! for a fixed set of notations (the scanner of MMT backtracks over open
//! notations, which this crate does as MMT does).

pub mod archive;
pub(crate) mod chars;
pub mod error;
pub(crate) mod lexer;
pub mod library;
pub mod notation;
pub(crate) mod objparser;
pub(crate) mod paths;
pub(crate) mod printer;
pub(crate) mod reader;
pub mod rules;
pub(crate) mod scanner;
pub mod syntax;
pub mod term;
pub mod uri;

pub use archive::{Archive, ArchiveLoad, Manifest};
pub use error::{Error, ErrorKind, Pos, Result};
pub use library::{Constant, Declaration, Elaboration, Library, Metadatum, ObjectScope, RuleDecl, Theory};
pub use notation::Notation;
pub use objparser::ParseResult;
pub use syntax::Document;
pub use term::Term;

/// Limits on the input that this crate reads and the objects it adds and
/// prints, so that deep input is an error of kind [`ErrorKind::Limit`]
/// rather than a stack overflow.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Limits {
    depth: usize,
}

impl Limits {
    /// The default depth: safe on a 2 MiB stack in an unoptimized build
    /// (`tests/limits.rs` proves it), and deeper than any object of
    /// MMT/urtheories.
    pub const DEFAULT_DEPTH: usize = 200;

    /// The same limits with another depth: the largest nesting of theories
    /// in a document, of notations with arguments, default applications and
    /// interpolated strings in an object (brackets are not counted; at most
    /// twice the depth of notations, brackets included, may be open at once
    /// while an object is scanned), and the largest nesting of a term that
    /// is added or printed (a term of [`Term::depth`] `d` nests `d - 1`
    /// levels). Each level costs a few kilobytes of stack in an unoptimized
    /// build; raise it only with a correspondingly larger stack.
    pub fn with_depth(self, depth: usize) -> Limits {
        Limits { depth }
    }

    /// The depth.
    pub fn depth(self) -> usize {
        self.depth
    }

    /// The most notations that may be open at once while an object is
    /// scanned: twice the depth (and two more), so that every printed object
    /// of the allowed depth, with a pair of brackets around each argument,
    /// reads back.
    pub(crate) fn max_open(self) -> usize {
        self.depth.saturating_mul(2).saturating_add(2)
    }
}

impl Default for Limits {
    fn default() -> Limits {
        Limits { depth: Limits::DEFAULT_DEPTH }
    }
}
