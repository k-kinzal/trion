//! The structural syntax of `.mmt` files: documents, interpretation
//! instructions, theories and declarations (doc/language/namespaces.md,
//! modules.md, declarations.md), read as `api/parser/StructureParser.scala`
//! (`KeywordBasedParser`) reads them.
//!
//! The structure parser does not parse objects: the components of
//! declarations (types, definitions, notations, rules, include domains) are
//! kept as text, because their meaning depends on the notations in scope,
//! which [`crate::library`] determines when it elaborates a document. The
//! syntax tree here is therefore exact: its `Display` writes text that
//! [`Document::parse`] reads back to an equal tree (source positions are not
//! part of the tree and are ignored by equality).
//!
//! Supported: the instructions `namespace`, `import`, `fixmeta` and `rule`;
//! `theory` with optional meta-theory and a body (also nested in theories);
//! constants (with or without the keyword `constant`) with the components
//! `:` type, `=` definiens, `#` notation, `##` presentation notation, `@`
//! alias, `role`, `meta` and `tag` metadata and `//` comments; `include` of
//! a theory; `rule`; `meta` and `tag` declarations; comments `//` and
//! opaque text `/T` at both levels.
//!
//! Theories nest at most [`crate::Limits::depth`] levels; deeper text is
//! rejected with [`ErrorKind::Limit`].
//!
//! Rejected as unsupported: views and morphisms, structures, `implicit` and
//! `total` links, `realize`, defined includes, theory parameters and defined
//! theories (`>`, `abbrev`, `extends`, `:=`), `document` and `ref`, sections
//! (`#`, `##`, ...), derived declarations and patterns (`instance`,
//! `pattern`), `link` metadata, opaque formats other than `T`, and any other
//! keyword that MMT would hand to a plugin.

use std::fmt;
use std::str::FromStr;

use crate::error::{Error, ErrorKind, Pos, Result};
use crate::reader::{delimiter_level, is_delimiter, Level, Reader};
use crate::Limits;

macro_rules! text_type {
    ($(#[$doc:meta])* $name:ident, $forbidden:expr, $nonempty:expr, $what:expr) => {
        $(#[$doc])*
        #[derive(Clone, Debug)]
        pub struct $name {
            text: String,
            pos: Pos,
        }

        impl $name {
            /// Validates the text against the invariant stated above, so
            /// that it is written and read back as itself.
            pub fn new(text: impl Into<String>) -> Result<$name> {
                $name::at(text, Pos::default())
            }

            /// As `new`, with the source position of the first character.
            pub fn at(text: impl Into<String>, pos: Pos) -> Result<$name> {
                let text = text.into();
                let forbidden: fn(char) -> bool = $forbidden;
                if $nonempty && text.is_empty() {
                    return Err(Error::at(ErrorKind::Syntax, pos, format!("{} may not be empty", $what)));
                }
                if let Some(c) = text.chars().find(|&c| forbidden(c)) {
                    return Err(Error::at(ErrorKind::Syntax, pos, format!("{} may not contain {:?}", $what, c)));
                }
                if text.starts_with(crate::reader::is_ws) || text.ends_with(crate::reader::is_ws) {
                    return Err(Error::at(ErrorKind::Syntax, pos, format!("{} may not start or end with whitespace", $what)));
                }
                if text.contains('\r') {
                    return Err(Error::at(ErrorKind::Syntax, pos, format!("{} may not contain a carriage return, which MMT reads as a line break", $what)));
                }
                Ok($name { text, pos })
            }

            /// The text.
            pub fn as_str(&self) -> &str {
                &self.text
            }

            /// The source position of the first character (the default position if built by hand).
            pub fn pos(&self) -> Pos {
                self.pos
            }
        }

        impl PartialEq for $name {
            fn eq(&self, other: &$name) -> bool {
                self.text == other.text
            }
        }
        impl Eq for $name {}

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(&self.text)
            }
        }
    };
}

text_type!(
    /// The text of one component of a declaration: it contains no
    /// delimiter and no carriage return, and neither starts nor ends with
    /// whitespace. It may be empty.
    ObjectText,
    |c| is_delimiter(c),
    false,
    "the text of a component"
);
text_type!(
    /// The text of a declaration-level comment: it contains no ❙, ❚ and
    /// no carriage return, and neither starts nor ends with whitespace. It
    /// may be empty.
    DeclText,
    |c| matches!(delimiter_level(c), Some(l) if l >= Level::Declaration),
    false,
    "the text of a declaration"
);
text_type!(
    /// The text of a document-level comment or instruction: it contains no
    /// ❚ and no carriage return, and neither starts nor ends with
    /// whitespace. It may be empty.
    ModuleText,
    |c| matches!(delimiter_level(c), Some(l) if l >= Level::Module),
    false,
    "the text of a module-level item"
);
text_type!(
    /// A word: a non-empty name or URI reference without whitespace or delimiters.
    Word,
    |c| is_delimiter(c) || crate::chars::is_java_whitespace(c),
    true,
    "a name"
);

impl Word {
    fn checked(text: String, pos: Pos, what: &str) -> Result<Word> {
        if text.is_empty() {
            return Err(Error::at(ErrorKind::Syntax, pos, format!("{what} expected")));
        }
        Word::at(text, pos)
    }
}

/// A document: the contents of one `.mmt` file.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Document {
    /// The items in order.
    pub items: Vec<DocItem>,
}

/// An item of a document.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum DocItem {
    /// `namespace URI❚`: sets the namespace of the following modules.
    Namespace(Word),
    /// `import PREFIX URI❚`: defines a CURIE prefix.
    Import {
        /// The prefix.
        prefix: Word,
        /// The URI reference it stands for.
        uri: Word,
    },
    /// `fixmeta URI❚`: the default meta-theory of the following theories.
    FixMeta(Word),
    /// `rule URI❚`: a rule for the rest of the document.
    Rule(Word),
    /// `// text❚`: a comment.
    Comment(ModuleText),
    /// `/T text❚`: informal text.
    Text(ModuleText),
    /// A theory.
    Theory(TheoryItem),
}

/// A theory: `theory NAME : META = BODY ❚`.
///
/// Printing and dropping do not recurse, so theories nested to any depth are
/// written and dropped on any stack.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoryItem {
    /// The name, as written.
    pub name: Word,
    /// The meta-theory reference, as written.
    pub meta: Option<Word>,
    /// The declarations of the body.
    pub body: Vec<Decl>,
}

/// A declaration in a theory.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Decl {
    /// A constant.
    Constant(ConstantItem),
    /// `include DOMAIN❙`.
    Include(ObjectText),
    /// `rule RULE ARGS❙`.
    Rule(ObjectText),
    /// A nested theory.
    Theory(TheoryItem),
    /// `meta KEY VALUE❙`: metadata of the theory.
    Meta {
        /// The key, a symbol reference.
        key: Word,
        /// The value, an object.
        value: ObjectText,
    },
    /// `tag KEY❙`.
    Tag(Word),
    /// `// text❙`.
    Comment(DeclText),
    /// `/T text❙`.
    Text(DeclText),
}

/// A constant declaration: a name and its components, with at most one
/// type, definiens, notation and presentation notation (as the reader
/// requires).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstantItem {
    name: Word,
    components: Vec<Component>,
}

impl ConstantItem {
    /// A constant; an error if a type, definiens, notation or presentation
    /// notation occurs twice.
    pub fn new(name: Word, components: Vec<Component>) -> Result<ConstantItem> {
        let mut seen = [false; 4];
        for c in &components {
            let (i, what) = match c {
                Component::Type(_) => (0, "type"),
                Component::Definiens(_) => (1, "definiens"),
                Component::Notation(_) => (2, "notation"),
                Component::PresentationNotation(_) => (3, "presentation notation"),
                _ => continue,
            };
            if std::mem::replace(&mut seen[i], true) {
                return Err(Error::at(ErrorKind::Structure, name.pos(), format!("{what} of the constant {name} given twice")));
            }
        }
        Ok(ConstantItem { name, components })
    }

    /// The name, as written.
    pub fn name(&self) -> &Word {
        &self.name
    }

    /// The components in order.
    pub fn components(&self) -> &[Component] {
        &self.components
    }
}

/// A component of a constant declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Component {
    /// `: TYPE`.
    Type(ObjectText),
    /// `= DEFINIENS`.
    Definiens(ObjectText),
    /// `# NOTATION`.
    Notation(ObjectText),
    /// `## NOTATION`, used only for presentation.
    PresentationNotation(ObjectText),
    /// `@ ALIAS`.
    Alias(ObjectText),
    /// `role ROLE`.
    Role(ObjectText),
    /// `meta KEY VALUE`.
    Meta {
        /// The key.
        key: Word,
        /// The value.
        value: ObjectText,
    },
    /// `tag KEY`.
    Tag(Word),
    /// `// text`.
    Comment(ObjectText),
}

/// The keywords that the structure parser does not read as constant names.
const MODULE_KEYWORDS: &[&str] = &[
    "constant", "include", "realize", "structure", "theory", "view", "morphism", "implicit", "total", "instance", "pattern", "rule", "//", "/", "meta",
    "tag", "link",
];

fn unsupported(pos: Pos, what: impl fmt::Display) -> Error {
    Error::at(ErrorKind::Unsupported, pos, format!("{what} are not supported"))
}

fn syntax(pos: Pos, what: impl Into<String>) -> Error {
    Error::at(ErrorKind::Syntax, pos, what)
}

impl Document {
    /// Reads a document with the default limits.
    ///
    /// ```
    /// use mmt::syntax::{Decl, DocItem};
    ///
    /// let doc = mmt::Document::parse("theory T =\n  c : type ❘ # C❙\n❚")?;
    /// let DocItem::Theory(t) = &doc.items[0] else { unreachable!() };
    /// let Decl::Constant(c) = &t.body[0] else { unreachable!() };
    /// assert_eq!(c.name().as_str(), "c");
    /// assert_eq!(doc.to_string().parse::<mmt::Document>()?, doc);
    ///
    /// let e = mmt::Document::parse("theory T = c ❘ = x❙❚").unwrap_err();
    /// assert_eq!(e.to_string(), "1:14: syntax error: expected ':', '=', '#', '##', '@', 'role', found nothing (note that 'c' was treated as a constant name)");
    /// # Ok::<(), mmt::Error>(())
    /// ```
    pub fn parse(text: &str) -> Result<Document> {
        Document::parse_with_limits(text, Limits::default())
    }

    /// Reads a document; theories nest at most `limits.depth()` levels.
    pub fn parse_with_limits(text: &str, limits: Limits) -> Result<Document> {
        let mut r = Reader::new(text);
        let mut items = Vec::new();
        loop {
            if r.end_of_document() {
                break;
            }
            let (kw, pos) = r.read_token();
            match kw.as_str() {
                "" => {
                    if r.end_of_document() {
                        break;
                    }
                    return Err(syntax(pos, "keyword expected"));
                }
                "document" | "ref" => return Err(unsupported(pos, format!("'{kw}' declarations"))),
                "view" | "morphism" | "implicit" => return Err(unsupported(pos, "views")),
                "/" => {
                    let (format, fpos) = r.read_token();
                    if format != "T" {
                        return Err(Error::at(ErrorKind::Unsupported, fpos, format!("opaque format '{format}' is not supported (only /T)")));
                    }
                    let (t, tpos) = r.read_module();
                    items.push(DocItem::Text(ModuleText::at(t, tpos)?));
                }
                "//" => {
                    let (t, tpos) = r.read_module();
                    items.push(DocItem::Comment(ModuleText::at(t, tpos)?));
                }
                "namespace" | "import" | "fixmeta" | "rule" => {
                    let (t, tpos) = r.read_module();
                    let parts: Vec<&str> = t.split(crate::chars::is_java_whitespace).filter(|s| !s.is_empty()).collect();
                    let word = |s: &str| Word::at(s, tpos);
                    let item = match (kw.as_str(), parts.as_slice()) {
                        ("namespace", [u]) => DocItem::Namespace(word(u)?),
                        ("import", [p, u]) => DocItem::Import { prefix: word(p)?, uri: word(u)? },
                        ("fixmeta", [u]) => DocItem::FixMeta(word(u)?),
                        ("rule", [u]) => DocItem::Rule(word(u)?),
                        _ => return Err(syntax(pos, format!("unknown interpretation instruction: {kw} {t}"))),
                    };
                    items.push(item);
                }
                "theory" => items.push(DocItem::Theory(read_theory(&mut r, 1, limits)?)),
                k => return Err(Error::at(ErrorKind::Unsupported, pos, format!("unknown or unsupported keyword at document level: {k}"))),
            }
            if !r.end_of_module() {
                let (rest, p) = r.read_module();
                if !rest.is_empty() {
                    return Err(syntax(p, format!("extraneous tokens: {rest}")));
                }
            }
        }
        Ok(Document { items })
    }

}

impl FromStr for Document {
    type Err = Error;

    /// As [`Document::parse`].
    fn from_str(s: &str) -> Result<Document> {
        Document::parse(s)
    }
}

fn read_theory(r: &mut Reader, depth: usize, limits: Limits) -> Result<TheoryItem> {
    let (name, npos) = r.read_to_space();
    if depth > limits.depth() {
        return Err(Error::at(ErrorKind::Limit, npos, format!("theories nest more than {} levels", limits.depth())));
    }
    let name = Word::checked(name, npos, "name")?;
    let (mut delim, mut dpos) = r.read_token();
    let mut meta = None;
    if delim == ":" {
        let (m, mpos) = r.read_to_space();
        meta = Some(Word::checked(m, mpos, "MMT URI")?);
        (delim, dpos) = r.read_token();
    }
    match delim.as_str() {
        ">" => return Err(unsupported(dpos, "theory parameters")),
        "abbrev" | "extends" | ":=" => return Err(unsupported(dpos, "defined theories")),
        "=" => {}
        _ => return Err(syntax(dpos, "':' or '=' or 'abbrev' expected")),
    }
    let body = read_in_module(r, depth, limits)?;
    Ok(TheoryItem { name, meta, body })
}

fn read_in_module(r: &mut Reader, depth: usize, limits: Limits) -> Result<Vec<Decl>> {
    let mut body = Vec::new();
    loop {
        let (kw, pos) = r.read_token();
        match kw.as_str() {
            "" => {
                if r.end_of_module() {
                    return Ok(body);
                }
                return Err(syntax(pos, "keyword expected"));
            }
            "constant" => {
                let (name, npos) = r.read_to_space();
                let name = Word::checked(name, npos, "name")?;
                body.push(Decl::Constant(read_constant(r, name)?));
            }
            "include" => {
                let (t, tpos) = r.read_object();
                if !r.end_of_declaration() {
                    return Err(unsupported(pos, "defined includes"));
                }
                body.push(Decl::Include(ObjectText::at(t, tpos)?));
            }
            "realize" => return Err(unsupported(pos, "realizations")),
            "structure" | "implicit" | "total" => return Err(unsupported(pos, "structures and implicit links")),
            "view" | "morphism" => return Err(unsupported(pos, "views")),
            "instance" | "pattern" => return Err(unsupported(pos, "patterns and instances")),
            "link" => return Err(unsupported(pos, "link metadata")),
            k if k.chars().all(|c| c == '#') => return Err(unsupported(pos, "sections")),
            k if k.starts_with("@_") => return Err(unsupported(pos, "narrative metadata")),
            "theory" => body.push(Decl::Theory(read_theory(r, depth + 1, limits)?)),
            "/" => {
                let (format, fpos) = r.read_token();
                if format != "T" {
                    return Err(Error::at(ErrorKind::Unsupported, fpos, format!("opaque format '{format}' is not supported (only /T)")));
                }
                let (t, tpos) = r.read_declaration();
                body.push(Decl::Text(DeclText::at(t, tpos)?));
            }
            "//" => {
                let (t, tpos) = r.read_declaration();
                body.push(Decl::Comment(DeclText::at(t, tpos)?));
            }
            "rule" => {
                let (t, tpos) = r.read_declaration();
                if t.chars().any(|c| delimiter_level(c).is_some()) {
                    return Err(syntax(tpos, "a rule is one object; the text after ❘ would be ignored by MMT"));
                }
                body.push(Decl::Rule(ObjectText::at(t, tpos)?));
            }
            "meta" | "tag" => {
                let (t, tpos) = r.read_declaration();
                let mut sub = Reader::at(&t, tpos);
                body.push(read_metadatum(&kw, &mut sub, tpos)?.into_decl());
            }
            k => {
                let name = Word::checked(k.to_string(), pos, "name")?;
                body.push(Decl::Constant(read_constant(r, name)?));
            }
        }
        if !r.end_of_declaration() {
            let (rest, p) = r.read_declaration();
            if !rest.is_empty() {
                return Err(syntax(p, format!("end of declaration expected, found: {rest}")));
            }
        }
    }
}

enum Metadatum {
    Meta(Word, ObjectText),
    Tag(Word),
}

impl Metadatum {
    fn into_decl(self) -> Decl {
        match self {
            Metadatum::Meta(key, value) => Decl::Meta { key, value },
            Metadatum::Tag(key) => Decl::Tag(key),
        }
    }
    fn into_component(self) -> Component {
        match self {
            Metadatum::Meta(key, value) => Component::Meta { key, value },
            Metadatum::Tag(key) => Component::Tag(key),
        }
    }
}

/// Reads `KEY VALUE` (meta) or `KEY` (tag) from a sub-reader over the whole text (`MetadataParser`).
fn read_metadatum(kw: &str, sub: &mut Reader, pos: Pos) -> Result<Metadatum> {
    let (key, kpos) = sub.read_to_space();
    let key = Word::checked(key, kpos, "metadata key")?;
    let md = if kw == "meta" {
        let (v, vpos) = sub.read_object();
        if !sub.end_of_input() {
            return Err(syntax(pos, "a metadatum value is one object"));
        }
        Metadatum::Meta(key, ObjectText::at(v, vpos)?)
    } else {
        if !sub.end_of_input() {
            let (rest, rpos) = sub.read_object();
            if !rest.is_empty() || !sub.end_of_input() {
                return Err(syntax(rpos, "a tag has only a key"));
            }
        }
        Metadatum::Tag(key)
    };
    Ok(md)
}

fn read_constant(r: &mut Reader, name: Word) -> Result<ConstantItem> {
    let mut components = Vec::new();
    let (mut has_tp, mut has_df, mut has_nt, mut has_pnt) = (false, false, false, false);
    while !r.end_of_declaration() {
        let (delim, pos) = r.read_token();
        let once = |flag: &mut bool, what: &str| -> Result<()> {
            if *flag {
                return Err(Error::at(ErrorKind::Structure, pos, format!("{what} of this constant already given")));
            }
            *flag = true;
            Ok(())
        };
        let comp = match delim.as_str() {
            ":" => {
                once(&mut has_tp, "type")?;
                let (t, p) = r.read_object();
                Component::Type(ObjectText::at(t, p)?)
            }
            "=" => {
                once(&mut has_df, "definiens")?;
                let (t, p) = r.read_object();
                Component::Definiens(ObjectText::at(t, p)?)
            }
            "#" => {
                once(&mut has_nt, "notation")?;
                let (t, p) = r.read_object();
                Component::Notation(ObjectText::at(t, p)?)
            }
            "##" => {
                once(&mut has_pnt, "presentation notation")?;
                let (t, p) = r.read_object();
                Component::PresentationNotation(ObjectText::at(t, p)?)
            }
            "@" => {
                let (t, p) = r.read_object();
                Component::Alias(ObjectText::at(t, p)?)
            }
            "role" => {
                let (t, p) = r.read_object();
                Component::Role(ObjectText::at(t, p)?)
            }
            "//" => {
                let (t, p) = r.read_object();
                Component::Comment(ObjectText::at(t, p)?)
            }
            "meta" | "tag" => {
                let (t, p) = r.read_object();
                let mut sub = Reader::at(&t, p);
                read_metadatum(&delim, &mut sub, p)?.into_component()
            }
            "link" => return Err(unsupported(pos, "link metadata")),
            "" => {
                if r.end_of_declaration() {
                    break;
                }
                return Err(syntax(pos, format!("expected ':', '=', '#', '##', '@', 'role', found nothing (note that '{name}' was treated as a constant name)")));
            }
            k => return Err(syntax(pos, format!("expected ':', '=', '#', '##', '@', 'role', found {k} (note that '{name}' was treated as a constant name because it is not a keyword)"))),
        };
        components.push(comp);
    }
    Ok(ConstantItem { name, components })
}

/// Whether `name` is read back by the module-level token reader as itself and
/// is not a keyword, so that it can be written without the keyword `constant`.
fn is_plain_constant_name(name: &str) -> bool {
    if MODULE_KEYWORDS.contains(&name) || name.chars().all(|c| c == '#') || name.starts_with("@_") {
        return false;
    }
    // the name is followed by a space or a delimiter when printed; a connector at its end would join them (`TokenList.canFollow`)
    let followed = format!("{name}❙");
    let mut r = Reader::new(&followed);
    let (t, _) = r.read_token();
    t == name
}

impl fmt::Display for Document {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for item in &self.items {
            match item {
                DocItem::Namespace(u) => writeln!(f, "namespace {u}❚")?,
                DocItem::Import { prefix, uri } => writeln!(f, "import {prefix} {uri}❚")?,
                DocItem::FixMeta(u) => writeln!(f, "fixmeta {u}❚")?,
                DocItem::Rule(u) => writeln!(f, "rule {u}❚")?,
                DocItem::Comment(t) => writeln!(f, "// {t}❚")?,
                DocItem::Text(t) => writeln!(f, "/T {t}❚")?,
                DocItem::Theory(t) => write_theory(f, t, 0)?,
            }
        }
        Ok(())
    }
}

impl Drop for TheoryItem {
    fn drop(&mut self) {
        let mut stack: Vec<Decl> = std::mem::take(&mut self.body);
        while let Some(d) = stack.pop() {
            if let Decl::Theory(mut t) = d {
                stack.append(&mut t.body);
            }
        }
    }
}

/// The deepest indentation: deeper theories are written at this indentation,
/// so that the text stays linear in the size of the document.
const MAX_INDENT: usize = 64;

/// Writes a theory without recursion: nested theories are pushed on a work list.
fn write_theory(f: &mut fmt::Formatter<'_>, t: &TheoryItem, indent: usize) -> fmt::Result {
    enum Work<'a> {
        Open(&'a TheoryItem, usize),
        Decl(&'a Decl, usize),
        Close(usize),
    }
    let mut work = vec![Work::Open(t, indent)];
    while let Some(w) = work.pop() {
        match w {
            Work::Open(t, indent) => {
                let pad = " ".repeat(indent);
                write!(f, "{pad}theory {}", t.name)?;
                if let Some(m) = &t.meta {
                    write!(f, " : {m}")?;
                }
                writeln!(f, " =")?;
                work.push(Work::Close(indent));
                let inner = (indent + 2).min(MAX_INDENT);
                work.extend(t.body.iter().rev().map(|d| Work::Decl(d, inner)));
            }
            Work::Decl(Decl::Theory(t), indent) => work.push(Work::Open(t, indent)),
            Work::Decl(d, indent) => write_decl(f, d, indent)?,
            Work::Close(indent) => writeln!(f, "{}❚", " ".repeat(indent))?,
        }
    }
    Ok(())
}

/// Writes a declaration other than a nested theory.
fn write_decl(f: &mut fmt::Formatter<'_>, d: &Decl, indent: usize) -> fmt::Result {
    let pad = " ".repeat(indent);
    match d {
        Decl::Constant(c) => {
            if is_plain_constant_name(c.name.as_str()) {
                write!(f, "{pad}{}", c.name)?;
            } else {
                write!(f, "{pad}constant {}", c.name)?;
            }
            for (i, comp) in c.components.iter().enumerate() {
                f.write_str(if i == 0 { " " } else { " ❘ " })?;
                match comp {
                    Component::Type(t) => write!(f, ": {t}")?,
                    Component::Definiens(t) => write!(f, "= {t}")?,
                    Component::Notation(t) => write!(f, "# {t}")?,
                    Component::PresentationNotation(t) => write!(f, "## {t}")?,
                    Component::Alias(t) => write!(f, "@ {t}")?,
                    Component::Role(t) => write!(f, "role {t}")?,
                    Component::Meta { key, value } => write!(f, "meta {key} {value}")?,
                    Component::Tag(key) => write!(f, "tag {key}")?,
                    Component::Comment(t) => write!(f, "// {t}")?,
                }
            }
            writeln!(f, "❙")
        }
        Decl::Include(t) => writeln!(f, "{pad}include {t}❙"),
        Decl::Rule(t) => writeln!(f, "{pad}rule {t}❙"),
        Decl::Theory(t) => write_theory(f, t, indent),
        Decl::Meta { key, value } => writeln!(f, "{pad}meta {key} {value}❙"),
        Decl::Tag(key) => writeln!(f, "{pad}tag {key}❙"),
        Decl::Comment(t) => writeln!(f, "{pad}// {t}❙"),
        Decl::Text(t) => writeln!(f, "{pad}/T {t}❙"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_and_writes_a_small_document() {
        let src = "namespace http://a.org❚\nimport ur http://cds.omdoc.org/urtheories❚\ntheory T : ur:?LF =\n  a : type❙\n  f : a ⟶ a ❘ # f 1 prec 3❘ role Simplify❙\n  constant theory # THY❙\n  // a comment ❘ with an object delimiter❙\n❚\n";
        let d = Document::parse(src).unwrap();
        assert_eq!(d.items.len(), 3);
        let printed = d.to_string();
        assert_eq!(Document::parse(&printed).unwrap(), d);
    }

    #[test]
    fn a_module_delimiter_after_a_component_does_not_end_the_theory() {
        // StructureParser.readInModuleAux continues after a declaration that consumed ❚
        let d = Document::parse("theory A =\n c : type❚\ntheory B = d❙❚").unwrap();
        assert_eq!(d.items.len(), 1);
        match &d.items[0] {
            DocItem::Theory(t) => assert!(matches!(t.body[1], Decl::Theory(_))),
            _ => panic!(),
        }
    }

    #[test]
    fn rejects_a_component_without_key() {
        let e = Document::parse("theory A = c ❘ = x❙❚").unwrap_err();
        assert_eq!(e.kind(), ErrorKind::Syntax);
        assert_eq!(e.pos().unwrap().column(), 14);
    }

    #[test]
    fn nesting_beyond_the_limit_is_an_error_not_an_overflow() {
        let n = 100;
        let text = format!("{}{}", "theory T = ".repeat(n), "❚".repeat(n));
        assert!(Document::parse_with_limits(&text, Limits::default().with_depth(n)).is_ok());
        let e = Document::parse_with_limits(&text, Limits::default().with_depth(n - 1)).unwrap_err();
        assert_eq!(e.kind(), ErrorKind::Limit);
    }

    #[test]
    fn deep_theories_built_by_hand_print_and_drop_without_recursion() {
        let mut t = TheoryItem { name: Word::new("T").unwrap(), meta: None, body: vec![] };
        for _ in 0..100_000 {
            t = TheoryItem { name: Word::new("T").unwrap(), meta: None, body: vec![Decl::Theory(t)] };
        }
        let d = Document { items: vec![DocItem::Theory(t)] };
        let run = move || {
            let text = d.to_string();
            assert_eq!(text.matches('❚').count(), 100_001);
            drop(d);
        };
        std::thread::Builder::new().stack_size(256 * 1024).spawn(run).unwrap().join().unwrap();
    }

    #[test]
    fn constants_have_each_main_component_once() {
        let t = || Component::Type(ObjectText::new("a").unwrap());
        assert!(ConstantItem::new(Word::new("c").unwrap(), vec![t()]).is_ok());
        assert_eq!(ConstantItem::new(Word::new("c").unwrap(), vec![t(), t()]).unwrap_err().kind(), ErrorKind::Structure);
    }

    #[test]
    fn words_are_not_empty() {
        assert!(Word::new("").is_err());
        assert!(ObjectText::new("").is_ok());
        assert!(ObjectText::new("a\rb").is_err());
    }
}
