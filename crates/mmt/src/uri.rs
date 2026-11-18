//! MMT URIs (doc/language/uris.md) and their resolution against a
//! namespace map (doc/language/namespaces.md).
//!
//! An MMT URI has up to three `?`-separated components: a namespace (a URI
//! without query and fragment), a module name and a local name, the latter
//! two `/`-separated sequences of names. The parsing of URI references and
//! their resolution against a base and a set of CURIE prefixes follows the
//! Scala implementation of MMT v27.0.0, since the documentation does not
//! define them: `api/utils/URI.scala` (URI syntax by the regular expression
//! of RFC 3986 and MMT's own resolution, which differs from java.net.URI),
//! `api/Path.scala` (`Path.parse`, `LocalRef`, `LNStep`) and
//! `api/Namespace.scala` (`NamespaceMap.expand`).
//!
//! Component paths (`CPath`, a fourth `?` component naming a component of a
//! declaration) are rejected as unsupported.

use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::str::FromStr;
use std::sync::Arc;

use crate::error::{Error, ErrorKind, Result};

/// A URI as MMT represents it (`api/utils/URI.scala`): optional scheme and
/// authority, a path given as segments with a flag whether it is absolute,
/// and optional query and fragment.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Uri {
    pub(crate) scheme: Option<String>,
    pub(crate) authority: Option<String>,
    pub(crate) path: Vec<String>,
    pub(crate) absolute: bool,
    pub(crate) query: Option<String>,
    pub(crate) fragment: Option<String>,
}

impl Uri {
    /// Parses a URI reference by the regular expression of RFC 3986, appendix B,
    /// as `URI.apply(String)` does.
    pub fn parse(s: &str) -> Uri {
        let mut rest = s;
        // (([^:/?#]+):)?
        let mut scheme = None;
        if let Some(i) = rest.find([':', '/', '?', '#']) {
            if rest[i..].starts_with(':') && i > 0 {
                scheme = Some(rest[..i].to_string());
                rest = &rest[i + 1..];
            }
        }
        // (//([^/?#]*))?
        let mut authority = None;
        if let Some(r) = rest.strip_prefix("//") {
            let end = r.find(['/', '?', '#']).unwrap_or(r.len());
            authority = Some(r[..end].to_string());
            rest = &r[end..];
        }
        // ([^?#]*)
        let end = rest.find(['?', '#']).unwrap_or(rest.len());
        let jpath = &rest[..end];
        rest = &rest[end..];
        // (\?([^#]*))?
        let mut query = None;
        if let Some(r) = rest.strip_prefix('?') {
            let end = r.find('#').unwrap_or(r.len());
            query = Some(r[..end].to_string());
            rest = &r[end..];
        }
        // (#(.*))?
        let fragment = rest.strip_prefix('#').map(str::to_string);
        let (path_string, absolute) = match jpath.strip_prefix('/') {
            Some(p) => (p, true),
            None => (jpath, false),
        };
        let mut path: Vec<String> = path_string.split('/').map(str::to_string).collect();
        if path == [""] {
            path.clear();
        }
        Uri { scheme, authority, path, absolute, query, fragment }
    }

    /// The URI of a file path: `file:` followed by the components of the
    /// path joined by `/` (a path with a root or a Windows prefix becomes
    /// `file:///…`). Components are not percent-encoded, as MMT's
    /// `File.toURI` does not encode them either.
    pub fn from_file_path(path: &std::path::Path) -> Uri {
        use std::path::Component;
        let mut segments = Vec::new();
        let mut absolute = false;
        for c in path.components() {
            match c {
                Component::Prefix(p) => {
                    absolute = true;
                    segments.push(p.as_os_str().to_string_lossy().replace('\\', "/"));
                }
                Component::RootDir => absolute = true,
                Component::CurDir => {}
                Component::ParentDir => segments.push("..".to_string()),
                Component::Normal(n) => segments.push(n.to_string_lossy().into_owned()),
            }
        }
        Uri { scheme: Some("file".to_string()), authority: absolute.then(String::new), path: segments, absolute, query: None, fragment: None }
    }

    /// The scheme, without the colon.
    pub fn scheme(&self) -> Option<&str> {
        self.scheme.as_deref()
    }

    /// The authority, without the leading `//`.
    pub fn authority(&self) -> Option<&str> {
        self.authority.as_deref()
    }

    /// The path segments.
    pub fn path(&self) -> &[String] {
        &self.path
    }

    /// Whether the path starts with `/`.
    pub fn is_absolute(&self) -> bool {
        self.absolute
    }

    /// The query, without `?`.
    pub fn query(&self) -> Option<&str> {
        self.query.as_deref()
    }

    /// The fragment, without `#`.
    pub fn fragment(&self) -> Option<&str> {
        self.fragment.as_deref()
    }

    /// The path without an empty last segment (which results from a trailing slash).
    pub fn path_no_trailing_slash(&self) -> &[String] {
        match self.path.last() {
            Some(l) if l.is_empty() => &self.path[..self.path.len() - 1],
            _ => &self.path,
        }
    }

    /// Appends segments to the path, dropping query and fragment (`URI./`).
    pub fn slash(&self, segments: &[String]) -> Uri {
        let must_be_abs = !segments.is_empty() && self.authority.is_some();
        let mut path = self.path_no_trailing_slash().to_vec();
        path.extend(segments.iter().cloned());
        Uri { scheme: self.scheme.clone(), authority: self.authority.clone(), path, absolute: self.absolute || must_be_abs, query: None, fragment: None }
    }

    fn merge(p: &[String], q: &[String]) -> Vec<String> {
        let mut joined: Vec<String> = if p.is_empty() { q.to_vec() } else { p[..p.len() - 1].iter().chain(q.iter()).cloned().collect() };
        // dodots
        let mut out: Vec<String> = Vec::new();
        for cur in joined.drain(..) {
            if cur == "." {
            } else if cur == ".." {
                out.pop();
            } else {
                out.push(cur);
            }
        }
        out
    }

    /// Resolves a reference against this URI as `URI.resolve` does.
    pub fn resolve(&self, u: &Uri) -> Uri {
        if u.scheme.is_some() {
            u.clone()
        } else if u.authority.is_some() {
            Uri { scheme: self.scheme.clone(), ..u.clone() }
        } else if u.absolute {
            Uri { scheme: self.scheme.clone(), authority: self.authority.clone(), ..u.clone() }
        } else if !u.path.is_empty() {
            Uri {
                scheme: self.scheme.clone(),
                authority: self.authority.clone(),
                path: Uri::merge(&self.path, &u.path),
                absolute: self.absolute || self.authority.is_some(),
                query: u.query.clone(),
                fragment: u.fragment.clone(),
            }
        } else if u.query.is_some() {
            Uri { query: u.query.clone(), fragment: u.fragment.clone(), ..self.clone() }
        } else if u.fragment.is_some() {
            Uri { fragment: u.fragment.clone(), ..self.clone() }
        } else {
            self.clone()
        }
    }

}

impl FromStr for Uri {
    type Err = std::convert::Infallible;

    /// As [`Uri::parse`]: every string is a URI reference.
    fn from_str(s: &str) -> std::result::Result<Uri, Self::Err> {
        Ok(Uri::parse(s))
    }
}

impl fmt::Display for Uri {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(s) = &self.scheme {
            write!(f, "{s}:")?;
        }
        if let Some(a) = &self.authority {
            write!(f, "//{a}")?;
        }
        if self.absolute {
            write!(f, "/")?;
        }
        write!(f, "{}", self.path.join("/"))?;
        if let Some(q) = &self.query {
            write!(f, "?{q}")?;
        }
        if let Some(fr) = &self.fragment {
            write!(f, "#{fr}")?;
        }
        Ok(())
    }
}

/// Decodes `%XX` escapes in a name segment (`utils.xml.decodeURI`): each
/// escape stands for one UTF-16 code unit.
pub fn decode_name(s: &str) -> Result<String> {
    let mut units: Vec<u16> = Vec::new();
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c == '%' {
            let h: String = chars.by_ref().take(2).collect();
            let v = if h.len() == 2 { u16::from_str_radix(&h, 16).ok() } else { None };
            match v {
                Some(v) => units.push(v),
                None => return Err(Error::new(ErrorKind::Uri, format!("error decoding URI {s}"))),
            }
        } else {
            let mut buf = [0u16; 2];
            units.extend_from_slice(c.encode_utf16(&mut buf));
        }
    }
    String::from_utf16(&units).map_err(|_| Error::new(ErrorKind::Uri, format!("error decoding URI {s}")))
}

/// Encodes a name segment (`utils.xml.encodeURI`): `?`, `/`, `%` and `#` are escaped.
pub fn encode_name(s: &str) -> String {
    let mut out = String::new();
    for c in s.chars() {
        match c {
            '?' => out.push_str("%3F"),
            '/' => out.push_str("%2F"),
            '%' => out.push_str("%25"),
            '#' => out.push_str("%23"),
            c => out.push(c),
        }
    }
    out
}

/// A namespace: an MMT document path, given by a URI without query and fragment.
///
/// Equality follows `DPath.equals` of MMT: the scheme is ignored, an absent
/// and an empty authority are equal, and a trailing slash is ignored. The
/// comparisons are derived from one normal form computed at construction (the
/// authority, whether the path is absolute, and the path without a trailing
/// empty segment), so that equality is an equivalence and `Hash` and `Ord`
/// agree with it. The URI as given is kept for display. A namespace is
/// shared, so that cloning it and the names in it is cheap.
#[derive(Clone, Debug)]
pub struct DPath {
    inner: Arc<DPathInner>,
}

#[derive(Debug)]
struct DPathInner {
    uri: Uri,
    key: (String, bool, Vec<String>),
}

impl DPath {
    /// The namespace of a URI; fails if it has a query or a fragment.
    pub fn new(uri: Uri) -> Result<DPath> {
        if uri.query.is_some() || uri.fragment.is_some() {
            return Err(Error::new(ErrorKind::Uri, format!("MMT namespace URI may not have query or fragment: {uri}")));
        }
        let path = uri.path_no_trailing_slash().to_vec();
        let absolute = !path.is_empty() && (uri.absolute || uri.authority.is_some());
        let key = (uri.authority.clone().unwrap_or_default(), absolute, path);
        Ok(DPath { inner: Arc::new(DPathInner { uri, key }) })
    }

    /// The URI of this namespace.
    pub fn uri(&self) -> &Uri {
        &self.inner.uri
    }

    fn key(&self) -> &(String, bool, Vec<String>) {
        &self.inner.key
    }

    /// The module of this name in this namespace.
    pub fn module(&self, name: LocalName) -> MPath {
        MPath { doc: self.clone(), name }
    }

    /// Appends segments to this namespace.
    pub fn slash(&self, segments: &[String]) -> DPath {
        let uri = self.uri().slash(segments);
        // `slash` drops query and fragment, which a namespace has not
        DPath::new(uri).unwrap_or_else(|_| unreachable!("a namespace without query and fragment"))
    }
}

impl TryFrom<Uri> for DPath {
    type Error = Error;

    fn try_from(uri: Uri) -> Result<DPath> {
        DPath::new(uri)
    }
}

impl FromStr for DPath {
    type Err = Error;

    /// Reads an absolute namespace URI (no CURIEs, no resolution).
    fn from_str(s: &str) -> Result<DPath> {
        DPath::new(Uri::parse(s))
    }
}

impl PartialEq for DPath {
    fn eq(&self, that: &DPath) -> bool {
        Arc::ptr_eq(&self.inner, &that.inner) || self.key() == that.key()
    }
}
impl Eq for DPath {}
impl Hash for DPath {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.key().hash(state);
    }
}
impl PartialOrd for DPath {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for DPath {
    fn cmp(&self, other: &Self) -> Ordering {
        self.key().cmp(other.key())
    }
}

impl fmt::Display for DPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.uri())
    }
}

/// One step of a local name: a simple name, or a complex step naming an
/// unnamed include by the module it includes (`[MPath]`).
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LNStep {
    /// A plain name.
    Simple(String),
    /// The name of an include of the given module.
    Complex(Box<MPath>),
}

impl LNStep {
    /// The machine-oriented form (`LNStep.toPath`).
    pub fn to_path(&self) -> String {
        match self {
            LNStep::Simple(s) => encode_name(s),
            LNStep::Complex(p) => format!("[{p}]"),
        }
    }

    fn parse(s: &str, ns: &NamespaceMap) -> Result<LNStep> {
        if s.len() >= 2 && s.starts_with('[') && s.ends_with(']') {
            let inner = &s[1..s.len() - 1];
            if inner.starts_with('(') && inner.ends_with(')') {
                return Err(Error::new(ErrorKind::Unsupported, format!("complex name steps given as objects are not supported: {s}")));
            }
            Ok(LNStep::Complex(Box::new(Path::parse_module(&decode_name(inner)?, ns)?)))
        } else {
            Ok(LNStep::Simple(decode_name(s)?))
        }
    }
}

impl fmt::Display for LNStep {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_path())
    }
}

/// A local name: a `/`-separated sequence of steps.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct LocalName(Vec<LNStep>);

impl LocalName {
    /// A name of the given steps.
    pub fn new(steps: Vec<LNStep>) -> LocalName {
        LocalName(steps)
    }

    /// The steps.
    pub fn steps(&self) -> &[LNStep] {
        &self.0
    }

    /// A name of one simple step.
    pub fn simple(s: impl Into<String>) -> LocalName {
        LocalName(vec![LNStep::Simple(s.into())])
    }

    /// A name of simple steps.
    pub fn simple_steps<S: Into<String>>(steps: impl IntoIterator<Item = S>) -> LocalName {
        LocalName(steps.into_iter().map(|s| LNStep::Simple(s.into())).collect())
    }

    /// Parses a local name (`LocalName.parse`); complex steps are resolved against `ns`.
    pub fn parse(s: &str, ns: &NamespaceMap) -> Result<LocalName> {
        let r = LocalRef::parse(s)?;
        r.to_local_name(ns)
    }

    /// Parses a local name without namespace map.
    pub fn parse_plain(s: &str) -> Result<LocalName> {
        LocalName::parse(s, &NamespaceMap::empty())
    }

    /// The number of steps.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Whether the name has no steps.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// This name followed by another.
    pub fn join(&self, other: &LocalName) -> LocalName {
        LocalName(self.0.iter().chain(other.0.iter()).cloned().collect())
    }

    /// This name followed by a simple step.
    pub fn child(&self, s: impl Into<String>) -> LocalName {
        let mut v = self.0.clone();
        v.push(LNStep::Simple(s.into()));
        LocalName(v)
    }

    /// The name without complex steps.
    pub fn drop_complex(&self) -> LocalName {
        LocalName(self.0.iter().filter(|s| matches!(s, LNStep::Simple(_))).cloned().collect())
    }

    /// The machine-oriented form (`LocalName.toPath`).
    pub fn to_path(&self) -> String {
        self.0.iter().map(LNStep::to_path).collect::<Vec<_>>().join("/")
    }

    /// The last step as text, if it is simple.
    pub fn last_simple(&self) -> Option<&str> {
        match self.0.last() {
            Some(LNStep::Simple(s)) => Some(s),
            _ => None,
        }
    }

    /// The name without its last step.
    pub fn init(&self) -> LocalName {
        LocalName(self.0[..self.0.len().saturating_sub(1)].to_vec())
    }

    /// The steps after the first `n`.
    pub fn drop_prefix(&self, n: usize) -> LocalName {
        LocalName(self.0[n.min(self.0.len())..].to_vec())
    }
}

impl FromStr for LocalName {
    type Err = Error;

    /// As [`LocalName::parse_plain`].
    fn from_str(s: &str) -> Result<LocalName> {
        LocalName::parse_plain(s)
    }
}

impl fmt::Display for LocalName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_path())
    }
}

/// A possibly relative local name (`LocalRef`): `absolute` is true unless the
/// text starts with `/` (MMT's naming: a leading slash makes the reference
/// relative to the base name).
#[derive(Clone, Debug, PartialEq, Eq)]
struct LocalRef {
    segments: Vec<String>,
    absolute: bool,
}

impl LocalRef {
    fn split_name(s: &str) -> Result<Vec<String>> {
        // port of LocalRef.splitName
        let chars: Vec<char> = s.chars().collect();
        let mut i = 0usize;
        let mut seen: Vec<String> = Vec::new();
        let mut current = String::new();
        loop {
            if i >= chars.len() {
                if !current.is_empty() || !seen.is_empty() {
                    seen.push(std::mem::take(&mut current));
                }
                break;
            }
            let left: String = chars[i..].iter().collect();
            let complex_start = left.starts_with('[') && current.is_empty() && {
                match left.find(']') {
                    Some(p) => left.len() == p + 1 || left[p + 1..].starts_with('/'),
                    None => false,
                }
            };
            if complex_start {
                // complex: copy up to and including the matching ']'
                loop {
                    if i >= chars.len() {
                        return Err(Error::new(ErrorKind::Uri, format!("unclosed '[' in {s}")));
                    }
                    let rest: String = chars[i..].iter().collect();
                    if rest == "]" {
                        current.push(']');
                        i += 1;
                        seen.push(std::mem::take(&mut current));
                        break;
                    } else if rest.starts_with("]/") {
                        current.push(']');
                        seen.push(std::mem::take(&mut current));
                        i += 2;
                        // continue with start; an empty remainder ends
                        if i >= chars.len() {
                            // "a]/" leaves an empty last segment like the Scala code
                            seen.push(String::new());
                            return Ok(seen);
                        }
                        break;
                    } else {
                        current.push(chars[i]);
                        i += 1;
                    }
                }
                if i >= chars.len() {
                    return Ok(seen);
                }
            } else if chars[i] == '/' {
                seen.push(std::mem::take(&mut current));
                i += 1;
                if i >= chars.len() {
                    seen.push(String::new());
                    return Ok(seen);
                }
            } else {
                current.push(chars[i]);
                i += 1;
            }
        }
        Ok(seen)
    }

    fn parse(n: &str) -> Result<LocalRef> {
        let relative = n.starts_with('/');
        let mut l = LocalRef::split_name(n)?;
        if relative && !l.is_empty() {
            l.remove(0);
        }
        Ok(LocalRef { segments: l, absolute: !relative })
    }

    fn to_local_name(&self, ns: &NamespaceMap) -> Result<LocalName> {
        Ok(LocalName(self.segments.iter().map(|s| LNStep::parse(s, ns)).collect::<Result<Vec<_>>>()?))
    }
}

/// The URI of a module: a namespace and a module name.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MPath {
    doc: DPath,
    name: LocalName,
}

impl MPath {
    /// The module of a name in a namespace.
    pub fn new(doc: DPath, name: LocalName) -> MPath {
        MPath { doc, name }
    }

    /// The namespace.
    pub fn doc(&self) -> &DPath {
        &self.doc
    }

    /// The name of the module in the namespace.
    pub fn name(&self) -> &LocalName {
        &self.name
    }

    /// The symbol of this name in this module.
    pub fn symbol(&self, name: LocalName) -> GlobalName {
        GlobalName { module: self.clone(), name }
    }

    /// The symbol of this simple name in this module.
    pub fn sym(&self, name: &str) -> GlobalName {
        self.symbol(LocalName::simple(name))
    }

    /// Parses a module URI without namespace map.
    pub fn parse_plain(s: &str) -> Result<MPath> {
        Path::parse_module(s, &NamespaceMap::empty())
    }
}

impl FromStr for MPath {
    type Err = Error;

    /// As [`MPath::parse_plain`].
    fn from_str(s: &str) -> Result<MPath> {
        MPath::parse_plain(s)
    }
}

impl fmt::Display for MPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}?{}", self.doc, self.name.to_path())
    }
}

/// The URI of a symbol: a module and a local name.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct GlobalName {
    module: MPath,
    name: LocalName,
}

impl GlobalName {
    /// The symbol of a name in a module.
    pub fn new(module: MPath, name: LocalName) -> GlobalName {
        GlobalName { module, name }
    }

    /// The module.
    pub fn module(&self) -> &MPath {
        &self.module
    }

    /// The name in the module.
    pub fn name(&self) -> &LocalName {
        &self.name
    }

    /// Parses a symbol URI without namespace map.
    pub fn parse_plain(s: &str) -> Result<GlobalName> {
        match Path::parse(s, &NamespaceMap::empty())? {
            Path::Symbol(g) => Ok(g),
            p => Err(Error::new(ErrorKind::Uri, format!("symbol path expected: {p}"))),
        }
    }
}

impl FromStr for GlobalName {
    type Err = Error;

    /// As [`GlobalName::parse_plain`].
    fn from_str(s: &str) -> Result<GlobalName> {
        GlobalName::parse_plain(s)
    }
}

impl fmt::Display for GlobalName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}?{}", self.module, self.name.to_path())
    }
}

/// An MMT URI of a namespace, a module or a symbol.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[non_exhaustive]
pub enum Path {
    /// A namespace (document).
    Doc(DPath),
    /// A module.
    Module(MPath),
    /// A symbol.
    Symbol(GlobalName),
}

impl fmt::Display for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Path::Doc(d) => write!(f, "{d}"),
            Path::Module(m) => write!(f, "{m}"),
            Path::Symbol(s) => write!(f, "{s}"),
        }
    }
}

impl Path {
    /// The namespace of this path.
    pub fn doc(&self) -> &DPath {
        match self {
            Path::Doc(d) => d,
            Path::Module(m) => &m.doc,
            Path::Symbol(s) => &s.module.doc,
        }
    }

    /// The components (namespace, module name, local name) of this path.
    fn triple(&self) -> (DPath, Option<LocalName>, Option<LocalName>) {
        match self {
            Path::Doc(d) => (d.clone(), None, None),
            Path::Module(m) => (m.doc.clone(), Some(m.name.clone()), None),
            Path::Symbol(s) => (s.module.doc.clone(), Some(s.module.name.clone()), Some(s.name.clone())),
        }
    }

    /// Splits `uri?mod?name?component` (`Path.split`): `[...]` in the module
    /// and name components may contain `?`.
    fn split(s: &str) -> Result<[String; 4]> {
        let mut comp: [String; 4] = Default::default();
        let mut current = 0usize;
        let chars: Vec<char> = s.chars().collect();
        let mut i = 0usize;
        while i < chars.len() {
            match chars[i] {
                '?' => {
                    if current == 3 {
                        return Err(Error::new(ErrorKind::Uri, format!("MMT-URI may have at most three ?s: {s}")));
                    }
                    current += 1;
                }
                '#' => return Err(Error::new(ErrorKind::Uri, format!("MMT-URI may not have fragment: {s}"))),
                '[' if current == 1 || current == 2 => {
                    match chars[i..].iter().position(|&c| c == ']') {
                        None => comp[current].push('['),
                        Some(p) => {
                            comp[current].extend(chars[i..=i + p].iter());
                            i += p;
                        }
                    }
                }
                c => comp[current].push(c),
            }
            i += 1;
        }
        Ok(comp)
    }

    /// Parses an MMT URI reference and makes it absolute against the namespace
    /// map, as `Path.parse(s, nsMap)` does.
    pub fn parse(s: &str, ns: &NamespaceMap) -> Result<Path> {
        let [d, m, n, c] = Path::split(s)?;
        if !c.is_empty() {
            return Err(Error::new(ErrorKind::Unsupported, format!("component paths are not supported: {s}")));
        }
        let doc = if d.is_empty() { None } else { Some(DPath::new(ns.expand(&Uri::parse(&d)))?) };
        let wrap = |l: LocalRef| if l.segments.is_empty() { None } else { Some(l) };
        let module = wrap(LocalRef::parse(&m)?);
        let name = wrap(LocalRef::parse(&n)?);
        let (bdoc, bmod, bname) = ns.base.triple();
        let merge_n = |bl: &Option<LocalName>, l: &LocalRef| -> Result<LocalName> {
            match bl {
                Some(b) if !l.absolute => Ok(b.join(&l.to_local_name(ns)?)),
                _ => l.to_local_name(ns),
            }
        };
        let merge_d = |d: &DPath| -> Result<DPath> { DPath::new(bdoc.uri().resolve(d.uri())) };
        let path = match (&bmod, &doc, &module, &name) {
            (Some(bm), None, None, Some(n)) => Path::Symbol(bdoc.module(bm.clone()).symbol(merge_n(&bname, n)?)),
            (_, None, Some(m), None) => Path::Module(bdoc.module(merge_n(&bmod, m)?)),
            (_, None, Some(m), Some(n)) => Path::Symbol(bdoc.module(merge_n(&bmod, m)?).symbol(n.to_local_name(ns)?)),
            (_, None, None, None) => ns.base.clone(),
            (_, Some(d), None, None) => Path::Doc(merge_d(d)?),
            (_, Some(d), Some(m), None) => Path::Module(merge_d(d)?.module(m.to_local_name(ns)?)),
            (_, Some(d), Some(m), Some(n)) => Path::Symbol(merge_d(d)?.module(m.to_local_name(ns)?).symbol(n.to_local_name(ns)?)),
            _ => return Err(Error::new(ErrorKind::Uri, format!("{s} cannot be resolved against {}", ns.base))),
        };
        Ok(path)
    }

    /// As [`Path::parse`] but requires a module URI.
    pub fn parse_module(s: &str, ns: &NamespaceMap) -> Result<MPath> {
        match Path::parse(s, ns)? {
            Path::Module(m) => Ok(m),
            p => Err(Error::new(ErrorKind::Uri, format!("module path expected: {p}"))),
        }
    }

    /// As [`Path::parse`] but requires a namespace URI.
    pub fn parse_doc(s: &str, ns: &NamespaceMap) -> Result<DPath> {
        match Path::parse(s, ns)? {
            Path::Doc(d) => Ok(d),
            p => Err(Error::new(ErrorKind::Uri, format!("document path expected: {p}"))),
        }
    }
}

/// The base path and the CURIE prefixes in effect at a point of a document
/// (`api/Namespace.scala`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NamespaceMap {
    base: Path,
    prefixes: Vec<(String, Uri)>,
}

impl NamespaceMap {
    /// The map MMT starts from: base `http://cds.omdoc.org/` (`utils.mmt.mmtbase`), no prefixes.
    pub fn empty() -> NamespaceMap {
        NamespaceMap { base: Path::Doc(DPath::new(Uri::parse("http://cds.omdoc.org/")).unwrap_or_else(|_| unreachable!("a namespace URI"))), prefixes: vec![] }
    }

    /// The base against which relative references are resolved.
    pub fn base(&self) -> &Path {
        &self.base
    }

    /// The prefixes and the URIs they stand for, most recent first.
    pub fn prefixes(&self) -> &[(String, Uri)] {
        &self.prefixes
    }

    /// A map with the given base and no prefixes.
    pub fn with_base(base: Path) -> NamespaceMap {
        NamespaceMap { base, prefixes: vec![] }
    }

    /// The URI of the namespace of the base.
    pub fn default_uri(&self) -> &Uri {
        self.base.doc().uri()
    }

    /// The URI a prefix stands for.
    pub fn get(&self, prefix: &str) -> Option<&Uri> {
        self.prefixes.iter().find(|(p, _)| p == prefix).map(|(_, u)| u)
    }

    /// Defines a prefix; the URI is resolved against the default namespace.
    pub fn add(&self, prefix: &str, uri: &Uri) -> NamespaceMap {
        let mut m = self.clone();
        m.prefixes.insert(0, (prefix.to_string(), self.default_uri().resolve(uri)));
        m
    }

    /// Changes the base.
    pub fn rebase(&self, base: Path) -> NamespaceMap {
        NamespaceMap { base, prefixes: self.prefixes.clone() }
    }

    /// Expands a CURIE `prefix:rest` into a URI if the prefix is known.
    pub fn expand(&self, u: &Uri) -> Uri {
        if let (Some(p), None) = (&u.scheme, &u.authority) {
            if let Some(r) = self.get(p) {
                let rest = Uri { scheme: None, ..u.clone() };
                return Uri::parse(&format!("{r}{rest}"));
            }
        }
        u.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn curie_and_relative_module() {
        let base = Path::Doc(DPath::new(Uri::parse("http://cds.omdoc.org/urtheories")).unwrap());
        let ns = NamespaceMap::with_base(base).add("rules", &Uri::parse("scala://lf.mmt.kwarc.info"));
        assert_eq!(Path::parse("?Typed", &ns).unwrap().to_string(), "http://cds.omdoc.org/urtheories?Typed");
        assert_eq!(Path::parse("rules:?UniverseType", &ns).unwrap().to_string(), "scala://lf.mmt.kwarc.info?UniverseType");
        assert_eq!(Path::parse("rules:/lf?Realize", &ns).unwrap().to_string(), "scala://lf.mmt.kwarc.info/lf?Realize");
        assert_eq!(Path::parse("http://a.org/b?T?c", &ns).unwrap().to_string(), "http://a.org/b?T?c");
    }

    #[test]
    fn scheme_is_ignored_by_namespace_equality() {
        let a = DPath::new(Uri::parse("http://a.org/b/")).unwrap();
        let b = DPath::new(Uri::parse("https://a.org/b")).unwrap();
        assert_eq!(a, b);
        assert_eq!(a.cmp(&b), Ordering::Equal);
    }

    #[test]
    fn namespace_equality_is_symmetric_and_agrees_with_order() {
        // the cases of the review: `file://` and `/`; x == z but x < y < z
        let d = |s: &str| DPath::new(Uri::parse(s)).unwrap();
        assert_eq!(d("file://"), d("/"));
        assert_eq!(d("/"), d("file://"));
        let (x, y, z) = (d("http://a.org/x"), d("http://a.org/y"), d("https://a.org/x"));
        assert_eq!(x, z);
        assert_eq!(x.cmp(&z), Ordering::Equal);
        assert_eq!(x.cmp(&y), z.cmp(&y));
    }

    #[test]
    fn file_uris_of_paths() {
        assert_eq!(Uri::from_file_path(std::path::Path::new("/a/b c")).to_string(), "file:///a/b c");
        assert_eq!(Uri::from_file_path(std::path::Path::new("a/b")).to_string(), "file:a/b");
    }

    #[test]
    fn names_with_complex_steps() {
        let ns = NamespaceMap::empty();
        let n = LocalName::parse("[http://a.org?T]/c", &ns).unwrap();
        assert_eq!(n.len(), 2);
        assert_eq!(n.to_path(), "[http://a.org?T]/c");
    }
}
