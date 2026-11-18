//! The readers are total: any text, random or a valid document mangled by
//! random edits, is read or rejected with an error, never a panic. The
//! printer is total on what the readers produce: whatever reads, prints (or
//! is refused with an error).

mod common;

use std::sync::OnceLock;

use common::*;
use mmt::uri::{MPath, NamespaceMap, Path, Uri};
use mmt::{Document, Library, Notation};
use proptest::prelude::*;

/// A valid document with notations, literals, interpolation, nested theories and metadata.
const VALID: &str = "namespace http://test.org/total❚
import rules scala://mmt.kwarc.info❚
import t http://test.org/total❚
theory M : http://cds.omdoc.org/urtheories?LF =
  str : type❙
  concat : str ⟶ str ⟶ str❙
  rule rules/lf?Realize str rules/api/uom?StandardString❙
  rule rules/literals?StandardStringInterpolation str concat❙
  int : type❙
  rule rules/lf?Realize int rules/api/uom?StandardInt❙
  plus : int ⟶ int ⟶ int ❘ # 1 + 2 prec 10 ❘ role Simplify❙
  neg : int ⟶ int ❘ # - 1 prec 30❙
  all : (int ⟶ str) ⟶ str ❘ # ∀ [ V1T,… ] 2 prec -10000❙
  tup : int ⟶ int ⟶ int ❘ # ⟨ 1 , 2 ⟩❙
  sum : int ⟶ int ❘ # Σ 1,…❙
  c : int ❘ = 1 + - 2 ❘ @ cc❙
  s : str ❘ = s\"a${ \"b\" }c\"❙
  theory N =
    d : str ❘ = ∀ [x : int, y] concat \"x\" \"y\" ❘ meta ?M?c 3❙
  ❚
  tag ?M?c❙
❚
";

/// Characters that matter to the readers: delimiters (Unicode and ASCII), keywords' letters, notation markers, brackets, quotes.
fn alphabet() -> impl Strategy<Value = char> {
    prop_oneof![
        3 => prop::sample::select(vec!['❚', '❙', '❘', '\u{1c}', '\u{1d}', '\u{1e}', '\u{1f}', ' ', '\n', '\r', '\t', '(', ')', '[', ']', '{', '}', '"', '$', '?', '/', ':', '=', '#', '@', '%', '%', '…', ',', '.', '⟨', '⟩', '∀', '-', '+', '☞', '0', '1', '9', 'V', 'T', 'I', 'n', 'D', 'R', 'w', 'L', 's', '_']),
        2 => prop::char::range('a', 'z'),
        1 => any::<char>(),
    ]
}

fn text() -> impl Strategy<Value = String> {
    prop::collection::vec(alphabet(), 0..80).prop_map(|cs| cs.into_iter().collect())
}

/// Random edits of a text: replacing, inserting or deleting characters at random places.
fn mangled(base: &'static str) -> impl Strategy<Value = String> {
    prop::collection::vec((any::<prop::sample::Index>(), 0u8..3, alphabet()), 1..8).prop_map(move |edits| {
        let mut cs: Vec<char> = base.chars().collect();
        for (at, op, c) in edits {
            let i = at.index(cs.len() + 1);
            match op {
                0 if i < cs.len() => cs[i] = c,
                1 => cs.insert(i, c),
                _ if i < cs.len() => {
                    cs.remove(i);
                }
                _ => cs.push(c),
            }
        }
        cs.into_iter().collect()
    })
}

fn library() -> &'static (Library, MPath) {
    static LIB: OnceLock<(Library, MPath)> = OnceLock::new();
    LIB.get_or_init(|| {
        let mut lib = mini_lf();
        let e = lib.add_source(VALID, &base(), None);
        assert!(e.is_ok(), "{}", show(e.errors()));
        (lib, mpath("http://test.org/total?M"))
    })
}

/// Reads a document into a library and prints back what was added.
fn read_and_print(text: &str) {
    let mut lib = mini_lf();
    let e = lib.add_source(text, &base(), None);
    let _ = lib.print_theories(e.theories());
}

/// Notation text built from the characters that markers are made of, so
/// that escapes (`%D`, `%R`, `%i`, `%I`, `%n`, `%w`), numbers, flags and
/// sequence markers (`…`) occur in every position of a marker.
fn marker_text() -> impl Strategy<Value = String> {
    let piece = prop::sample::select(vec!["%", "D", "R", "i", "I", "n", "w", "V", "L", "T", "d", "1", "2", "0", "…", ",", "x", "+", " ", "prec", "meta", "block"]);
    prop::collection::vec(piece, 0..12).prop_map(|v| v.concat())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(cases(1024)))]

    #[test]
    fn notations_of_marker_characters_print_as_they_read(t in marker_text()) {
        let ns = NamespaceMap::empty();
        if let Ok(n) = Notation::parse(&t, &ns) {
            prop_assert_eq!(Notation::parse(&n.to_string(), &ns).ok(), Some(n));
        }
    }

    #[test]
    fn documents_of_random_text_are_read_or_rejected(t in text()) {
        let _ = Document::parse(&t);
        read_and_print(&t);
    }

    #[test]
    fn mangled_documents_are_read_or_rejected(t in mangled(VALID)) {
        if let Ok(d) = Document::parse(&t) {
            prop_assert_eq!(Document::parse(&d.to_string()).ok(), Some(d));
        }
        read_and_print(&t);
    }

    #[test]
    fn objects_of_random_text_are_read_or_rejected_and_what_reads_prints(t in text()) {
        let (lib, m) = library();
        let scope = lib.object_scope(m).unwrap();
        if let Ok(r) = scope.parse(&t) {
            let _ = scope.print(&r);
        }
    }

    #[test]
    fn mangled_objects_are_read_or_rejected_and_what_reads_prints(t in mangled("∀ [x : int, y] concat s\"a${ \"b\" }c\" (- (1 + ⟨ 2 , Σ 3, 4 ⟩)) ☞http://test.org/total?M?c _ X")) {
        let (lib, m) = library();
        let scope = lib.object_scope(m).unwrap();
        if let Ok(r) = scope.parse(&t) {
            let _ = scope.print(&r);
        }
    }

    #[test]
    fn notations_uris_and_names_of_random_text_are_read_or_rejected(t in text()) {
        let ns = NamespaceMap::empty().rebase(Path::parse("http://test.org/a?T", &NamespaceMap::empty()).unwrap());
        if let Ok(n) = Notation::parse(&t, &ns) {
            // what reads, prints so that it reads back
            prop_assert_eq!(Notation::parse(&n.to_string(), &ns).ok(), Some(n));
        }
        let _ = Uri::parse(&t).to_string();
        let _ = Path::parse(&t, &ns);
        let _ = mmt::uri::LocalName::parse(&t, &ns);
    }
}
