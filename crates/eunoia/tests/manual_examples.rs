//! The examples of the Ethos user manual, read verbatim from the manual itself
//! (`user_manual.md` of the Ethos sources at commit
//! 08e4aa40c4f8a6e00833f10e8d8985777e424027, in
//! `.tools/ethos-08e4aa40c4f8a6e00833f10e8d8985777e424027`, which are not part
//! of the repository; see `common`).
//!
//! Every ```` ```smt ```` block of the manual is taken, with its first line
//! number and the heading of its section, and classified here by that line
//! number. A block that is not classified fails the test, so every example is
//! accounted for.
//!
//! - **Notation**: grammar schemas with `...` or `<typed-param>*`, and the type
//!   rules of "Proofs as terms". They are not Eunoia text and must not parse.
//! - **Equations**: the evaluation tables (`term == value`). Their commands
//!   must parse, and each side of each equation must parse as a term and print
//!   back, except the value `#b`: the empty bit-vector has no literal (Ethos
//!   `src/lexer.cpp`: "Error expected bit string").
//! - **Desugarings** of "Proofs as terms": they show what a command means in
//!   terms of `Proof` and `Quote`, which are not symbols of the language. They
//!   must parse and print back.
//! - **Scripts**: everything else. Each must parse and print back to an equal
//!   script. (Whether a fragment is well formed is not this crate's business:
//!   several rely on declarations the manual makes elsewhere, and one, at
//!   line 1803, is a definition the manual says Ethos rejects.)

mod common;

use eunoia::{parse_script, parse_term};

struct Block {
    line: usize,
    section: String,
    text: String,
}

fn blocks() -> Vec<Block> {
    let Some(dir) = common::ethos_sources() else { return Vec::new() };
    let text = std::fs::read_to_string(dir.join("user_manual.md")).unwrap();
    let lines: Vec<&str> = text.lines().collect();
    let mut out = Vec::new();
    let mut section = String::new();
    let mut i = 0;
    while i < lines.len() {
        if lines[i].starts_with('#') {
            section = lines[i].trim_start_matches('#').trim().to_string();
        }
        if lines[i] == "```smt" {
            let start = i + 1;
            let mut j = start;
            while lines[j] != "```" {
                j += 1;
            }
            out.push(Block { line: start + 1, section: section.clone(), text: lines[start..j].join("\n") });
            i = j;
        }
        i += 1;
    }
    out
}

fn block(line: usize) -> Block {
    blocks().into_iter().find(|b| b.line == line).unwrap_or_else(|| panic!("no block at line {line}"))
}

const NOTATION: [usize; 11] = [216, 1193, 1282, 1514, 1650, 1706, 1721, 2184, 2319, 2336, 2346];
const DESUGARINGS: [usize; 4] = [2356, 2362, 2368, 2374];
const EQUATIONS: [usize; 5] = [900, 974, 1068, 1332, 1406];

/// Whether the manual's text is at hand; prints what is missing when not.
fn present() -> bool {
    common::ethos_sources().is_some()
}

#[test]
fn every_block_is_classified() {
    if !present() {
        return;
    }
    let all = blocks();
    assert_eq!(all.len(), 70);
    for b in &all {
        let known = NOTATION.contains(&b.line) || DESUGARINGS.contains(&b.line) || EQUATIONS.contains(&b.line) || is_script(b.line);
        assert!(known, "line {} [{}]", b.line, b.section);
    }
    for l in NOTATION.iter().chain(&DESUGARINGS).chain(&EQUATIONS) {
        block(*l);
    }
}

fn is_script(line: usize) -> bool {
    !NOTATION.contains(&line) && !DESUGARINGS.contains(&line) && !EQUATIONS.contains(&line)
}

#[test]
fn notation_does_not_parse() {
    if !present() {
        return;
    }
    for l in NOTATION {
        let b = block(l);
        assert!(parse_script(&b.text).is_err(), "line {l} [{}]", b.section);
    }
}

#[test]
fn desugarings_parse_and_round_trip() {
    if !present() {
        return;
    }
    for l in DESUGARINGS {
        let b = block(l);
        let s = parse_script(&b.text).unwrap_or_else(|e| panic!("line {l}: {e}"));
        assert_eq!(parse_script(&s.to_string()).unwrap(), s, "line {l}");
    }
}

#[test]
fn scripts_parse_and_round_trip() {
    if !present() {
        return;
    }
    let mut read = 0;
    for b in blocks().into_iter().filter(|b| is_script(b.line)) {
        let s = parse_script(&b.text).unwrap_or_else(|e| panic!("line {} [{}]: {e}", b.line, b.section));
        assert!(!s.is_empty(), "line {}", b.line);
        assert_eq!(parse_script(&s.to_string()).unwrap(), s, "line {}", b.line);
        read += 1;
    }
    assert_eq!(read, 70 - NOTATION.len() - DESUGARINGS.len() - EQUATIONS.len());
}

/// Splits `lhs == rhs ; comment` at the `==` outside strings.
fn equation(line: &str) -> Option<(&str, &str)> {
    let mut in_string = false;
    let bytes = line.as_bytes();
    for i in 0..bytes.len() {
        match bytes[i] {
            b'"' => in_string = !in_string,
            b'=' if !in_string && bytes.get(i + 1) == Some(&b'=') && bytes.get(i.wrapping_sub(1)) == Some(&b' ') => {
                let rhs = &line[i + 2..];
                let mut in_s = false;
                let end = rhs.char_indices().find(|&(_, c)| {
                    if c == '"' {
                        in_s = !in_s;
                    }
                    c == ';' && !in_s
                });
                return Some((line[..i].trim(), end.map_or(rhs, |(k, _)| &rhs[..k]).trim()));
            }
            _ => {}
        }
    }
    None
}

#[test]
fn equations_parse_and_round_trip() {
    if !present() {
        return;
    }
    let mut equations = 0;
    for l in EQUATIONS {
        let b = block(l);
        let mut commands = Vec::new();
        for line in b.text.lines() {
            match equation(line) {
                Some((lhs, rhs)) => {
                    let left = parse_term(lhs).unwrap_or_else(|e| panic!("line {l}: {lhs}: {e}"));
                    assert_eq!(parse_term(&left.to_string()).unwrap(), left);
                    if rhs == "#b" {
                        assert!(parse_term(rhs).is_err());
                    } else {
                        let right = parse_term(rhs).unwrap_or_else(|e| panic!("line {l}: {rhs}: {e}"));
                        assert_eq!(parse_term(&right.to_string()).unwrap(), right);
                    }
                    equations += 1;
                }
                None => commands.push(line),
            }
        }
        let script = parse_script(&commands.join("\n")).unwrap_or_else(|e| panic!("line {l}: {e}"));
        assert_eq!(parse_script(&script.to_string()).unwrap(), script, "line {l} [{}]", b.section);
    }
    assert!(equations > 100, "{equations}");
}
