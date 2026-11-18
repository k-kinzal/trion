//! Reading what cvc5 prints: SMT-LIB responses and CPC proofs.
//!
//! The output of an SMT-LIB solver cannot be read without the commands that
//! produced it (SMT-LIB 2.7 §3.11.1: `(a b)` is an unsat core, unsat
//! assumptions or a proof), so the reader takes the commands, or their
//! [`ResponseKind`]s, and reads one response per command, as
//! [`smtlib::GeneralResponse::parse_session`] does. Two things of cvc5 1.4.2
//! are added to that reading:
//!
//! - a `get-proof` answer under `--proof-format-mode=cpc` is a parenthesized
//!   list of Eunoia commands, which is not SMT-LIB (`eo::` symbols, `:rule`
//!   attributes after a step's name). It is read by `eunoia` instead
//!   ([`eunoia::parse_script_at`], in place, so that its positions are
//!   positions in the whole output);
//! - with `--dump-proofs` ([`SessionOptions::with_dump_proofs`]) cvc5 prints a
//!   proof after every `unsat` answer to `check-sat`, without a `get-proof`.
//!
//! Every other response (`check-sat`, `get-value`, `get-model`, `get-info`,
//! `echo`, `success`, `unsupported`, `(error ...)`) is read by `smtlib`.
//!
//! The output is cut into its top-level S-expressions once, from left to
//! right, and each is read once: the reader takes time linear in the length
//! of the output.

use std::fmt;

use eunoia::{parse_script_at, ParseError, Position, Script};
use smtlib::response::{CheckSatResponse, ResponseKind, SpecificSuccessResponse};
use smtlib::sexpr::read as read_sexpr;
use smtlib::{Command, Dialect, GeneralResponse};

/// How cvc5 was run, as far as it changes what it prints.
///
/// ```
/// let options = cpc::SessionOptions::new().with_dump_proofs(true);
/// assert!(options.dump_proofs() && !options.print_success());
/// ```
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct SessionOptions {
    dump_proofs: bool,
    print_success: bool,
}

impl SessionOptions {
    /// cvc5's defaults: no proof dumping, `:print-success` false.
    pub fn new() -> SessionOptions {
        SessionOptions::default()
    }

    /// `--dump-proofs`: a proof follows every `unsat`.
    pub fn with_dump_proofs(mut self, on: bool) -> SessionOptions {
        self.dump_proofs = on;
        self
    }

    /// `:print-success` (§4.1.7): every command answers, `success` included.
    pub fn with_print_success(mut self, on: bool) -> SessionOptions {
        self.print_success = on;
        self
    }

    /// See [`SessionOptions::with_dump_proofs`].
    pub fn dump_proofs(&self) -> bool {
        self.dump_proofs
    }

    /// See [`SessionOptions::with_print_success`].
    pub fn print_success(&self) -> bool {
        self.print_success
    }
}

/// A CPC proof printed by cvc5: the Eunoia commands between its parentheses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Proof {
    position: Position,
    script: Script,
}

impl Proof {
    /// Where the proof's `(` is in the output.
    pub fn position(&self) -> Position {
        self.position
    }

    /// The commands, with their positions in the output.
    pub fn script(&self) -> &Script {
        &self.script
    }

    /// The commands, consuming the proof.
    pub fn into_script(self) -> Script {
        self.script
    }
}

/// What cvc5 answered to one command.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Response {
    /// An SMT-LIB response.
    Smt(GeneralResponse),
    /// A CPC proof: the answer to `get-proof`, or the proof that
    /// `--dump-proofs` prints after `unsat`.
    Proof(Proof),
}

/// One response, with the command it answers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Answer {
    command: usize,
    position: Position,
    response: Response,
}

impl Answer {
    /// The index, in the commands given to the reader, of the command this answers.
    pub fn command(&self) -> usize {
        self.command
    }

    /// Where the response begins in the output.
    pub fn position(&self) -> Position {
        self.position
    }

    /// The response.
    pub fn response(&self) -> &Response {
        &self.response
    }

    /// The response, consuming the answer.
    pub fn into_response(self) -> Response {
        self.response
    }

    /// The proof, if the response is one.
    pub fn proof(&self) -> Option<&Proof> {
        match &self.response {
            Response::Proof(p) => Some(p),
            Response::Smt(_) => None,
        }
    }

    /// The answer to `check-sat`, if the response is one.
    pub fn check_sat(&self) -> Option<CheckSatResponse> {
        match &self.response {
            Response::Smt(GeneralResponse::Specific(SpecificSuccessResponse::CheckSat(r))) => Some(*r),
            _ => None,
        }
    }
}

/// Output of cvc5 that cannot be read as the responses to the commands.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum OutputError {
    /// Unbalanced parentheses, or an unterminated string or quoted symbol,
    /// in the S-expression that begins here.
    Unbalanced(Position),
    /// The output ends before the response to the command at this index.
    MissingResponse {
        /// The index of the command.
        command: usize,
    },
    /// The output goes on after the response to the last command.
    ExtraResponse(Position),
    /// A response that is not of the kind its command expects; the error's
    /// position is in the whole output.
    Response {
        /// The index of the command.
        command: usize,
        /// What `smtlib` says.
        error: smtlib::Error,
    },
    /// A proof that is not a sequence of Eunoia commands.
    Proof {
        /// The index of the command.
        command: usize,
        /// What `eunoia` says, with a position in the whole output.
        error: ParseError,
    },
}

impl fmt::Display for OutputError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OutputError::Unbalanced(p) => write!(f, "{p}: unbalanced cvc5 output"),
            OutputError::MissingResponse { command } => write!(f, "the output ends before the response to command #{command}"),
            OutputError::ExtraResponse(p) => write!(f, "{p}: more responses than commands"),
            OutputError::Response { command, error } => write!(f, "response to command #{command}: {error}"),
            OutputError::Proof { command, error } => write!(f, "proof for command #{command}: {error}"),
        }
    }
}

impl std::error::Error for OutputError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            OutputError::Response { error, .. } => Some(error),
            OutputError::Proof { error, .. } => Some(error),
            _ => None,
        }
    }
}

/// A top-level S-expression of the output.
#[derive(Debug, Clone, Copy)]
struct Item {
    start: usize,
    end: usize,
    position: Position,
}

/// Cuts a text into its top-level S-expressions, keeping the position.
struct Scanner<'a> {
    bytes: &'a [u8],
    at: usize,
    line: u32,
    column: u32,
}

impl<'a> Scanner<'a> {
    fn new(text: &'a str) -> Scanner<'a> {
        Scanner { bytes: text.as_bytes(), at: 0, line: 1, column: 1 }
    }

    fn position(&self) -> Position {
        Position::new(self.line, self.column)
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.at).copied()
    }

    /// Advances one byte; columns count characters, so only the first byte of
    /// a character moves the column.
    fn bump(&mut self) {
        let Some(b) = self.peek() else { return };
        self.at += 1;
        if b == b'\n' {
            self.line = self.line.saturating_add(1);
            self.column = 1;
        } else if b & 0xC0 != 0x80 {
            self.column = self.column.saturating_add(1);
        }
    }

    fn skip_comment(&mut self) {
        while let Some(b) = self.peek() {
            if b == b'\n' {
                break;
            }
            self.bump();
        }
    }

    /// Skips a string or quoted symbol that starts here.
    fn skip_delimited(&mut self, close: u8, start: Position) -> Result<(), OutputError> {
        self.bump();
        loop {
            match self.peek() {
                None => return Err(OutputError::Unbalanced(start)),
                Some(b) if b == close => {
                    self.bump();
                    if close == b'"' && self.peek() == Some(b'"') {
                        self.bump();
                        continue;
                    }
                    return Ok(());
                }
                Some(_) => self.bump(),
            }
        }
    }

    fn next(&mut self) -> Result<Option<Item>, OutputError> {
        loop {
            match self.peek() {
                None => return Ok(None),
                Some(b' ' | b'\t' | b'\r' | b'\n') => self.bump(),
                Some(b';') => self.skip_comment(),
                Some(_) => break,
            }
        }
        let start = self.at;
        let position = self.position();
        match self.peek() {
            Some(b'(') => {
                let mut depth = 0usize;
                loop {
                    match self.peek() {
                        None => return Err(OutputError::Unbalanced(position)),
                        Some(b'(') => {
                            depth += 1;
                            self.bump();
                        }
                        Some(b')') => {
                            depth = depth.saturating_sub(1);
                            self.bump();
                            if depth == 0 {
                                break;
                            }
                        }
                        Some(b'"') => {
                            let p = self.position();
                            self.skip_delimited(b'"', p)?;
                        }
                        Some(b'|') => {
                            let p = self.position();
                            self.skip_delimited(b'|', p)?;
                        }
                        Some(b';') => self.skip_comment(),
                        Some(_) => self.bump(),
                    }
                }
            }
            Some(b')') => return Err(OutputError::Unbalanced(position)),
            Some(b'"') => self.skip_delimited(b'"', position)?,
            Some(b'|') => self.skip_delimited(b'|', position)?,
            _ => {
                while let Some(b) = self.peek() {
                    if matches!(b, b' ' | b'\t' | b'\r' | b'\n' | b'(' | b')' | b';' | b'"' | b'|') {
                        break;
                    }
                    self.bump();
                }
            }
        }
        Ok(Some(Item { start, end: self.at, position }))
    }
}

/// Whether a parenthesized item holds Eunoia commands: its content, after
/// whitespace and comments, is empty or begins with `(`.
fn is_proof(text: &str, item: Item) -> bool {
    let inner = &text[item.start..item.end];
    let Some(mut rest) = inner.strip_prefix('(') else { return false };
    loop {
        rest = rest.trim_start();
        match rest.strip_prefix(';') {
            Some(comment) => rest = comment.split_once('\n').map_or("", |(_, r)| r),
            None => return rest.starts_with('(') || rest.starts_with(')'),
        }
    }
}

fn shift(p: smtlib::Position, base: Position) -> smtlib::Position {
    if p.line() <= 1 {
        smtlib::Position::new(base.line as usize, p.column() + base.column as usize - 1)
    } else {
        smtlib::Position::new(p.line() + base.line as usize - 1, p.column())
    }
}

fn read_smt(text: &str, item: Item, kind: ResponseKind, dialect: &Dialect, command: usize) -> Result<GeneralResponse, OutputError> {
    read_sexpr(&text[item.start..item.end], dialect).and_then(|node| GeneralResponse::from_spanned_in(&node, kind, dialect)).map_err(|error| {
        let error = match error.position() {
            Some(p) => smtlib::Error::at(error.kind(), shift(p, item.position), error.message()),
            None => error,
        };
        OutputError::Response { command, error }
    })
}

fn read_proof(text: &str, item: Item, command: usize) -> Result<Proof, OutputError> {
    let inner = &text[item.start + 1..item.end - 1];
    let start = Position::new(item.position.line, item.position.column.saturating_add(1));
    let script = parse_script_at(inner, start).map_err(|error| OutputError::Proof { command, error })?;
    Ok(Proof { position: item.position, script })
}

/// Reads the responses that cvc5 printed for commands of the given kinds,
/// in order (see the module documentation).
///
/// ```
/// use cpc::{read_responses, SessionOptions};
/// use cpc::smtlib::response::{CheckSatResponse, ResponseKind};
///
/// let output = "sat\n((x 1))\nunsat\n(\n(assume @p1 false)\n)\n";
/// let kinds = [ResponseKind::CheckSat, ResponseKind::GetValue, ResponseKind::CheckSat];
/// let answers = read_responses(output, &kinds, SessionOptions::new().with_dump_proofs(true))?;
/// assert_eq!(answers[0].check_sat(), Some(CheckSatResponse::Sat));
/// assert_eq!(answers[2].check_sat(), Some(CheckSatResponse::Unsat));
/// let proof = answers[3].proof().unwrap();
/// assert_eq!((answers[3].command(), proof.script().len()), (2, 1));
/// assert_eq!(proof.script().position(0), Some(eunoia::Position::new(5, 1)));
/// # Ok::<(), cpc::OutputError>(())
/// ```
pub fn read_responses(output: &str, kinds: &[ResponseKind], options: SessionOptions) -> Result<Vec<Answer>, OutputError> {
    let dialect = Dialect::strict();
    let mut items = Scanner::new(output);
    let mut out = Vec::new();
    for (command, kind) in kinds.iter().copied().enumerate() {
        if kind == ResponseKind::General && !options.print_success {
            continue;
        }
        let item = items.next()?.ok_or(OutputError::MissingResponse { command })?;
        let response = if kind == ResponseKind::GetProof && is_proof(output, item) { Response::Proof(read_proof(output, item, command)?) } else { Response::Smt(read_smt(output, item, kind, &dialect, command)?) };
        let unsat = matches!(response, Response::Smt(GeneralResponse::Specific(SpecificSuccessResponse::CheckSat(CheckSatResponse::Unsat))));
        out.push(Answer { command, position: item.position, response });
        if unsat && options.dump_proofs {
            let item = items.next()?.ok_or(OutputError::MissingResponse { command })?;
            let response = if is_proof(output, item) { Response::Proof(read_proof(output, item, command)?) } else { Response::Smt(read_smt(output, item, ResponseKind::General, &dialect, command)?) };
            out.push(Answer { command, position: item.position, response });
        }
    }
    if let Some(extra) = items.next()? {
        return Err(OutputError::ExtraResponse(extra.position));
    }
    Ok(out)
}

/// Reads the responses that cvc5 printed for `commands`, in order.
pub fn read_session(output: &str, commands: &[Command], options: SessionOptions) -> Result<Vec<Answer>, OutputError> {
    let kinds: Vec<ResponseKind> = commands.iter().map(ResponseKind::of).collect();
    read_responses(output, &kinds, options)
}

/// The proofs among the responses that cvc5 printed for `commands`, in order.
pub fn read_proofs(output: &str, commands: &[Command], options: SessionOptions) -> Result<Vec<Proof>, OutputError> {
    Ok(read_session(output, commands, options)?
        .into_iter()
        .filter_map(|a| match a.into_response() {
            Response::Proof(p) => Some(p),
            Response::Smt(_) => None,
        })
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kinds(names: &str) -> Vec<ResponseKind> {
        names
            .split_whitespace()
            .map(|n| match n {
                "check-sat" => ResponseKind::CheckSat,
                "get-proof" => ResponseKind::GetProof,
                "get-value" => ResponseKind::GetValue,
                "get-model" => ResponseKind::GetModel,
                "get-info" => ResponseKind::GetInfo,
                "echo" => ResponseKind::Echo,
                _ => ResponseKind::General,
            })
            .collect()
    }

    #[test]
    fn reads_interleaved_responses() {
        let output = "sat\n((x 1) (y (- 2)))\n(\n(define-fun x () Int 1)\n(define-fun y () Int (- 2))\n)\n(:name \"cvc5\")\nunsat\n(\n(assume @p1 false)\n)\n(error \"no \"\"proof\"\"\")\n\"done\"\n";
        let answers = read_responses(output, &kinds("set-option check-sat get-value get-model get-info push check-sat get-proof get-proof echo"), SessionOptions::new()).unwrap();
        assert_eq!(answers.iter().map(Answer::command).collect::<Vec<_>>(), [1, 2, 3, 4, 6, 7, 8, 9]);
        assert!(matches!(answers[1].response(), Response::Smt(GeneralResponse::Specific(SpecificSuccessResponse::GetValue(v))) if v.len() == 2));
        assert!(matches!(answers[2].response(), Response::Smt(GeneralResponse::Specific(SpecificSuccessResponse::GetModel(m))) if m.len() == 2));
        assert!(matches!(answers[3].response(), Response::Smt(GeneralResponse::Specific(SpecificSuccessResponse::GetInfo(_)))));
        let proof = answers[5].proof().unwrap();
        assert_eq!(proof.position(), Position::new(9, 1));
        assert_eq!(proof.script().position(0), Some(Position::new(10, 1)));
        assert!(matches!(answers[6].response(), Response::Smt(GeneralResponse::Error(_))));
        assert!(matches!(answers[7].response(), Response::Smt(GeneralResponse::Specific(SpecificSuccessResponse::Echo(_)))));
    }

    #[test]
    fn a_model_is_not_a_proof() {
        // the answer that the line-oriented reader once took for a proof
        let output = "unsat\n(\n(define-fun x () Int 1)\n)\n";
        let answers = read_responses(output, &kinds("check-sat get-model"), SessionOptions::new()).unwrap();
        assert!(matches!(answers[1].response(), Response::Smt(GeneralResponse::Specific(SpecificSuccessResponse::GetModel(_)))));
        // and as a proof it would not be one: `define-fun` is not a Eunoia command
        let err = read_responses(output, &kinds("check-sat get-proof"), SessionOptions::new()).unwrap_err();
        assert!(matches!(&err, OutputError::Proof { command: 1, error } if error.position == Position::new(3, 2)), "{err}");
    }

    #[test]
    fn skips_delimited_text() {
        let output = "unsat\n(\n(echo \"a ) b\")\n(declare-const |x ) y| Bool) ; ) comment\n)\n";
        let proofs = read_responses(output, &kinds("check-sat"), SessionOptions::new().with_dump_proofs(true)).unwrap();
        assert_eq!(proofs[1].proof().unwrap().script().len(), 2);
    }

    #[test]
    fn refuses_what_does_not_fit_the_commands() {
        let dump = SessionOptions::new().with_dump_proofs(true);
        assert_eq!(read_responses("unsat\n(\n(assume @p1 false)\n", &kinds("check-sat"), dump), Err(OutputError::Unbalanced(Position::new(2, 1))));
        assert_eq!(read_responses("unsat )", &kinds("check-sat"), SessionOptions::new()), Err(OutputError::Unbalanced(Position::new(1, 7))));
        assert_eq!(read_responses("unsat", &kinds("check-sat"), dump), Err(OutputError::MissingResponse { command: 0 }));
        assert_eq!(read_responses("sat sat", &kinds("check-sat"), SessionOptions::new()), Err(OutputError::ExtraResponse(Position::new(1, 5))));
        let err = read_responses("sat\n  (x 1)", &kinds("check-sat get-value"), SessionOptions::new()).unwrap_err();
        assert!(matches!(&err, OutputError::Response { command: 1, error } if error.position().is_some_and(|p| p.line() == 2)), "{err}");
        assert!(matches!(read_responses("(\n(assume)\n)", &kinds("get-proof"), SessionOptions::new()), Err(OutputError::Proof { .. })));
        assert!(matches!(read_responses("(\"abc", &kinds("get-proof"), SessionOptions::new()), Err(OutputError::Unbalanced(_))));
    }

    #[test]
    fn success_is_read_under_print_success() {
        let answers = read_responses("success\nunsat\n", &kinds("set-logic check-sat"), SessionOptions::new().with_print_success(true)).unwrap();
        assert_eq!(answers[0].response(), &Response::Smt(GeneralResponse::Success));
        assert_eq!(answers[1].check_sat(), Some(CheckSatResponse::Unsat));
    }

    #[test]
    fn columns_count_characters() {
        let answers = read_responses("((declare-const |é| Bool)) unsat", &kinds("get-proof check-sat"), SessionOptions::new()).unwrap();
        // `unsat` follows 27 characters (28 bytes)
        assert_eq!(answers[1].position(), Position::new(1, 28));
        assert_eq!(answers[0].proof().unwrap().script().position(0), Some(Position::new(1, 2)));
    }
}
