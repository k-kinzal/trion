use crate::{Diagnostic, Mapping, Rejected, Root, Span};
use std::collections::BTreeMap;
use trion_core::{CoreDocument, Expr, Problem, Question, MAX_DEPTH};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TokenKind {
    Name,
    Proposition,
    Assume,
    Entails,
    Satisfiable,
    False,
    True,
    Not,
    And,
    Or,
    Implies,
    If,
    Then,
    Open,
    Close,
    Dot,
    End,
}

#[derive(Clone, Copy)]
struct Token {
    kind: TokenKind,
    span: Span,
}

fn diagnostic(rule: &str, span: Span, reason: impl Into<String>, hint: Option<&str>) -> Diagnostic {
    Diagnostic {
        rule: rule.into(),
        span,
        reason: reason.into(),
        suggestion: hint.map(str::to_owned),
    }
}

fn lex(source: &str) -> Result<Vec<Token>, Rejected> {
    let bytes = source.as_bytes();
    let mut position = 0;
    let mut tokens = Vec::new();
    while position < bytes.len() {
        let start = position;
        let kind = match bytes[position] {
            b' ' | b'\t' | b'\r' | b'\n' => {
                position += 1;
                continue;
            }
            b'(' => TokenKind::Open,
            b')' => TokenKind::Close,
            b'.' => TokenKind::Dot,
            b if b.is_ascii_alphabetic() => {
                position += 1;
                while bytes
                    .get(position)
                    .is_some_and(|b| b.is_ascii_alphanumeric() || *b == b'_')
                {
                    position += 1;
                }
                let word = &source[start..position];
                let span = Span {
                    start,
                    end: position,
                };
                let kind = match word {
                    "proposition" => TokenKind::Proposition,
                    "assume" => TokenKind::Assume,
                    "entails" => TokenKind::Entails,
                    "satisfiable" => TokenKind::Satisfiable,
                    "false" => TokenKind::False,
                    "true" => TokenKind::True,
                    "not" => TokenKind::Not,
                    "and" => TokenKind::And,
                    "or" => TokenKind::Or,
                    "implies" => TokenKind::Implies,
                    "if" => TokenKind::If,
                    "then" => TokenKind::Then,
                    "always" | "eventually" | "next" | "forall" | "exists" | "shall" | "may" => {
                        return Err(unsupported_feature(span, word));
                    }
                    _ => TokenKind::Name,
                };
                tokens.push(Token { kind, span });
                continue;
            }
            b if b.is_ascii_digit() => {
                position += 1;
                while bytes.get(position).is_some_and(u8::is_ascii_digit) {
                    position += 1;
                }
                return Err(unsupported_feature(
                    Span {
                        start,
                        end: position,
                    },
                    &source[start..position],
                ));
            }
            b'+' | b'-' | b'*' | b'/' | b'=' | b'<' | b'>' => {
                return Err(unsupported_feature(
                    Span {
                        start,
                        end: start + 1,
                    },
                    &source[start..start + 1],
                ));
            }
            _ => {
                let character = source[start..].chars().next().unwrap();
                return Err(Rejected::Invalid(diagnostic(
                    "CNL-LEX",
                    Span {
                        start,
                        end: start + character.len_utf8(),
                    },
                    format!("unexpected character {character:?}"),
                    None,
                )));
            }
        };
        position += 1;
        tokens.push(Token {
            kind,
            span: Span {
                start,
                end: position,
            },
        });
    }
    tokens.push(Token {
        kind: TokenKind::End,
        span: Span {
            start: position,
            end: position,
        },
    });
    Ok(tokens)
}

fn unsupported_feature(span: Span, spelling: &str) -> Rejected {
    Rejected::Unsupported(diagnostic(
        "CNL-FEATURE",
        span,
        format!("{spelling:?} is unavailable in this grammar"),
        None,
    ))
}

fn depth_error(span: Span) -> Rejected {
    Rejected::Unsupported(diagnostic(
        "CNL-DEPTH",
        span,
        format!("exchange depth exceeds {MAX_DEPTH}"),
        None,
    ))
}

enum Form {
    Constant(bool),
    Atom(u32),
    Not(Box<Surface>),
    Binary(Token, Box<Surface>, Box<Surface>),
}

struct Surface {
    form: Form,
    span: Span,
    grouped: bool,
}

impl Surface {
    fn new(form: Form, span: Span) -> Self {
        Self {
            form,
            span,
            grouped: false,
        }
    }

    fn binary(operator: Token, left: Surface, right: Surface) -> Self {
        let span = if operator.kind == TokenKind::If {
            Span {
                start: operator.span.start,
                end: right.span.end,
            }
        } else {
            Span {
                start: left.span.start,
                end: right.span.end,
            }
        };
        Self::new(
            Form::Binary(operator, Box::new(left), Box::new(right)),
            span,
        )
    }

    fn lower(
        &self,
        root: Root,
        path: &mut Vec<u8>,
        mappings: &mut Vec<Mapping>,
        remaining: usize,
    ) -> Result<Expr, Rejected> {
        if remaining == 0 {
            return Err(depth_error(self.span));
        }
        let rule = match &self.form {
            Form::Constant(_) => "CNL-CONST",
            Form::Atom(_) => "CNL-NAME",
            Form::Not(_) => "CNL-NOT",
            Form::Binary(operator, ..) => match operator.kind {
                TokenKind::And => "CNL-AND",
                TokenKind::Or => "CNL-OR",
                TokenKind::Implies => "CNL-IMPLIES",
                TokenKind::If => "CNL-IF",
                _ => unreachable!("binary operator is resolved by the parser"),
            },
        };
        let mut rules = vec![rule.into()];
        if self.grouped {
            rules.push("CNL-PARENS".into());
        }
        mappings.push(Mapping {
            root,
            children: path.clone(),
            span: self.span,
            rules,
        });
        Ok(match &self.form {
            Form::Constant(true) => Expr::True,
            Form::Constant(false) => Expr::False,
            Form::Atom(i) => Expr::Atom(*i),
            Form::Not(child) => {
                path.push(0);
                let child = child.lower(root, path, mappings, remaining - 1)?;
                path.pop();
                Expr::Not(Box::new(child))
            }
            Form::Binary(operator, left, right) => {
                path.push(0);
                let left = if matches!(operator.kind, TokenKind::Implies | TokenKind::If) {
                    if remaining == 1 {
                        return Err(depth_error(self.span));
                    }
                    mappings.push(Mapping {
                        root,
                        children: path.clone(),
                        span: operator.span,
                        rules: vec![rule.into()],
                    });
                    path.push(0);
                    let nested = left.lower(root, path, mappings, remaining - 2)?;
                    path.pop();
                    Expr::Not(Box::new(nested))
                } else {
                    left.lower(root, path, mappings, remaining - 1)?
                };
                path.pop();
                path.push(1);
                let right = right.lower(root, path, mappings, remaining - 1)?;
                path.pop();
                if operator.kind == TokenKind::And {
                    Expr::And(Box::new(left), Box::new(right))
                } else {
                    Expr::Or(Box::new(left), Box::new(right))
                }
            }
        })
    }
}

struct Parser<'a> {
    tokens: Vec<Token>,
    cursor: usize,
    source: &'a str,
    slots: BTreeMap<&'a str, u32>,
    ambiguity: Option<Span>,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Token {
        self.tokens[self.cursor]
    }

    fn take(&mut self) -> Token {
        let token = self.peek();
        if token.kind != TokenKind::End {
            self.cursor += 1;
        }
        token
    }

    fn syntax(&self, hint: &str) -> Rejected {
        Rejected::Invalid(diagnostic("CNL-SYNTAX", self.peek().span, hint, None))
    }

    fn expect(&mut self, kind: TokenKind, expected: &str) -> Result<Token, Rejected> {
        if self.peek().kind == kind {
            Ok(self.take())
        } else {
            Err(self.syntax(expected))
        }
    }

    fn expression(&mut self, depth: usize) -> Result<Surface, Rejected> {
        let left = self.unary(depth)?;
        if !matches!(
            self.peek().kind,
            TokenKind::And | TokenKind::Or | TokenKind::Implies
        ) {
            return Ok(left);
        }
        let operator = self.take();
        let right = self.unary(depth)?;
        let mut result = Surface::binary(operator, left, right);
        // Inspect the rest for syntax and name errors. No partial tree is accepted.
        let mut chain = false;
        while matches!(
            self.peek().kind,
            TokenKind::And | TokenKind::Or | TokenKind::Implies
        ) {
            self.take();
            result.span.end = self.unary(depth)?.span.end;
            chain = true;
        }
        if chain {
            self.ambiguity.get_or_insert(result.span);
        }
        Ok(result)
    }

    fn unary(&mut self, depth: usize) -> Result<Surface, Rejected> {
        let token = self.peek();
        if depth == 0 {
            return Err(depth_error(token.span));
        }
        match token.kind {
            TokenKind::Name => {
                self.take();
                let name = &self.source[token.span.start..token.span.end];
                let Some(slot) = self.slots.get(name) else {
                    return Err(Rejected::Invalid(diagnostic(
                        "CNL-UNDECLARED",
                        token.span,
                        format!("{name:?} is not declared"),
                        Some("declare the proposition before the premises"),
                    )));
                };
                Ok(Surface::new(Form::Atom(*slot), token.span))
            }
            TokenKind::False | TokenKind::True => {
                self.take();
                Ok(Surface::new(
                    Form::Constant(token.kind == TokenKind::True),
                    token.span,
                ))
            }
            TokenKind::Not => {
                self.take();
                let child = self.unary(depth - 1)?;
                let span = Span {
                    start: token.span.start,
                    end: child.span.end,
                };
                Ok(Surface::new(Form::Not(Box::new(child)), span))
            }
            TokenKind::If => {
                self.take();
                let left = self.unary(depth - 1)?;
                self.expect(TokenKind::Then, "expected 'then' after the antecedent")?;
                let right = self.unary(depth - 1)?;
                Ok(Surface::binary(token, left, right))
            }
            TokenKind::Open => {
                self.take();
                let mut child = self.expression(depth - 1)?;
                let close = self.expect(TokenKind::Close, "expected ')'")?;
                child.span = Span {
                    start: token.span.start,
                    end: close.span.end,
                };
                child.grouped = true;
                Ok(child)
            }
            _ => Err(self
                .syntax("expected a proposition, constant, negation, or parenthesized expression")),
        }
    }
}

pub(crate) fn document(
    source: &str,
) -> Result<(Problem, Vec<Mapping>), Rejected> {
    let mut parser = Parser {
        tokens: lex(source)?,
        cursor: 0,
        source,
        slots: BTreeMap::new(),
        ambiguity: None,
    };
    let mut declarations = Vec::new();
    let mut mappings = Vec::new();
    while parser.peek().kind == TokenKind::Proposition {
        let start = parser.take().span.start;
        let token = parser.expect(TokenKind::Name, "expected a proposition name")?;
        let name = &source[token.span.start..token.span.end];
        let slot = u32::try_from(declarations.len()).map_err(|_| {
            Rejected::Unsupported(diagnostic(
                "CNL-DECL",
                token.span,
                "too many declarations",
                None,
            ))
        })?;
        if parser.slots.insert(name, slot).is_some() {
            return Err(Rejected::Invalid(diagnostic(
                "CNL-DUPLICATE",
                token.span,
                format!("duplicate declaration {name:?}"),
                Some("keep a single declaration or choose a new name"),
            )));
        }
        declarations.push(name.to_owned());
        let end = parser
            .expect(TokenKind::Dot, "expected '.' after declaration")?
            .span
            .end;
        mappings.push(Mapping {
            root: Root::Declaration(slot as usize),
            children: Vec::new(),
            span: Span { start, end },
            rules: vec!["CNL-DECL".into()],
        });
    }

    let mut pending = Vec::new();
    while parser.peek().kind == TokenKind::Assume {
        parser.take();
        pending.push(parser.expression(MAX_DEPTH)?);
        parser.expect(TokenKind::Dot, "expected '.' after premise")?;
    }
    let start = parser.peek().span.start;
    let goal = match parser.peek().kind {
        TokenKind::Satisfiable => {
            parser.take();
            None
        }
        TokenKind::Entails => {
            parser.take();
            Some(parser.expression(MAX_DEPTH)?)
        }
        _ => return Err(parser.syntax("expected exactly one 'satisfiable' or 'entails' question")),
    };
    let end = parser
        .expect(TokenKind::Dot, "expected '.' after question")?
        .span
        .end;
    parser.expect(TokenKind::End, "the question must end the document")?;
    if let Some(span) = parser.ambiguity {
        return Err(Rejected::Ambiguous(diagnostic(
            "CNL-AMBIGUOUS",
            span,
            "multiple operator associations produce different Core trees",
            Some("parenthesize each nested binary expression"),
        )));
    }
    let premises = pending
        .iter()
        .enumerate()
        .map(|(i, expr)| {
            let index = mappings.len();
            let core = expr.lower(Root::Premise(i), &mut Vec::new(), &mut mappings, MAX_DEPTH)?;
            mappings[index].rules.push("CNL-PREMISE".into());
            Ok(core)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let question = if let Some(goal) = goal {
        let index = mappings.len();
        let core = goal.lower(Root::Question, &mut Vec::new(), &mut mappings, MAX_DEPTH)?;
        mappings[index].rules.push("CNL-QUESTION".into());
        Question::Entails(core)
    } else {
        mappings.push(Mapping {
            root: Root::Question,
            children: Vec::new(),
            span: Span { start, end },
            rules: vec!["CNL-QUESTION".into()],
        });
        Question::Satisfiable
    };
    let problem = CoreDocument::new(declarations, premises)
        .and_then(|doc| Problem::new(doc, question))
        .map_err(|error| {
            Rejected::Invalid(diagnostic(
                "CNL-CORE",
                Span { start: 0, end },
                error.to_string(),
                None,
            ))
        })?;
    Ok((problem, mappings))
}
