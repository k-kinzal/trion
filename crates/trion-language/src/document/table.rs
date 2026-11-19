//! Native tables are document syntax for statements, references and text.

use super::{bracket_list, last_significant, quoted, sentence_spans, Context, Document, Parser};
use serde::Serialize;
use std::collections::BTreeSet;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Table {
    pub title: String,
    pub line: usize,
    pub sections: Vec<String>,
    pub headings: Vec<String>,
    pub rows: Vec<TableRow>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct TableRow {
    pub line: usize,
    pub cells: Vec<TableCell>,
}

impl TableRow {
    pub fn identifier(&self) -> Option<&str> {
        self.cells.iter().find_map(|cell| match cell {
            TableCell::Identifier(id) => Some(id.as_str()),
            _ => None,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum TableCell {
    Text(String),
    Identifier(String),
    Statement(String),
    References(Vec<String>),
}

impl fmt::Display for TableCell {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Text(text) | Self::Statement(text) => f.write_str(text),
            Self::Identifier(id) => write!(f, "[{id}]"),
            Self::References(ids) => {
                for (i, id) in ids.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "[{id}]")?;
                }
                Ok(())
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Role {
    Text,
    Id,
    Statement,
    References,
}

fn heading(text: &str) -> Option<(&str, Role)> {
    let Some((label, annotation)) = text.rsplit_once(" {") else {
        return (!text.is_empty()).then_some((text, Role::Text));
    };
    let role = match annotation.strip_suffix('}')? {
        "id" => Role::Id,
        "statement" => Role::Statement,
        "references" => Role::References,
        _ => return None,
    };
    let label = label.trim();
    (!label.is_empty()).then_some((label, role))
}

/// Split a delimited row and retain the source column of each trimmed cell.
/// A backslash followed by a pipe writes a literal pipe in a cell.
fn cells(text: &str) -> Option<Vec<(usize, String)>> {
    let mut chars = text.strip_prefix('|')?.char_indices().peekable();
    let mut cells = Vec::new();
    let mut start = 1;
    let mut content = String::new();
    while let Some((offset, ch)) = chars.next() {
        match ch {
            '\\' if chars.next_if(|(_, next)| *next == '|').is_some() => content.push('|'),
            '|' => {
                let whitespace = content.len() - content.trim_start().len();
                let column = text[..start + whitespace].chars().count();
                cells.push((column, content.trim().to_string()));
                content.clear();
                start = offset + 2;
            }
            _ => content.push(ch),
        }
    }
    (start == text.len() && !cells.is_empty()).then_some(cells)
}

fn cell(role: Role, text: String) -> Result<TableCell, &'static str> {
    if text.is_empty() {
        return Err("a table cell is empty");
    }
    match role {
        Role::Text => Ok(TableCell::Text(text)),
        Role::Id => match bracket_list(&text).as_deref() {
            Some([id]) => Ok(TableCell::Identifier(id.clone())),
            _ => Err("an id cell holds one stable identifier as `[ID]`"),
        },
        Role::Statement
            if last_significant(&text) == Some('.') && sentence_spans(&text).len() == 1 =>
        {
            Ok(TableCell::Statement(text))
        }
        Role::Statement => Err("a statement cell holds one complete sentence ending in a period"),
        Role::References => bracket_list(&text)
            .map(TableCell::References)
            .ok_or("a references cell holds stable identifiers as `[ID], [ID]`"),
    }
}

impl Parser<'_> {
    pub(super) fn table(&mut self, doc: &mut Document, ctx: &Context, line: usize, header: &str) {
        let lines = self.block_lines();
        let Some((title, ":")) = quoted(header).map(|(title, tail)| (title, tail.trim())) else {
            self.error("parse-table", "write `table \"title\":`", line, header);
            return;
        };
        if title.trim().is_empty() {
            self.error("parse-table", "a table needs a title", line, header);
            return;
        }
        let [(head_line, indent, head), (rule_line, rule_indent, rule), rows @ ..] =
            lines.as_slice()
        else {
            self.error(
                "parse-table",
                "a table needs a header, a separator and at least one row",
                line,
                header,
            );
            return;
        };
        let Some(columns) = cells(head).and_then(|cells| {
            cells
                .iter()
                .map(|(_, text)| heading(text).map(|(title, role)| (title.to_string(), role)))
                .collect::<Option<Vec<_>>>()
        }) else {
            self.error("parse-table", "each column needs a heading and may have the role `{id}`, `{statement}` or `{references}`", *head_line, head);
            return;
        };
        let mut headings = BTreeSet::new();
        let mut roles = BTreeSet::new();
        if columns.iter().any(|(label, role)| {
            !headings.insert(label) || (*role != Role::Text && !roles.insert(*role))
        }) {
            self.error(
                "parse-table",
                "table headings and typed roles must be unique",
                *head_line,
                head,
            );
            return;
        }
        if roles.contains(&Role::Id) && !roles.contains(&Role::Statement) {
            self.error(
                "parse-table",
                "an id column needs a statement column",
                *head_line,
                head,
            );
            return;
        }
        if indent != rule_indent
            || !cells(rule).is_some_and(|cells| {
                cells.len() == columns.len()
                    && cells
                        .iter()
                        .all(|(_, text)| text.len() >= 3 && text.bytes().all(|byte| byte == b'-'))
            })
        {
            self.error(
                "parse-table",
                "each column needs a separator of at least three hyphens at the header indentation",
                *rule_line,
                rule,
            );
            return;
        }
        if rows.is_empty() {
            self.error(
                "parse-table",
                "a table needs at least one row",
                line,
                header,
            );
            return;
        }
        let mut table = Table {
            title,
            line,
            sections: ctx.sections.clone(),
            headings: columns.iter().map(|(label, _)| label.clone()).collect(),
            rows: Vec::new(),
        };
        let mut statement_columns = Vec::new();
        for (line, row_indent, text) in rows {
            let Some(cells) = cells(text).filter(|cells| cells.len() == columns.len()) else {
                self.error(
                    "parse-table",
                    format!("this row needs {} cells between pipes", columns.len()),
                    *line,
                    text,
                );
                return;
            };
            if indent != row_indent {
                self.error(
                    "parse-table",
                    "table rows use the indentation of the header",
                    *line,
                    text,
                );
                return;
            }
            let mut row = TableRow {
                line: *line,
                cells: Vec::new(),
            };
            let mut statement_column = None;
            for ((offset, value), (label, role)) in cells.into_iter().zip(&columns) {
                let cell = match cell(*role, value) {
                    Ok(cell) => cell,
                    Err(reason) => {
                        self.error(
                            "parse-table",
                            format!("column {label:?}: {reason}"),
                            *line,
                            text,
                        );
                        return;
                    }
                };
                if *role == Role::Statement {
                    statement_column = Some(row_indent + offset + 1);
                }
                row.cells.push(cell);
            }
            table.rows.push(row);
            statement_columns.push(statement_column);
        }

        // Each semantic cell uses the same path as its ordinary source form.
        for (row, column) in table.rows.iter().zip(statement_columns) {
            for cell in &row.cells {
                match cell {
                    TableCell::Statement(text) => {
                        self.column = column.expect("a statement cell has a source column");
                        self.end_line = row.line;
                        self.shares_line = false;
                        self.plain_statement(
                            doc,
                            ctx,
                            row.identifier().map(str::to_string),
                            text,
                            row.line,
                        );
                    }
                    TableCell::References(ids) => {
                        doc.references
                            .extend(ids.iter().map(|id| (id.clone(), row.line)));
                    }
                    TableCell::Text(_) | TableCell::Identifier(_) => {}
                }
            }
        }
        doc.tables.push(table);
    }
}
