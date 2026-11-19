//! A package as a Markdown document: each file with its sections and its
//! statements, each statement with the assume-guarantee contract that it is
//! read as by responsibility, and the proof obligations of the package in
//! their bounded form. Nothing in it is proved.

use crate::convert::Converted;
use crate::project::Project;
use std::collections::BTreeSet;
use trion_language::document::{Table, TableCell};
use trion_language::Spec;
use trion_solver::Formula;
use trion_verification::{ObligationQuestion, ProofObligations};

/// A formula as it is written in a contract: a conjunction at the top
/// stands without brackets.
fn written(formula: &Formula) -> String {
    match formula {
        Formula::And(parts) if !parts.is_empty() => parts.iter().map(ToString::to_string).collect::<Vec<_>>().join(" ∧ "),
        other => other.to_string(),
    }
}

/// A formula without what says nothing: a conjunction or a disjunction of
/// one part is that part, and `⊤` is no part of a conjunction.
fn plain(formula: &Formula) -> Formula {
    let one = |mut parts: Vec<Formula>, join: fn(Vec<Formula>) -> Formula| if parts.len() == 1 { parts.remove(0) } else { join(parts) };
    match formula {
        Formula::And(parts) => one(parts.iter().map(plain).filter(|part| *part != Formula::True).collect(), Formula::And),
        Formula::Or(parts) => one(parts.iter().map(plain).filter(|part| *part != Formula::Not(Box::new(Formula::True))).collect(), Formula::Or),
        Formula::Not(inner) => Formula::Not(Box::new(plain(inner))),
        Formula::Implies(left, right) => Formula::Implies(Box::new(plain(left)), Box::new(plain(right))),
        Formula::True | Formula::Atom(_) => formula.clone(),
    }
}

/// The text of a statement on one line.
fn text_of(spec: &Spec) -> String {
    spec.sentence.source.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The bounded proof obligation that a behaviour keeps every statement, as
/// the MMT form states it: a contract that is required at some moment is
/// written once over a moment `t` (`Ok@t`) with the disjunction of its
/// moments, and the formulas that order the times of the moments are
/// written as one line.
fn obligation_of(stated: &ProofObligations) -> String {
    let Some(consistency) = stated.obligations.iter().find(|o| o.name == "consistency") else { return String::new() };
    // What a behaviour of the system keeps: the standing formulas and the guarantees.
    let ObligationQuestion::ForAllExists { standing, conclusions, .. } = &consistency.question else { return String::new() };
    let formulas: Vec<(usize, &Formula)> = standing.iter().chain(conclusions).map(|&id| (id, &stated.pool[id])).collect();
    // `time@(t+1) − time@t ≥ 0 ms` for each moment `t` but the last.
    let ordering = |at: usize, formula: &Formula| formula.to_string() == format!("time@{} − time@{at} ≥ 0 ms", at + 1);
    let ordered = formulas.iter().take_while(|(id, formula)| ordering(*id, formula)).count();
    // A disjunction whose parts differ in their moment only: `Ok@0 ∨ Ok@1 ∨ …`.
    let over_moments = |formula: &Formula| -> Option<(String, usize)> {
        let Formula::Or(parts) = formula else { return None };
        let at = |moment: usize, part: &Formula| written(part).replace(&format!("@{moment})"), "@t)");
        let first = at(0, parts.first()?);
        (first.contains("@t)") && parts.iter().enumerate().all(|(moment, part)| at(moment, part) == first)).then_some((first, parts.len()))
    };
    let contracts: Vec<(usize, Option<(String, usize)>, String)> = formulas.iter().skip(ordered).map(|(id, formula)| (*id, plain(formula))).map(|(id, formula)| (id, over_moments(&formula), written(&formula))).collect();
    let named = contracts.iter().filter(|(_, schema, _)| schema.is_some()).count();
    let name = |number: usize| if named == 1 { "Ok".to_string() } else { format!("Ok{number}") };
    let mut definitions = String::new();
    let mut lines = String::new();
    let mut number = 0;
    for (id, schema, plain) in &contracts {
        match schema {
            Some((body, moments)) => {
                number += 1;
                definitions.push_str(&format!("{}@t ≔ {body}\n", name(number)));
                lines.push_str(&format!("f{id} ≔ {}\n", (0..*moments).map(|moment| format!("{}@{moment}", name(number))).collect::<Vec<_>>().join(" ∨ ")));
            }
            None => lines.push_str(&format!("f{id} ≔ {plain}\n")),
        }
    }
    if ordered > 0 {
        let range = if ordered == 1 { "f0".to_string() } else { format!("f0..f{}", ordered - 1) };
        lines.push_str(&format!("{range} ≔ time@(t+1) − time@t ≥ 0 ms\n"));
    }
    if definitions.is_empty() { lines } else { format!("{definitions}\n{lines}") }
}

/// The contracts of a displayed sentence or of its expanded parts.
fn contracts_of(parts: &[&Spec], converted: &Converted) -> Vec<String> {
    parts.iter()
        .flat_map(|part| converted.contracts.iter().filter(move |c| c.role != "axiom" && c.statement.id == part.display_id()))
        .map(|c| {
            let mut block = String::new();
            let variables = |list: &[(String, String)]| list.iter().map(|(variable, kind)| format!("{variable}: {kind}")).collect::<Vec<_>>().join(", ");
            if !c.parameters.is_empty() {
                block.push_str(&format!("  for each {}\n", variables(&c.parameters)));
            }
            if !c.chosen.is_empty() {
                block.push_str(&format!("  for some {} that the response chooses\n", variables(&c.chosen)));
            }
            block.push_str(&format!("  A = {}\n  G = {}\n", written(&c.assume), written(&c.guarantee)));
            for line in &c.timing {
                block.push_str(&format!("  time: {line}\n"));
            }
            match &c.scope {
                Some(trion_verification::Scope::Document) => block.push_str("  distributed to every guarantee of the document\n"),
                Some(trion_verification::Scope::Block { head, file, line }) => block.push_str(&format!("  distributed to the guarantees of the block `{head}` ({file}:{line})\n")),
                None => {}
            }
            block
        })
        .collect()
}

fn table(out: &mut String, table: &Table, specs: &[&Spec], converted: &Converted, anchors: &BTreeSet<&str>) {
    let row = |cells: Vec<String>| format!("| {} |\n", cells.iter().map(|text| text.replace('|', "\\|")).collect::<Vec<_>>().join(" | "));
    out.push_str(&format!("\n**{}**\n\n", table.title));
    out.push_str(&row(table.headings.clone()));
    out.push_str(&row(vec!["---".to_string(); table.headings.len()]));
    for line in &table.rows {
        out.push_str(&row(line.cells.iter().map(|cell| match cell {
            TableCell::Identifier(id) => format!("<a id=\"{id}\"></a>`{id}`"),
            TableCell::References(ids) => ids.iter().map(|id| {
                if anchors.contains(id.as_str()) { format!("[`{id}`](#{id})") } else { format!("`{id}`") }
            }).collect::<Vec<_>>().join(", "),
            _ => cell.to_string(),
        }).collect()));
    }
    for line in &table.rows {
        let parts: Vec<_> = specs.iter().copied().filter(|spec| spec.line == line.line).collect();
        let contracts = contracts_of(&parts, converted);
        if !contracts.is_empty() {
            let label = line.identifier().map_or_else(|| format!("Row at line {}", line.line), |id| format!("[{id}]"));
            out.push_str(&format!("\n- **{label}**\n\n  ```text\n{}  ```\n", contracts.join("\n")));
        }
    }
}

/// Renders the package, or one of its files, as one Markdown document.
pub(crate) fn render(project: &Project, converted: &Converted, only: Option<&str>) -> Result<String, String> {
    let mut files: Vec<&str> = Vec::new();
    for spec in project.root_specs() {
        if !files.contains(&spec.file.as_str()) {
            files.push(&spec.file);
        }
    }
    let tables: Vec<_> = project.set.packages.iter().filter(|p| p.is_root)
        .flat_map(|p| &p.documents)
        .flat_map(|doc| doc.tables.iter().map(|table| (doc.file.as_str(), table)))
        .collect();
    for &(file, _) in &tables {
        if !files.contains(&file) {
            files.push(file);
        }
    }
    if let Some(wanted) = only {
        let wanted = wanted.trim_start_matches("./");
        files.retain(|file| *file == wanted || file.ends_with(&format!("/{wanted}")) || wanted.ends_with(&format!("/{file}")));
        if files.is_empty() {
            return Err(format!("no file of package `{}` is `{wanted}`", project.manifest.package.name));
        }
    }
    let stated = &converted.obligations;
    let bound = match stated.individuals {
        Some(n) => format!("traces of {} moments and domains of {n} individuals", stated.moments),
        None => format!("traces of {} moments and domains of one individual of each type", stated.moments),
    };
    let mut out = format!("# {}\n\nConverted; nothing here is proved. The proof obligations hold within {bound}, and `trioc prove` proves them from the MMT form.\n", project.manifest.package.name);
    let anchors = tables.iter().filter(|(file, _)| files.contains(file))
        .flat_map(|(_, table)| table.rows.iter().filter_map(|row| row.identifier())).collect();
    for file in files {
        out.push_str(&format!("\n## {file}\n"));
        enum Item<'a> { Statement(&'a Spec), Table(&'a Table) }
        let specs: Vec<_> = project.root_specs().filter(|spec| spec.file == file).collect();
        let file_tables: Vec<_> = tables.iter().filter(|(path, _)| *path == file).map(|&(_, table)| table).collect();
        let rows: BTreeSet<_> = file_tables.iter().flat_map(|table| table.rows.iter().map(|row| row.line)).collect();
        let mut items: Vec<_> = specs.iter().copied().filter(|spec| !rows.contains(&spec.line)).map(Item::Statement)
            .chain(file_tables.into_iter().map(Item::Table)).collect();
        items.sort_by_key(|item| match item { Item::Statement(spec) => spec.line, Item::Table(table) => table.line });
        let mut sections: &[String] = &[];
        for item in items {
            let next = match item { Item::Statement(spec) => &spec.sections, Item::Table(table) => &table.sections };
            if next != sections {
                sections = next;
                if let Some(title) = sections.last() {
                    out.push_str(&format!("\n{} {title}\n", "#".repeat((2 + sections.len()).min(6))));
                }
            }
            let spec = match item {
                Item::Statement(spec) => spec,
                Item::Table(value) => {
                    table(&mut out, value, &specs, converted, &anchors);
                    continue;
                }
            };
            // A sentence with composite vocabulary is written once, as its
            // author wrote it, with the contract of each sentence that it
            // abbreviates.
            let (text, label, parts): (String, Option<String>, Vec<&Spec>) = match &spec.abbreviates {
                Some((_, number)) if *number > 1 => continue,
                Some((authored, _)) => {
                    let parts = project.root_specs().filter(|part| part.file == spec.file && part.line == spec.line && part.abbreviates.as_ref().is_some_and(|(of, _)| of == authored)).collect();
                    (authored.split_whitespace().collect::<Vec<_>>().join(" "), spec.id.as_ref().and_then(|id| id.rsplit_once('/')).map(|(parent, _)| parent.to_string()), parts)
                }
                None => (text_of(spec), spec.id.clone(), vec![spec]),
            };
            let label = label.map_or(String::new(), |id| format!("**[{id}]** "));
            out.push_str(&format!("\n- {label}{text}\n"));
            let contracts = contracts_of(&parts, converted);
            if !contracts.is_empty() {
                out.push_str(&format!("\n  ```text\n{}  ```\n", contracts.join("\n")));
            }
        }
    }
    if only.is_none() {
        out.push_str("\n## Proof obligations\n\n");
        for obligation in &stated.obligations {
            out.push_str(&format!("- `{}` ({}): {}\n", obligation.name, obligation.property, obligation.proposition));
        }
        // The bounded proposition that a behaviour keeps every statement.
        let bounded = obligation_of(stated);
        if !bounded.is_empty() {
            out.push_str(&format!("\n```text\n{bounded}```\n"));
        }
    }
    Ok(out)
}
