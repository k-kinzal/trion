//! Definitions, counts and references are read from the nodes of the
//! sentence: each test shows that the sentence says what its words say, or
//! that the checker rejects it.

mod common;
use common::*;

const HEAD: &str = "primitive collection\nprimitive declaration\nprimitive constraint\nprimitive report\nprimitive summary\nprimitive user\nprimitive checker\nprimitive file\nprimitive author\nprimitive subject\nprimitive service\nprimitive room\nprimitive name\nprimitive request\n\n";

fn check(text: &str) -> serde_json::Value {
    Fixture::new(&[("a.trion", &format!("{HEAD}{text}"))]).verify(&["--json", "a.trion"]).json()
}

fn model(text: &str) -> String {
    Fixture::new(&[("a.trion", &format!("{HEAD}{text}"))]).inspect(&["model", "a.trion"]).stdout
}

fn codes(text: &str) -> Vec<String> {
    report_codes(&check(text))
}

/// The messages of the parts that have no reading, and of the sentences that have no parse.
fn rejected(text: &str) -> Vec<String> {
    let report = check(text);
    let mut out: Vec<String> = report["opaque"].as_array().unwrap().iter().map(|d| d["message"].as_str().unwrap().to_string()).collect();
    out.extend(report["diagnostics"].as_array().unwrap().iter().filter(|d| d["severity"] == "error").map(|d| format!("{}: {}", d["code"].as_str().unwrap(), d["message"].as_str().unwrap())));
    out
}

fn contradicts(text: &str) {
    assert!(codes(text).iter().any(|c| c == "contradiction"), "no contradiction in:\n{text}\n{:?}", rejected(text));
}

/// The statements describe and none requires: each is an assumption, and
/// assumptions that cannot all hold leave no environment.
fn incompatible(text: &str) {
    assert!(codes(text).iter().any(|c| c == "incompatible"), "no incompatibility in:\n{text}\n{:?}", rejected(text));
}

fn consistent(text: &str) {
    let found = rejected(text);
    assert!(found.is_empty(), "{text}\n{found:?}");
}

#[test]
fn a_definition_includes_its_term_in_the_kind_that_it_names() {
    let definition = "[D]\nA specification means a collection of declarations and constraints.\n";
    incompatible(&format!("{definition}\n[N]\nNo specification is a collection.\n"));
    // The list after `of` names the owners of one kind: the definition names no second kind.
    consistent(definition);
    consistent("[N]\nNo specification is a collection.\n");
}

#[test]
fn the_clause_of_a_kind_is_a_property_of_each_member() {
    let definition = "[D]\nA certificate means a report that the checker signs.\n";
    contradicts(&format!("{definition}\n[E]\nThere is a certificate.\n\n[N]\nThe checker shall not sign a certificate.\n"));
    consistent(&format!("{definition}\n[E]\nThere is a certificate.\n"));
}

#[test]
fn each_alternative_kind_is_a_kind_of_the_term() {
    let definition = "[K]\nA notice means a report or a summary.\n";
    incompatible(&format!("{definition}\n[L]\nNo report is a notice.\n"));
    incompatible(&format!("{definition}\n[L]\nNo summary is a notice.\n"));
    consistent(definition);
}

#[test]
fn a_definition_without_a_reading_is_rejected() {
    // Two kinds joined by `and`.
    let two = rejected("[D]\nA bundle means a report and a summary.\n");
    assert!(two.iter().any(|m| m.contains("between two kinds in a definition")), "{two:?}");
    // A participle after the noun, without `that is`.
    let participle = rejected("[D]\nA package means an identified report assembled from a file.\n");
    assert!(participle.iter().any(|m| m.contains("is a participle")), "{participle:?}");
    assert!(rejected("[D]\nA package means an identified report that is assembled from a file.\n").is_empty());
    // A clause after `means` names no kind.
    let clause = rejected("[D]\nA closed room means the room is locked.\n");
    assert!(!clause.is_empty(), "{clause:?}");
}

#[test]
fn an_article_inside_a_name_is_rejected() {
    let found = rejected("[A]\nThe checker shall weaken a constraint to obtain a report.\n");
    assert!(found.iter().any(|m| m.contains("is an article between two words of a name")), "{found:?}");
    assert!(rejected("[A]\nThe checker shall weaken a constraint.\n").is_empty());
}

#[test]
fn a_gerund_with_an_object_names_the_action_on_that_object() {
    let view = model("[G]\nMoving a file shall notify the user.\n");
    // The object of the gerund is a noun phrase of its own: no article stands in a name.
    assert!(rejected("[G]\nMoving a file shall notify the user.\n").is_empty());
    assert!(view.contains("notify user"), "{view}");
    // The same action on another thing is another subject.
    let other = model("[G]\nMoving a report shall notify the user.\n");
    assert_ne!(view, other);
}

#[test]
fn the_first_of_two_objects_receives_the_second() {
    let two = model("[T]\nThe checker shall give each user a report.\n");
    let role = model("[T]\nThe checker shall give a report to each user.\n");
    assert_eq!(two.lines().filter(|l| l.contains("guarantee")).collect::<Vec<_>>(), role.lines().filter(|l| l.contains("guarantee")).collect::<Vec<_>>(), "{two}\n{role}");
    contradicts("[T]\nThe checker shall give each user a report.\n\n[N]\nThe checker shall not give a report.\n");
}

#[test]
fn the_object_of_a_controlling_verb_is_the_subject_of_the_clause_after_it() {
    assert!(rejected("[C]\nThe checker shall let an author state a subject.\n").is_empty());
    assert!(rejected("[C]\nThe checker shall allow an author to state a subject.\n").is_empty());
    // The clause is a part of the action: another clause is another action.
    let state = model("[C]\nThe checker shall allow an author to state a subject.\n");
    let read = model("[C]\nThe checker shall allow an author to read a subject.\n");
    assert_ne!(state, read);
    assert!(state.contains("author state subject"), "{state}");
}

#[test]
fn a_gerund_after_without_is_rejected() {
    let found = rejected("[W]\nThe checker shall read the file without changing the report.\n");
    assert!(found.iter().any(|m| m.contains("without changing")), "{found:?}");
    contradicts("[W]\nThe checker shall read the file and shall not change the report.\n\n[C]\nThe checker shall change the report.\n");
}

#[test]
fn a_bare_cardinal_counts_at_least_that_many_things() {
    // `two reports` is at least two: at most one contradicts it, and three do not.
    contradicts("[A]\nThe checker shall send two reports.\n\n[B]\nThe checker shall send at most 1 report.\n");
    consistent("[A]\nThe checker shall send two reports.\n\n[B]\nThe checker shall send at least 3 reports.\n");
    // A numeral reads as its word does.
    contradicts("[A]\nThe checker shall send 2 reports.\n\n[B]\nThe checker shall send at most 1 report.\n");
    // A number word after a determiner is no count and no word of a name.
    let found = rejected("[A]\nThe checker shall send the two reports.\n");
    assert!(found.iter().any(|m| m.contains("`two` is a number word")), "{found:?}");
}

#[test]
fn a_count_of_owners_above_one_is_rejected() {
    let found = rejected("[A]\nThe checker shall send the report of two users.\n");
    assert!(found.iter().any(|m| m.contains("is a count before the owner of a thing")), "{found:?}");
    // One owner is an owner.
    assert!(rejected("[A]\nThe checker shall send the report of one user.\n").is_empty());
}

#[test]
fn a_denial_of_a_pair_is_read_over_individuals_or_rejected() {
    // Two rooms with one name are denied.
    incompatible("[P]\nNo two rooms have the same name.\n\n[C]\nThere are exactly 2 rooms.\n\n[N]\nThere is exactly 1 name.\n\n[E]\nEach room has a name.\n");
    // The statement denies no room a name.
    consistent("[P]\nNo two rooms have the same name.\n\n[E]\nEach room has a name.\n");
    // A pair among the things of an owner needs a relation of three things.
    let found = rejected("[P]\nNo two rooms of a user have the same name.\n");
    assert!(found.iter().any(|m| m.contains("`no two` is a denial of a pair")), "{found:?}");
}

#[test]
fn a_count_for_each_thing_bounds_no_total() {
    // Two reports in all do not break `at most 1 report for each request`.
    consistent("[A]\nThe service shall send at most 1 report for each request.\n\n[B]\nThe service shall send at least 2 reports.\n");
    contradicts("[A]\nThe service shall send at most 1 report.\n\n[B]\nThe service shall send at least 2 reports.\n");
}

#[test]
fn a_pronoun_with_one_candidate_antecedent_names_that_antecedent() {
    // One noun phrase stands before the pronoun: a thing of that noun phrase.
    let subject = model("[P]\nThe checker shall print its report.\n");
    assert!(subject.contains("report of checker"), "{subject}");
    // The possessive and the phrase with `of` are one action.
    contradicts("[P]\nEach checker shall print its report.\n\n[N]\nEach checker shall not print the report of the checker.\n");
    // `it` after a condition with one noun phrase.
    let it = model("[P]\nWhen a request arrives, the checker shall print it.\n");
    assert!(it.contains("print request"), "{it}");
}

#[test]
fn a_pronoun_with_two_candidate_antecedents_is_ambiguous() {
    // Neither the nearer noun phrase nor the subject is preferred.
    let found = rejected("[P]\nThe checker shall print each report with its file.\n");
    assert!(found.iter().any(|m| m.starts_with("AMBIGUOUS_REFERENCE") && m.contains("`its file` could refer to `checker` or `report`") && m.contains("repeat the noun")), "{found:?}");
    assert_eq!(codes("[P]\nThe checker shall copy the report to the file and shall print its name.\n"), ["AMBIGUOUS_REFERENCE"]);
    assert_eq!(codes("[P]\nWhen a user opens a file, the checker shall print it.\n"), ["AMBIGUOUS_REFERENCE"]);
    // The author repeats the noun.
    consistent("[P]\nThe checker shall print each report with the file of the report.\n");
}

#[test]
fn a_pronoun_without_a_candidate_antecedent_is_unresolved() {
    assert_eq!(codes("[P]\nIts report shall name the checker.\n"), ["UNRESOLVED_REFERENCE"]);
    assert_eq!(codes("[P]\nThe checker shall print their reports.\n"), ["UNRESOLVED_REFERENCE"]);
    assert_eq!(codes("[P]\nIt shall print the report.\n"), ["UNRESOLVED_REFERENCE"]);
}

#[test]
fn number_agreement_makes_an_antecedent_the_only_candidate() {
    // `their` is the files, and `its` is the parser.
    let plural = model("[P]\nThe parser shall read the files and shall report their paths.\n");
    assert!(plural.contains("path of file") && !plural.contains("path of parser"), "{plural}");
    let singular = model("[P]\nThe parser shall read the files and shall report its state.\n");
    assert!(singular.contains("state of parser"), "{singular}");
}

#[test]
fn a_noun_phrase_is_no_antecedent_of_a_pronoun_in_its_owner() {
    // `its` is not the header: the header is the thing whose owner holds the pronoun.
    let inside = model("[P]\nEach block shall keep the header of its file.\n");
    assert!(inside.contains("header of file of block"), "{inside}");
    // After the phrase is complete, the header is a candidate as any noun phrase is.
    assert_eq!(codes("[P]\nEach block shall keep the header of the file and its name.\n"), ["AMBIGUOUS_REFERENCE"]);
}

#[test]
fn an_object_pronoun_is_not_the_subject_of_its_clause() {
    // `the checker` cannot be `it`: the request is the one candidate.
    let object = model("[P]\nWhen a request arrives, the checker shall print it.\n");
    assert!(object.contains("print request"), "{object}");
    // As a subject, `it` has the checker and the request as candidates.
    assert_eq!(codes("[P]\nWhen a checker reads a request, it shall print the report.\n"), ["AMBIGUOUS_REFERENCE"]);
}

#[test]
fn a_pronoun_of_a_leading_condition_refers_forward_to_the_one_noun_phrase_of_the_core() {
    let forward = model("[P]\nWhen its file changes, the checker shall stop.\n");
    assert!(forward.contains("file of checker"), "{forward}");
    assert_eq!(codes("[P]\nWhen its file changes, the checker shall print the report.\n"), ["AMBIGUOUS_REFERENCE"]);
    // In a condition after the core, the noun phrases of the core stand before the pronoun.
    assert_eq!(codes("[P]\nThe checker shall print the report when its file changes.\n"), ["AMBIGUOUS_REFERENCE"]);
    let after = model("[P]\nThe checker shall stop when its file changes.\n");
    assert!(after.contains("file of checker"), "{after}");
}

#[test]
fn noun_phrases_that_or_joins_are_one_antecedent_and_those_that_and_joins_are_a_plural_one() {
    let either = model("[P]\nEach title or locator shall contain its value.\n");
    assert!(either.contains("value of title") && either.contains("locator"), "{either}");
    let both = model("[P]\nThe parser and the checker shall print their reports.\n");
    assert!(both.contains("report of parser") && both.contains("checker"), "{both}");
    // Each thing that `and` joins is a candidate of `its`.
    assert_eq!(codes("[P]\nThe user shall copy the report and the file and shall print its name.\n"), ["AMBIGUOUS_REFERENCE"]);
}

#[test]
fn a_repeated_noun_phrase_is_one_antecedent_and_a_second_thing_is_a_second_one() {
    // `the report` is the report that was named.
    let again = model("[P]\nWhen a report arrives, the report shall keep its name.\n");
    assert!(again.contains("name of report"), "{again}");
    // `a report` twice is two reports.
    assert_eq!(codes("[P]\nWhen a report arrives, a report shall keep its name.\n"), ["AMBIGUOUS_REFERENCE"]);
}

#[test]
fn the_defined_term_and_its_genus_are_one_antecedent() {
    consistent("[P]\nA signed report means a report that names its author.\n\n[U]\nThe checker shall print each signed report.\n");
}

#[test]
fn the_receiver_and_the_object_of_a_giving_verb_are_candidates_of_each_other() {
    assert_eq!(codes("[P]\nThe checker shall give each user its report.\n"), ["AMBIGUOUS_REFERENCE"]);
    // After another verb, a receiver stands after the object.
    let supplied = model("[P]\nEach checker shall supply its report to each user.\n");
    assert!(supplied.contains("report of checker"), "{supplied}");
}

#[test]
fn a_demonstrative_names_the_thing_that_the_sentence_names() {
    let that = model("[Q]\nWhen a user opens a file, the checker shall print that file.\n");
    let the = model("[Q]\nWhen a user opens a file, the checker shall print the file.\n");
    assert_eq!(that.lines().filter(|l| l.contains("guarantee")).collect::<Vec<_>>(), the.lines().filter(|l| l.contains("guarantee")).collect::<Vec<_>>());
    // No antecedent.
    assert_eq!(codes("[Q]\nThe checker shall print that file.\n"), ["UNRESOLVED_REFERENCE"]);
    // Two antecedents.
    assert_eq!(codes("[Q]\nThe checker shall copy a source file to a target file and shall print that file.\n"), ["AMBIGUOUS_REFERENCE"]);
    // `this` without an antecedent names nothing of the sentence.
    assert_eq!(codes("[Q]\nThe checker shall print this report.\n"), ["UNRESOLVED_REFERENCE"]);
}

#[test]
fn no_in_a_role_is_rejected() {
    let found = rejected("[R]\nThe checker shall send a report to no user.\n");
    assert!(found.iter().any(|m| m.contains("`no` is a negation in a role")), "{found:?}");
    assert!(rejected("[R]\nThe checker shall not send a report to a user.\n").is_empty());
}

#[test]
fn within_a_quantity_of_time_is_a_deadline_that_the_quantity_bounds() {
    let bounded = "[T]\nThe configured timeout is at most 3 seconds.\n\n[D]\nThe service shall respond within the configured timeout.\n";
    contradicts(&format!("{bounded}\n[L]\nThe service shall respond at least 10 seconds after the first request.\n\n[W]\nWhen a request arrives, the service shall respond.\n"));
    consistent(bounded);
}

#[test]
fn a_known_verb_before_a_determiner_or_a_role_is_the_verb_of_its_clause() {
    // `consists` is the verb, and the quoted text is a thing.
    let view = model("[L]\nIf a file consists of the word \"end\", then the checker shall reject that file.\n");
    assert!(view.contains("consist"), "{view}");
    assert!(view.contains("reject file"), "{view}");
    // `violates` is the verb: the subject does not end at `bound`.
    let clause = model("[V]\nIf a report of a bound user violates a constraint, then the checker shall reject the report.\n");
    assert!(clause.contains("violate constraint"), "{clause}");
    assert!(rejected("[V]\nIf a report of a bound user violates a constraint, then the checker shall reject the report.\n").is_empty());
}
