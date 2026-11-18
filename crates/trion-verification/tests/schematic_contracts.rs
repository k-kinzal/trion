//! One sentence is one contract (AGENTS.md, rule 1), and the size of the
//! domains of individuals is a bound of the obligations, not part of any
//! contract: the contract of a sentence about the individuals of a declared
//! type names each by the noun of its variable, whatever the size. Without
//! the declaration a noun names one thing, and a sentence that relates no
//! two declared types has the same formulas as with it.

mod common;
use common::*;
use trion_verification::{stated_contracts, Bounds, Options, StatedContract};

fn contracts(text: &str) -> Vec<StatedContract> {
    within(text, Options::default().bounds.scope)
}

/// The contracts of a package whose domains hold `scope` individuals of each type.
fn within(text: &str, scope: usize) -> Vec<StatedContract> {
    let set = set(text);
    let defaults = Options::default();
    let options = Options { bounds: Bounds { scope, ..defaults.bounds }, ..defaults };
    let analysis = proved(&set, &options);
    stated_contracts(&set, &analysis).0
}

/// The contracts without what only the declaration adds: the variables
/// and their types.
fn formulas(contracts: &[StatedContract]) -> Vec<String> {
    contracts.iter().map(|c| format!("{} {}: {} => {} | {:?}", c.statement.id, c.role, c.assume, c.guarantee, c.timing)).collect()
}

const CORPUS: [(&str, &str); 11] = [
    ("user, room", "[A] When a user enters a room, the API shall greet the user.\n"),
    ("user, message", "[A] When a user sends a message, the API shall store the message.\n[B] The API shall not store a message.\n"),
    ("user", "[A] Each user shall be notified.\n"),
    ("user, account", "[A] Each user has at most one account.\n"),
    ("door", "[A] While a door is open, the API shall log the door.\n"),
    ("request", "[A] When a request arrives, the API shall answer the request within 5 seconds.\n"),
    ("user", "[A] If a user is blocked, then the API shall reject the user.\n[B] When a user logs in, the API shall record the login.\n"),
    ("order", "[A] When an order is placed, the API shall confirm the order before the order ships.\n"),
    ("user", "[A] No user shall delete the log.\n"),
    ("user", "[A] The API should notify a user.\n"),
    ("sensor", "[A] While a sensor is faulty, the API shall raise an alarm until an operator acknowledges the alarm.\n"),
];

#[test]
fn a_declaration_of_individuals_leaves_the_contract_of_each_sentence_as_it_is() {
    for (types, body) in CORPUS {
        let body = format!("system API\n{body}");
        let plain = contracts(&body);
        let declared = contracts(&format!("individuals {types}\n{body}"));
        // One contract for each sentence, and no instance among them.
        assert!(declared.iter().all(|c| !c.statement.id.contains('/')), "{body}: {declared:#?}");
        assert_eq!(formulas(&plain), formulas(&declared), "{body}");
        assert!(plain.iter().all(|c| c.parameters.is_empty() && c.chosen.is_empty()), "{body}");
    }
}

#[test]
fn the_size_of_the_domains_changes_no_contract() {
    let corpus = CORPUS.iter().copied().chain([("member, room", "[A] When a member of a room posts a message, the API shall store the message.\n")]);
    for (types, body) in corpus {
        let text = format!("individuals {types}\nsystem API\n{body}");
        let one = within(&text, 1);
        for scope in [2, 3] {
            let other = within(&text, scope);
            let whole = |list: &[StatedContract]| list.iter().map(|c| format!("{} {} {:?} {:?}: {} => {} | {:?} {:?}", c.statement.id, c.role, c.parameters, c.chosen, c.assume, c.guarantee, c.timing, c.scope)).collect::<Vec<_>>();
            assert_eq!(whole(&one), whole(&other), "{body} within domains of {scope}");
        }
    }
}

#[test]
fn the_variables_of_a_schematic_contract_say_which_names_range_over_a_type() {
    let declared = contracts("individuals user, room\nsystem API\n[A] When a user enters a room, the API shall greet the user.\n[B] The API should notify a user.\n");
    let a = declared.iter().find(|c| c.statement.id == "A").unwrap();
    assert_eq!(a.parameters, [("user".to_string(), "user".to_string()), ("room".to_string(), "room".to_string())]);
    // `a user` in a response is one that the response chooses.
    let b = declared.iter().find(|c| c.statement.id == "B").unwrap();
    assert_eq!((b.parameters.as_slice(), b.chosen.as_slice()), (&[][..], &[("user".to_string(), "user".to_string())][..]));
}

#[test]
fn a_phrase_that_relates_two_declared_types_is_read_as_their_relation() {
    // A declaration of types is vocabulary that the document writes: it
    // says that `member` and `room` are kinds of individuals, and `of`
    // between two kinds is a relation between them (AGENTS.md, Limits 5). A
    // noun that no declaration makes a kind names one thing, and `member of
    // room` is then the name of that thing. The size of the domains plays no
    // part (`the_size_of_the_domains_changes_no_contract`).
    let body = "system API\n[A] When a member of a room posts a message, the API shall store the message.\n";
    let plain = contracts(body);
    assert_eq!(plain[0].assume.to_string(), "Event(member of room post message)");
    let declared = contracts(&format!("individuals member, room\n{body}"));
    assert_eq!(declared[0].assume.to_string(), "(Event(member post message) ∧ member(room, member))");
    assert_eq!(declared[0].parameters, [("room".to_string(), "room".to_string()), ("member".to_string(), "member".to_string())]);
}
