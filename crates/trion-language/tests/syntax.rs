use trion_language::parse_sentence;
use trion_language::syntax::ast::*;

fn core(text: &str) -> Core {
    parse_sentence(text).unwrap_or_else(|e| panic!("{text}: {e}")).core
}

#[test]
fn accepts_every_ears_pattern() {
    for text in [
        "The API shall return foo.",
        "When the user sends a message, the API shall store the message.",
        "While the room is open, the API shall accept members.",
        "Where the audit feature is enabled, the API shall write a log.",
        "If the payload is invalid, then the API shall return an error.",
        "Where the audit feature is enabled, while the room is open, when the user leaves the room, the API shall write a log.",
    ] {
        assert!(parse_sentence(text).is_ok(), "{text}");
    }
}

#[test]
fn keeps_the_source_text() {
    let text = "The API   shall return foo.";
    assert_eq!(parse_sentence(text).unwrap().source, text);
}

#[test]
fn reads_modal_force() {
    for (text, want, negated) in [
        ("The API shall stop.", Modal::Shall, false),
        ("The API must stop.", Modal::Must, false),
        ("The API shall not stop.", Modal::Shall, true),
        ("The API should stop.", Modal::Should, false),
        ("The API may stop.", Modal::May, false),
    ] {
        match core(text) {
            Core::Deontic { modal, negated: n, .. } => assert_eq!((modal, n), (want, negated), "{text}"),
            other => panic!("{other:?}"),
        }
    }
}

#[test]
fn rejects_a_sentence_without_a_pivot() {
    let error = parse_sentence("The API for gRPC.").unwrap_err();
    assert!(error.contains("pivot"), "{error}");
}

#[test]
fn rejects_japanese_sentences() {
    assert!(parse_sentence("APIはgRPC通信をする").is_err());
    assert!(parse_sentence("room_typeはPrivateである").is_err());
}

#[test]
fn rejects_more_than_one_sentence_on_a_line() {
    assert!(parse_sentence("The API shall stop. The API shall start.").is_err());
}

#[test]
fn a_backtick_literal_is_one_word() {
    match core("The `GET /foo and bar.` of the API shall return foo.") {
        Core::Deontic { subject: NpGroup::Single(np), .. } => assert_eq!(np.head, "`GET /foo and bar.`"),
        other => panic!("{other:?}"),
    }
}

#[test]
fn a_literal_shields_reserved_words() {
    match core("The `shall` field shall hold text.") {
        Core::Deontic { subject: NpGroup::Single(np), .. } => assert_eq!(np.modifiers, vec!["`shall`".to_string()]),
        other => panic!("{other:?}"),
    }
}

fn enumeration(text: &str) -> Vec<String> {
    match core(text) {
        Core::Description { predicate: Predicate::Enumeration { values, .. }, .. } => values,
        other => panic!("{text}: {other:?}"),
    }
}

#[test]
fn reads_every_enumeration_spelling() {
    let two = vec!["Private".to_string(), "Public".to_string()];
    let three = vec!["Private".to_string(), "Public".to_string(), "Secret".to_string()];
    assert_eq!(enumeration("room_type is Private and Public."), two);
    assert_eq!(enumeration("room_type is Private or Public."), two);
    assert_eq!(enumeration("room_type is one of Private and Public."), two);
    assert_eq!(enumeration("room_type is Private, Public and Secret."), three);
    assert_eq!(enumeration("room_type is Private, Public, and Secret."), three);
    assert_eq!(enumeration("room_type is one of Private, Public, or Secret."), three);
}

#[test]
fn rejects_mixed_enumeration_conjunctions() {
    assert!(parse_sentence("room_type is Private and Public or Secret.").is_err());
}

#[test]
fn an_enumeration_keeps_later_adjuncts() {
    let sentence = parse_sentence("room_type is Private and Public, unless the archive is enabled.").unwrap();
    assert!(sentence.exception.is_some());
    assert!(matches!(sentence.core, Core::Description { predicate: Predicate::Enumeration { .. }, .. }));
}

#[test]
fn a_comma_is_still_rejected_outside_an_enumeration() {
    assert!(parse_sentence("The API shall return foo, bar.").is_err());
}

/// A deterministic generator of hostile input.
struct Soup(u64);

impl Soup {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

#[test]
fn the_parser_is_total_on_hostile_input() {
    const WORDS: [&str; 28] = ["The", "shall", "not", "is", "and", "or", ",", ".", "`", "`a b", "When", "If", "then", "unless", "one", "of", "means", "may", "at", "most", "30", "€", "あ", "🙂", "\u{301}", "either", "that", "\t"];
    let mut soup = Soup(0x9E37_79B9_7F4A_7C15);
    for _ in 0..20_000 {
        let length = soup.next() % 12;
        let text: Vec<&str> = (0..length).map(|_| WORDS[(soup.next() % WORDS.len() as u64) as usize]).collect();
        let _ = parse_sentence(&text.join(" "));
    }
    let deep = format!("The a{} shall stop.", " of the a".repeat(5_000));
    let _ = parse_sentence(&deep);
    let _ = parse_sentence(&"`".repeat(10_000));
}

fn roles_of(text: &str) -> Vec<String> {
    match core(text) {
        Core::Deontic { vp, .. } => vp.single().unwrap().roles.iter().map(RolePp::render).collect(),
        other => panic!("{other:?}"),
    }
}

#[test]
fn a_preposition_opens_a_role() {
    assert_eq!(roles_of("The API shall reject a call for an open domain."), ["for an open domain"]);
    assert_eq!(roles_of("The API shall compare a source with a copy."), ["with a copy"]);
    // A possessive with one candidate is replaced by what it names: the position of the call.
    assert_eq!(roles_of("Each call shall arrive by its position."), ["by the position of the call"]);
    assert_eq!(roles_of("The API shall report a conflict as a set."), ["as a set"]);
    assert_eq!(roles_of("The API shall listen for 5 seconds."), ["for 5 seconds"]);
}

#[test]
fn of_after_a_verb_is_a_role() {
    assert_eq!(roles_of("The set shall consist of two parts."), ["of two parts"]);
}

#[test]
fn a_comma_list_of_noun_phrases_is_read() {
    match core("The API, the CLI and the daemon shall read the a, b, and c.") {
        Core::Deontic { subject: NpGroup::Coordinated { items, .. }, vp, .. } => {
            assert_eq!(items.len(), 3);
            match &vp.single().unwrap().object {
                Some(NpGroup::Coordinated { items, conj, .. }) => assert_eq!((items.len(), *conj), (3, Conj::And)),
                other => panic!("{other:?}"),
            }
        }
        other => panic!("{other:?}"),
    }
}

#[test]
fn a_condition_can_hold_a_comma_list() {
    let sentence = parse_sentence("When the user, the admin or the bot leaves, the API shall stop.").unwrap();
    assert!(sentence.frames.trigger.is_some());
    assert!(matches!(sentence.core, Core::Deontic { .. }));
}

#[test]
fn is_not_reads_as_never() {
    match core("room_type is not Invalid.") {
        Core::Description { adverb, .. } => assert_eq!(adverb, Some(DescriptionAdverb::Never)),
        other => panic!("{other:?}"),
    }
}

#[test]
fn a_condition_can_be_negated() {
    let sentence = parse_sentence("While the room is not open, the API shall stop.").unwrap();
    assert_eq!(sentence.frames.states[0].clause.render(), "the room is not open");
}

#[test]
fn unless_needs_no_comma() {
    for text in ["The API shall stop unless the override is active.", "The API shall stop, unless the override is active."] {
        assert!(parse_sentence(text).unwrap().exception.is_some(), "{text}");
    }
}

#[test]
fn a_quantified_subject_can_take_a_final_verb() {
    let sentence = parse_sentence("While at least one alternative remains, the API shall stop.").unwrap();
    assert_eq!(sentence.frames.states[0].clause.render(), "at least 1 alternative remains");
}

#[test]
fn words_without_a_formal_reading_are_rejected() {
    for text in [
        "Only admins shall delete users.",
        "Nobody shall delete users.",
        "Neither the client nor the server shall retry.",
        "The client is forbidden to access the dashboard.",
        "The API is required to return 200.",
        "While the user is active but idle, the API shall stop.",
    ] {
        assert!(parse_sentence(text).unwrap_err().contains("no formal reading"), "{text}");
    }
}

#[test]
fn a_literal_word_is_not_rejected() {
    assert!(parse_sentence("The API shall return `only`.").is_ok());
    assert!(parse_sentence("The disk is read-only.").is_ok());
}

#[test]
fn an_id_needs_brackets() {
    assert!(parse_sentence("REQ-1: The API shall stop.").unwrap_err().contains("in brackets"));
}

#[test]
fn a_pronoun_without_an_antecedent_is_rejected() {
    assert!(parse_sentence("It shall stop.").unwrap_err().contains("no noun phrase before it"));
}

#[test]
fn common_verbs_settle_the_boundary() {
    for (text, clause) in [
        ("When the user presses Escape, the modal shall close.", "the user presses Escape"),
        ("If the network request fails, then the app shall stop.", "the network request fails"),
        ("When a user changes its password, the app shall stop.", "a user changes the password of the user"),
        ("When the temperature exceeds 85 degrees, the app shall stop.", "the temperature exceeds 85 degrees"),
    ] {
        let sentence = parse_sentence(text).unwrap();
        assert_eq!(sentence.frames.trigger.unwrap().clause.render(), clause);
    }
}

#[test]
fn an_unknown_verb_stays_ambiguous() {
    assert!(parse_sentence("When the client frobs telemetry, the app shall stop.").unwrap_err().contains("ambiguous"));
}

#[test]
fn temporal_openers_are_frames() {
    for text in [
        "After the job ends, the app shall stop.",
        "Once the ticket is closed, the app shall stop.",
        "Before a node is drained, the app shall stop.",
        "After 3 failed retries, the app shall stop.",
        "On startup, the app shall stop.",
        "Upon receipt of a token, the app shall stop.",
    ] {
        assert!(parse_sentence(text).unwrap().frames.trigger.is_some(), "{text}");
    }
    for text in ["During maintenance, the app shall stop.", "Until the job ends, the app shall stop."] {
        assert_eq!(parse_sentence(text).unwrap().frames.states.len(), 1, "{text}");
    }
}

#[test]
fn in_is_a_particle_after_log() {
    let sentence = parse_sentence("When a user logs in with valid credentials, the app shall stop.").unwrap();
    assert_eq!(sentence.frames.trigger.unwrap().clause.render(), "a user logs in with valid credentials");
}

#[test]
fn a_measure_can_take_of() {
    assert_eq!(roles_of("The system shall delete data within 30 days of account deletion."), ["within 30 days", "of account deletion"]);
    assert_eq!(roles_of("The session shall expire after 30 minutes of inactivity."), ["after 30 minutes of inactivity"]);
}

fn trigger(text: &str) -> ClauseGroup {
    parse_sentence(text).unwrap_or_else(|e| panic!("{text}: {e}")).frames.trigger.unwrap_or_else(|| panic!("{text}: no trigger")).clause
}

#[test]
fn a_role_phrase_can_modify_the_subject_of_a_condition() {
    for (text, subject, verb) in [
        ("When a request from the client fails, the server shall log the request.", "a request that is from the client", "fails"),
        ("If a statement about the term violates a form, then the checker shall report the statement.", "a statement that is about the term", "violates"),
    ] {
        let group = trigger(text);
        assert_eq!(group.items.len(), 1, "{text}");
        let clause = &group.items[0];
        assert_eq!(clause.subject.render(), subject, "{text}");
        match &clause.body {
            ClauseBody::Verbal { verb: v, .. } => assert_eq!(v, verb, "{text}"),
            other => panic!("{text}: {other:?}"),
        }
    }
    // A verb never follows an article: no reading is guessed.
    assert!(parse_sentence("When ends inside a sentence, the server shall stop.").is_err());
}

#[test]
fn relative_clauses_on_one_head_can_be_coordinated() {
    for text in [
        "The formalizer shall read each statement as a contract whose assumption is the conditions and whose guarantee is the response.",
        "Each request that has a token and that has a session shall succeed.",
    ] {
        let rendered = parse_sentence(text).unwrap_or_else(|e| panic!("{text}: {e}")).render();
        assert!(rendered.contains(" and whose ") || rendered.contains(" and that "), "{text} -> {rendered}");
    }
}

#[test]
fn alternative_verbs_share_one_subject_and_its_role() {
    let group = trigger("If a quote begins or ends inside a sentence, then the checker shall report the quote.");
    assert_eq!(group.conj, Some(Conj::Or));
    assert_eq!(group.items.len(), 2);
    for clause in &group.items {
        assert_eq!(clause.subject.render(), "a quote");
        match &clause.body {
            ClauseBody::Verbal { roles, .. } => assert_eq!(roles.len(), 1, "the role belongs to both verbs"),
            other => panic!("{other:?}"),
        }
    }
    let group = trigger("When the job starts or stops, the server shall log the job.");
    assert_eq!(group.items.len(), 2);
}

#[test]
fn a_relative_clause_can_be_negated() {
    let negated = parse_sentence("Each rule that does not cite the draft shall have a test.").unwrap().render();
    assert!(negated.contains("that does not cite the draft"), "{negated}");
    let plain = parse_sentence("Each rule that cites the draft shall have a test.").unwrap().render();
    assert_ne!(negated, plain);
}
