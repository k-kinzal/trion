//! The word classes of the language.
//!
//! A word of a sentence is of an open class or of a closed class. An
//! open-class word (a noun, an adjective, a verb, an adverb of manner) may be
//! part of the name of a term. A closed-class word (a quantifier, a pronoun,
//! a conjunction, a preposition, an auxiliary, a negation, a word of time,
//! order, number or degree, a comparative) is never part of a name: it is
//! read by the node of the syntax tree that the parser builds for it, or the
//! sentence has no reading. The classes are stated here once; no other part
//! of the language keeps a list of them.

/// The class of a word.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum WordClass {
    /// A content word: it may be a word of a name.
    Open,
    /// No word of the sentence: a quoted literal, a code span, a number, a variable.
    Literal,
    /// A function word, with the kind that a report names it by.
    Closed(Closed),
}

/// The kinds of closed-class words.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Closed {
    Article,
    Quantifier,
    Pronoun,
    Conjunction,
    Preposition,
    Auxiliary,
    Negation,
    Distinction,
    Adverb,
    Number,
    Comparative,
}

impl Closed {
    /// How a report names a word of this kind.
    pub fn describe(self) -> &'static str {
        match self {
            Closed::Article => "an article",
            Closed::Quantifier => "a quantifier",
            Closed::Pronoun => "a pronoun",
            Closed::Conjunction => "a conjunction",
            Closed::Preposition => "a preposition",
            Closed::Auxiliary => "an auxiliary",
            Closed::Negation => "a negation",
            Closed::Distinction => "a word that tells two things apart",
            Closed::Adverb => "a word of time, order, number or degree",
            Closed::Number => "a number word",
            Closed::Comparative => "a comparative",
        }
    }
}

const ARTICLES: &[&str] = &["the", "a", "an"];
const QUANTIFIERS: &[&str] = &["each", "every", "all", "any", "some", "no", "none", "both", "either", "neither", "several", "many", "much", "few", "fewer", "fewest", "more", "most", "less", "least", "enough", "various", "numerous", "only", "just", "even", "also", "too", "exactly", "approximately", "almost", "nearly", "merely", "solely", "respectively", "else"];
const PRONOUNS: &[&str] = &["it", "its", "they", "them", "their", "theirs", "this", "that", "these", "those", "he", "she", "him", "her", "his", "hers", "we", "us", "our", "you", "your", "i", "me", "my", "itself", "themselves", "which", "what", "whatever", "whichever", "who", "whom", "whose", "whoever", "such", "nobody", "nothing", "anything", "everything", "something", "anyone", "everyone", "someone"];
const CONJUNCTIONS: &[&str] = &["and", "or", "nor", "but", "yet", "so", "because", "since", "although", "though", "unless", "until", "while", "when", "whenever", "where", "wherever", "whereas", "if", "whether", "than", "as", "once", "after", "before"];
const PREPOSITIONS: &[&str] = &["of", "in", "on", "at", "by", "for", "with", "without", "within", "to", "from", "into", "onto", "over", "under", "above", "below", "between", "among", "through", "during", "against", "about", "via", "per", "upon", "across", "along", "around", "behind", "beyond", "near", "beside", "outside", "inside", "toward", "towards", "except", "besides", "despite", "like", "unlike"];
const AUXILIARIES: &[&str] = &["be", "is", "are", "was", "were", "been", "being", "am", "has", "have", "had", "having", "do", "does", "did", "can", "could", "may", "might", "must", "shall", "should", "will", "would", "ought", "cannot"];
const NEGATIONS: &[&str] = &["not", "never", "nowhere"];
const DISTINCTIONS: &[&str] = &["another", "other", "others", "different", "distinct"];
const ADVERBS: &[&str] = &["always", "eventually", "already", "still", "again", "then", "now", "soon", "finally", "simultaneously", "together", "twice", "thrice", "sometimes", "often", "usually", "rarely", "typically", "ever", "instead", "otherwise", "very", "quite", "rather", "previously", "subsequently", "afterwards", "meanwhile", "henceforth", "anymore", "periodically", "repeatedly", "continuously", "continually", "constantly", "permanently", "temporarily", "concurrently", "initially", "eventually", "immediately", "instantly", "forever", "frequently", "occasionally", "regularly", "consecutively", "successively", "sequentially", "alone", "exclusively", "uniquely", "first", "second", "third", "last", "next", "previous", "prior", "former", "latter", "following", "preceding", "subsequent", "earlier", "later", "single", "multiple", "unique", "consecutive", "successive", "simultaneous", "concurrent", "periodic", "repeated"];
const NUMBERS: &[&str] = &["one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten", "eleven", "twelve", "dozen", "hundred", "thousand", "million"];
const COMPARATIVES: &[&str] = &["greater", "smaller", "larger", "longer", "shorter", "higher", "lower", "newer", "older", "better", "worse", "greatest", "smallest", "largest", "longest", "shortest", "highest", "lowest", "earliest", "latest", "newest", "oldest", "best", "worst"];

const CLASSES: &[(&[&str], Closed)] = &[
    (ARTICLES, Closed::Article),
    (QUANTIFIERS, Closed::Quantifier),
    (PRONOUNS, Closed::Pronoun),
    (CONJUNCTIONS, Closed::Conjunction),
    (PREPOSITIONS, Closed::Preposition),
    (AUXILIARIES, Closed::Auxiliary),
    (NEGATIONS, Closed::Negation),
    (DISTINCTIONS, Closed::Distinction),
    (ADVERBS, Closed::Adverb),
    (NUMBERS, Closed::Number),
    (COMPARATIVES, Closed::Comparative),
];

/// The value of a number word from `zero` to `twelve`.
pub(crate) fn number_word(word: &str) -> Option<u64> {
    const WORDS: [&str; 13] = ["zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten", "eleven", "twelve"];
    WORDS.iter().position(|w| word.eq_ignore_ascii_case(w)).map(|n| n as u64)
}

/// `true` for a token that is no word of the sentence: a quoted literal, a
/// code span, a number, a variable, a qualified or hyphenated name.
pub(crate) fn is_literal(word: &str) -> bool {
    word.is_empty() || word.contains(['"', '`', '#', ':', '/', '.', '_', '-', '>', '<', '=']) || word.chars().any(|c| c.is_ascii_digit()) || (word.len() <= 2 && word.chars().all(|c| c.is_ascii_uppercase())) || word.chars().all(|c| c.is_ascii_uppercase() || c == '-')
}

/// The class of a word, by its spelling.
pub fn classify(word: &str) -> WordClass {
    if is_literal(word) {
        return WordClass::Literal;
    }
    let lower = word.to_lowercase();
    CLASSES.iter().find(|(words, _)| words.contains(&lower.as_str())).map_or(WordClass::Open, |(_, kind)| WordClass::Closed(*kind))
}

/// Every closed-class word, for tests that try each of them in each place.
pub fn closed_words() -> Vec<(&'static str, Closed)> {
    CLASSES.iter().flat_map(|(words, kind)| words.iter().map(move |w| (*w, *kind))).collect()
}

/// `eventually` before a verb: the obligation is met at some later moment.
/// The temporal shape of every obligation without a deadline says so, and
/// the word adds nothing to the name of the action.
pub fn is_liveness(word: &str) -> bool {
    word.eq_ignore_ascii_case("eventually")
}

/// A preposition that orders an action and a thing: `before`, `after`, `during`, `until`.
pub(crate) fn is_order(preposition: &str) -> bool {
    ["before", "after", "during", "until"].iter().any(|w| preposition.eq_ignore_ascii_case(w))
}

/// Words in `-s` that are no plurals of a noun.
pub(crate) fn is_no_plural(word: &str) -> bool {
    ["does", "goes", "always", "besides", "sometimes", "perhaps", "towards", "afterwards", "whereas", "yes", "this", "thus", "alias", "basis", "series", "species"].contains(&word)
}

/// `true` for a preposition that excludes a part of what an action is
/// about: `send the file except the header`.
pub(crate) fn is_exclusion(word: &str) -> bool {
    matches!(word, "except" | "excluding" | "without")
}

/// A modifier that denies its head: a former member is no member.
pub(crate) fn is_privative(word: &str) -> bool {
    ["former", "fake", "false", "pseudo", "would-be", "alleged", "so-called", "non", "no", "not", "possible", "potential", "apparent", "missing"].contains(&word)
}

/// `the`, `a`, `an`, in any case.
pub fn is_article(word: &str) -> bool {
    ARTICLES.iter().any(|a| word.eq_ignore_ascii_case(a))
}

/// A word that builds the names of the classes that a nominal predicate
/// lists: an article, `of`, `or`, `and`.
pub(crate) fn builds_nominal(word: &str) -> bool {
    is_article(word) || ["of", "or", "and"].iter().any(|w| word.eq_ignore_ascii_case(w))
}

/// A word that selects the last occurrence of an event as the origin of a deadline.
pub(crate) fn selects_last(word: &str) -> bool {
    ["last", "latest", "previous"].iter().any(|w| word.eq_ignore_ascii_case(w))
}

/// What a verb says of the clause that follows it after `that`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ContentClass {
    /// The action makes the clause hold: when the action completes, the
    /// clause holds. `ensure that`, `guarantee that`.
    Establishing,
    /// The action is about the clause and says nothing of whether it holds:
    /// two such actions are one action only when their clauses are one
    /// clause. `report that`, `assume that`, and the verbs that examine a
    /// proposition: `verify that`, `confirm that`, `prove that`.
    Reporting,
    /// The action leaves the clause open to its subject: `allow the gate to
    /// open` permits the gate to open, and its denial forbids it.
    Permitting,
    /// The action obliges the clause: `require the gate to close`.
    Requiring,
}

/// The class of a verb, in its base form, that takes a content clause. A
/// verb that is in neither class takes no content clause.
pub(crate) fn content_class(verb: &str) -> Option<ContentClass> {
    // `verify`, `confirm` and `prove` examine a proposition and do not make
    // it hold: they stand with the verbs that are about a proposition.
    const ESTABLISHING: &[&str] = &["ensure", "guarantee", "establish"];
    const REPORTING: &[&str] = &["report", "state", "assert", "declare", "record", "indicate", "assume", "check", "decide", "verify", "confirm", "prove"];
    const PERMITTING: &[&str] = &["let", "allow", "permit", "enable"];
    if ESTABLISHING.contains(&verb) {
        Some(ContentClass::Establishing)
    } else if PERMITTING.contains(&verb) {
        Some(ContentClass::Permitting)
    } else if verb == "require" {
        Some(ContentClass::Requiring)
    } else if REPORTING.contains(&verb) {
        Some(ContentClass::Reporting)
    } else {
        None
    }
}

/// Whether a word is a unit of time or of size.
pub(crate) fn is_unit(word: &str) -> bool {
    const UNITS: [&str; 30] = ["ms", "millisecond", "milliseconds", "s", "sec", "secs", "second", "seconds", "min", "mins", "minute", "minutes", "h", "hour", "hours", "d", "day", "days", "b", "byte", "bytes", "kb", "mb", "gb", "kib", "mib", "gib", "tb", "%", "percent"];
    UNITS.contains(&word.to_ascii_lowercase().as_str())
}

/// The base form of a verb in the third person singular.
pub(crate) fn base_verb(verb: &str) -> String {
    if verb.starts_with('`') || verb.len() < 3 {
        return verb.to_string();
    }
    // `has` and `does` do not lose a final `s`.
    match verb {
        "has" => return "have".to_string(),
        "does" => return "do".to_string(),
        _ => {}
    }
    if let Some(stem) = verb.strip_suffix("ies") {
        return format!("{stem}y");
    }
    for ending in ["sses", "shes", "ches", "xes", "zes", "oes"] {
        if verb.ends_with(ending) {
            return verb[..verb.len() - 2].to_string();
        }
    }
    if verb.ends_with("ss") || verb.ends_with("us") || verb.ends_with("is") {
        return verb.to_string();
    }
    verb.strip_suffix('s').unwrap_or(verb).to_string()
}
