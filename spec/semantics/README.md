# Semantics of the trion patterns

[Names and target constraints](symbols.md)

This directory holds the meaning of the patterns (plan section 4.1):

- `core.md`: the rules that give a statement about individuals its meaning
  over concrete behaviours. The reading
  (`reading/typed.rs`, `ground.rs`), the reference evaluator and the check of
  the reading (`crates/trion-checker`) implement these rules apart.
- `readings.md`: the two readings of a package, what differs between them
  and how a package moves to the reading over individuals.
- this file: the inventory behind them, `spec/patterns/ledger.toml`, the
  syntax x meaning ledger of work item W01. It describes the reading of a
  package that declares no individuals and names
  the constructs of the reading over individuals.

## What the ledger is

One `[[pattern]]` table for each surface pattern that the implementation accepts
or deliberately rejects: 191 entries that describe the working tree of
2026-11-14 and say where the baseline 24cab2aa differed. It records what the
code does, not what is right. Each entry
names where the form is parsed, where its meaning is produced, which tests
assert that meaning, which claims its reading influences today (none where
the reading is absent), and what is undecided.

An `id` is a rule name of `crates/trion-language/src/reading/rules.rs` where one
exists. Otherwise it begins with `doc-` (a construct of `document.rs`), `rej-`
(a form that the parser or the reading rejects) or `variant-` (a surface
distinction that `rules.rs` reports under a broader rule, named in `rule`, but
that is lowered or classified differently).

`crates/trion-language/tests/pattern_ledger.rs` keeps the ledger honest: every
rule name that `Walk` can insert has an entry, every entry has the required keys
and allowed values, identifiers are unique, and every `parser`, `lowering` and
`evidence` pointer names a function or a test that exists.

## The classification of `meaning`

Every constituent of an accepted normative sentence is exactly one of:

| value | rule |
| - | - |
| `rule` | A named reading rule consumes the construct and it reaches the contract or the model: a formula, a bound, an order, an axiom, or the key of an atom. `lowering` names where. A rule may still have open questions. |
| `nonnormative` | The construct carries no constraint by design (`section`, `note`, `cite`, `even when`, `eventually`). The status must be shown to the user. |
| `unresolved` | The construct is accepted, and its meaning is dropped, kept only inside an uninterpreted name, changed, or merely reported. While one stands in a normative statement, the statement must not count as verified (W02). |
| `rejected` | The parser refuses the form (`parse = "rejected"`), or the reading refuses the statement with a diagnostic (`parse = "accepted"`). |

`parse = "partial"` marks a form that is read only in some positions or only
with a declaration elsewhere in the package.

## The priority of evidence

An entry is based, in this order, on (1) the parser branch, (2) tests with an
assertion, (3) the lowering code, (4) `spec/*.trion`. A comment or a statement
of the specification alone never makes an entry `rule`. `evidence` lists only
tests that assert what a form means (a contract, a conflict, a refusal); a test
that only shows that a form parses is not evidence, and 31 entries have none.
A passing test fixes current behaviour; it is not evidence that the reading is
correct (plan section 3).

## Unresolved patterns and the gate

A pattern without a meaning rule must not pass into a verified result (plan W01,
W02). The gate is the conversion: a package with an error does not conform to
the language, `trion` writes no MMT form for it, and so `trioc` has no
obligation to prove. Each pattern is connected to the gate in one of three ways.

**Stopped by the reading.** The statement is rejected with
`UNSUPPORTED_SEMANTICS` (`reading/rules.rs::UNRESOLVED`, `grounding.rs::unvisited`),
so the conversion fails. These were accepted and verified at the baseline;
the ledger entry of each records the lost capability and the migration.

| id | what was lost in the reading | owner |
| - | - | - |
| `concession-while-gerund` | `…, while retaining X` was kept as a string and reached no rule | W03 |
| `role-rate` | `per <unit>` reached the action name only; `3 per second` contradicted `5 per minute` | W07 |
| `role-exclusion` | `except`, `excluding`, `without <noun>` after a modal verb: the bare action was obliged too | W03, W05 |
| `role-by` | `respond by the deadline` was no deadline | W03, W06 |
| `predicate-able-to` | an uninterpreted value of the subject, related to no action and no permission | W03 |
| `content-of-noun` | `the proof that <clause>` kept the clause inside the noun's name | W03 |
| `frame-before` | a preposed `Before X,` was the free atom `Event(before X)`; the contract was vacuous | W06 |
| `subject-counted-descriptive` | `At most 5 users have a profile.` folded the count into the subject name | W07, W08 |
| `object-zero-or-more` | `shall send zero or more reports` obliged sending | W07 |
| `frame-counted-event` | `After 3 failed retries,` named one event that nothing related to a count | W06, W07 |
| `condition-only-if-denied` | `shall not stop only when C` was `Forbid → C`, which not forbidding satisfied | W03 |
| `variant-proportion` | a share in a statement about no declared type was a quantity that nothing tied to a behaviour | W07 |

**Stopped as a meaning obligation.** The statement is read, the word is reported
as `inexpressible-property` (an error since W02), and the conversion fails: `variant-quality-without-measure` (`secure`, `quickly`),
`variant-run-relation` (`deterministically`), `variant-optimum-or-preference`
(`as fast as possible`), `variant-proportion-word` (`usually`).

**Not stopped yet.** None. At the baseline a package could be verified
with a part of its meaning left out or changed by these routes; each is
closed, and its entry of the ledger states the capability that a rejection
takes away:

| id | what happened | closed by |
| - | - | - |
| `frame-counted-event` (was `variant-frame-after-counted`) | `After 3 failed retries,` kept the count in the event name | rejected (`UNSUPPORTED_SEMANTICS`) |
| `predicate-enumeration` | nothing said that an attribute holds some listed value: three prohibitions of the three values of an enumeration were consistent | a rule: the subject has exactly one listed value at each moment |
| `condition-only-if` | `shall stop only when the door is open` was satisfied by marking the action forbidden or discouraged | a rule: where the condition fails the action is forbidden; `shall not … only when` is rejected (`condition-only-if-denied`) |
| `content-established` | `shall verify that P` made P an axiom | a rule: `verify`, `confirm` and `prove` are about their clause; only `ensure`, `guarantee` and `establish` make it hold |
| `variant-frame-after-once-upon-on` | the one-event rule covered `When`/`If` only: `After A occurs and B occurs,` was accepted | the rule covers each opener; tests assert the contract of each |
| `variant-proportion` | the population and the window of a share were names inside the key of a quantity that nothing tied to a behaviour | rejected without declared individuals (`share-of-representative`); with them the formulas count the activations, and one measure names one population (`variant-share-of-activations`) |
| `doc-diagram-kind` | `preserves "..."` had to be present and was never checked | nonnormative, and each result names it as declared and not checked |
| `doc-compatibility` | only the source name and revision string were compared | nonnormative for the agreement of the forms, and each result names it as declared and not checked |

Closed earlier: `role-after` (an `after` cycle of one activation was kept;
an occurrence now belongs to an activation when it opens it or lies after
it, acceptance case A04b), and `definition` (a state that a definition
gives by an action that is done had no consequence against a prohibition of
the action; a holder that is forbidden an action is not disposed to it,
acceptance case A03b).

The entries of the ledger that are `rule` with an open question are no
routes of this kind: the question is which of several meanings the
language should give, and the meaning that the reading gives today is stated
in the entry and asserted by its tests. `crates/trion-cli/tests/closed_routes.rs`
holds, for each route above that became a rule, two packages that the rule
tells apart.

In a package that declares its individuals a
statement that names a declared type has a record of its reading, is
rejected as outside the typed fragment, or is a statement about the domain,
and the check of the reading refuses a package where none of the three
holds (`derivation-refused`).

## Open questions by owning work item

An `open` string of the ledger that states a question begins with the work
item that owns it; one that begins with `closed` records a question that was
decided, with the date and the behaviour before.

| owner | patterns with an open question |
| - | - |
| W01 | `doc-include` |
| W02 | `recommendation`, `recommendation-against`, `description`, `variant-quality-without-measure`, `variant-optimum-or-preference`, `flow-choice`, `doc-detailed-by`, `doc-overrides`, `doc-weight`, `doc-check`, `doc-example` |
| W03 | `obligation`, `prohibition`, `permission`, `action`, `action-passive-or-state`, `description`, `description-adverb`, `predicate-words`, `predicate-nominal`, `predicate-enumeration`, `predicate-prepositional`, `predicate-able-to`, `definition`, `relation`, `frame-where`, `frame-if`, `clause-copular`, `clause-verbal`, `condition-only-if`, `condition-if-and-only-if`, `concession-even-when`, `concession-while-gerund`, `purpose`, `variant-quality-without-measure`, `noun-phrase-bare`, `noun-phrase-article`, `noun-phrase-none`, `noun-phrase-counted`, `noun-phrase-reference`, `noun-phrase-modified`, `noun-phrase-kind-word`, `noun-phrase-of`, `content-of-noun`, `content-of-verb`, `content-established`, `content-permitted`, `content-required`, `role-recipient`, `role-means`, `role-topic`, `role-source`, `role-goal`, `role-location`, `role-agent`, `role-other`, `variant-exclusion-role`, `variant-by-outside-passive`, `variant-bare-cardinal`, `doc-namespace`, `doc-primitive`, `doc-term`, `doc-predicate`, `doc-alias`, `doc-extend`, `rej-unread-function-word`, `rej-ungrounded-statement` |
| W04 | `concession-even-when`, `doc-example` |
| W05 | `permission`, `actions-either`, `actions-and`, `statements-and`, `relation`, `frame-when`, `clause-verbal`, `variant-postposed-condition`, `exception-unless`, `condition-only-if`, `noun-phrase-article`, `noun-phrase-universal`, `noun-phrase-reference`, `noun-phrase-of`, `noun-phrases-and`, `noun-phrases-or`, `relative-verbal`, `relative-copular`, `relative-object-gap`, `relative-whose`, `relative-where`, `content-of-noun`, `content-permitted`, `variant-exclusion-role`, `composition-all`, `composition-some`, `composition-one`, `composition-flow`, `flow-choice`, `variant-only-focus`, `variant-pronoun`, `variant-explicit-variable`, `doc-statement-id`, `doc-shared-context`, `doc-for-each`, `doc-overrides`, `doc-default`, `doc-concept`, `doc-diagram-kind`, `doc-diagram`, `rej-flow-cycle` |
| W06 | `obligation`, `prohibition`, `recommendation`, `action-passive-or-state`, `frame-where`, `frame-while`, `frame-when`, `frame-if`, `clause-verbal-denied`, `clauses-and`, `clauses-or`, `exception-unless`, `condition-if-and-only-if`, `content-established`, `role-source`, `variant-by-outside-passive`, `role-deadline`, `deadline-origin`, `role-delay`, `role-duration`, `role-before`, `role-after`, `role-until`, `order-of-occurrence`, `occurrences-in-a-row`, `timing-immediately`, `timing-always`, `timing-eventually`, `variant-frame-after-once-upon-on`, `frame-counted-event`, `variant-frame-before`, `variant-frame-during`, `variant-frame-until`, `variant-frequency`, `composition-sequence`, `doc-otherwise`, `rej-deadline-without-origin`, `rej-time-word-without-reading` |
| W07 | `predicate-comparison`, `measure-quantity`, `measure-bounded`, `measure-named`, `variant-proportion-word`, `noun-phrase-counted`, `role-rate`, `frame-counted-event`, `variant-bare-cardinal`, `variant-count-per-thing`, `variant-counted-descriptive-subject`, `variant-zero-or-more-object`, `variant-linear-quantity`, `variant-proportion`, `doc-measure`, `rej-proportion-without-measure` |
| W08 | `relation`, `existence`, `noun-phrase-existential`, `noun-phrase-counted`, `variant-exactly-n`, `variant-counted-descriptive-subject`, `variant-no-two`, `variant-number-of-and-total` |
| W09 | `predicate-comparison`, `variant-run-relation`, `noun-phrase-universal`, `noun-phrase-existential`, `variant-linear-quantity`, `variant-same-for-same`, `doc-environment`, `doc-system` |
| W10 | `doc-diagram-kind`, `doc-compatibility` |
| W11 | `variant-bare-cardinal`, `doc-detailed-by`, `doc-source`, `doc-cite`, `doc-note`, `doc-ref`, `doc-compatibility` |
| W12 | `predicate-enumeration` |
| W13 | `doc-package`, `doc-use` |
| W14 | `doc-role`, `doc-bind`, `doc-classify` |
| no owner: a missing test or a dead rule name | `permission-denied`, `relative-verbal-denied`, `rej-may-not`, `rej-no-with-may`, `rej-unsupported-modal`, `rej-counted-normative-subject`, `rej-multiple-event-conjuncts`, `rej-frame-on-definition`, `rej-negated-alternatives`, `rej-words-without-formal-reading`, `rej-without-gerund`, `rej-within-bounded-measure`, `rej-descending-between`, `rej-unknown-number-word` |

## Changing the ledger

Add or change an entry in the same change as the parser branch, the reading
rule or the test that it describes. Move a pattern to `rule` only with a test
that gives one concrete behaviour to two sentences and tells them apart
(plan section 4.1). Moving a pattern to `rejected` to stop a false success is
recorded with the lost capability and the migration (plan W01).

## Where the implementation differs from the specification

The specification (`spec/*.trion`, `AGENTS.md`) and the theory behind it
(`formal/Trion/Merging.lean`, `formal/Trion/Document.lean`) are the
baseline. Where the implementation differs, the implementation is wrong.
No difference is known. Each point below was a difference, and each names
how the implementation meets the specification now and the tests that show it.

| specification | implementation | tests |
| - | - | - |
| `trion` converts and proves nothing; `trioc` proves the proof obligations of the MMT form (`TOOL-PROVE`, `PROOF-FROM-MMT`) | `trion --out` writes the MMT archive and the formats that `--format` names; `trioc prove` decides each obligation of the form and gives one result for each. No other search exists: the codes of the former in-process search are gone, and `relation-not-local` is a property of the reader that `--properties` reports | `crates/trion-cli/tests/certificate.rs`, `crates/trion-cli/tests/proof_engine.rs`, `crates/trion-cli/tests/code_fixtures.rs` |
| Output formats are MMT, Markdown, HTML or an extension format (`TOOL-CONVERT`) | a format that `trion` does not write is the program `trion-format-NAME` next to `trion` or on the path: it reads the report on standard input and writes into the output directory. `trion-format-rust-test` writes one ignored test for each guarantee | `crates/trion-cli/tests/formats.rs`, `crates/trion-format-rust-test` |
| The consistency of a document is one proposition about whole behaviours within the bound (`Document.lean`, `consistent`) | the obligation `consistency` asks, for every behaviour of the environment that the assumptions allow, for a behaviour of the system that keeps every guarantee over the whole trace. The reactive reading, which `Document.lean` names as an addition, is the obligation `realizability` for a response that must come before an occurrence that the environment decides (`VERIFY-REALIZABILITY`) | `crates/trion-verification/tests/proof_engine.rs`, `crates/trion-cli/tests/temporal_order.rs`, acceptance case A19 |
| Responsibility decides the assumption; an assumption is distributed to the guarantees of its scope, the document or a shared condition block (`SENTENCE-RESPONSIBILITY`, `COMPOSITE-ASSUMPTION-DISTRIBUTED`) | each contract states its role, and an assumption states its scope (`in_document`, `in_block`); an assumption inside a block is distributed to the guarantees of that block and of the blocks inside it only | `crates/trion-verification/tests/draft_rules.rs`, `crates/trion-cli/tests/contracts.rs` |
| A simple sentence is exactly one contract, and composite vocabulary has no meaning of its own (rules 1 and 2, `CATALOG-RULE-ONE`, `CATALOG-RULE-TWO`) | each reading example of the catalog is held to both rules on every conversion, and `--properties` holds every statement of a package to them (`sentence-not-one-contract`, `composite-not-its-expansion`). the size of the domains of individuals is a bound and no part of a contract: the contract of a sentence about individuals is one schematic contract over variables named by their nouns at every size. The declaration of types is vocabulary: `of` between two declared types is their relation, and a sentence that relates no two declared types has the same formulas without the declaration | `crates/trion-cli/tests/two_rules.rs`, `crates/trion-verification/tests/schematic_contracts.rs` |
| A contract is a set of whole behaviours, the time of each response included (the bounded proof obligation of `AGENTS.md`) | each contract of the MMT form carries its time (`timed`): its activation and the time of each response, and the obligations decide them over the moments of the trace | `crates/trion-cli/tests/contracts.rs`, `crates/trion-cli/tests/certificate.rs` |
| Correctness and completeness are defined against a reference (`VERIFY-CORRECTNESS`, `VERIFY-COMPLETENESS`) | a statement is the reference of the statements that detail it, and a quote of a source that reads as trion sentences is the reference of the statements that cite it: each has an obligation of correctness and one of completeness, in the sense of `Document.lean`. A value of a closed attribute that no statement covers is `missing-case`, a warning and no result about completeness (`VERIFY-MISSING-CASE`, `VERIFY-NO-REFERENCE`) | `crates/trion-cli/tests/sources.rs`, `crates/trion-verification/tests/proof_engine.rs` |
| A certificate is issued in each requested format that can express the result, and a format that cannot says so (`CERTIFICATE-PROVED`, `CERTIFICATE-INEXPRESSIBLE`) | `smt2` and `moxi` state each question with its expected answer; `alethe` and `cpc` restate the refutations of trion's own solver (`proof::derive`), a satisfiable question by the refutation of its witness check. trioc runs no other program (`PROVER-OWN`); Carcara and Ethos check the proofs in the tests | `crates/trion-cli/tests/certificate.rs`, `crates/trion-verification/tests/proof_formats.rs` |
