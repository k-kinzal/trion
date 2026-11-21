# Names and target constraints

The work starts at `4da7c4e6a57c409db178c506d99665b19aeae511`. Package declarations identify packages by name. The reader applies the same rules to all packages. [Language rules](../../spec/semantics/symbols.md)

## Package and proof identity

`package NAME` declares the name. `refer DEPENDENCY` resolves the manifest dependency without importing its contracts. `apply` selects the relevant statements and records the package, mapping and source locations. The standard libraries use the same rules at their usual paths.

The saved proof subject stores the package input digest, the generated obligation digest and the proof bounds. The input digest covers the package files and manifests, including dependencies. The obligation digest is computed from the questions and formulas read by `trioc`. Propositional artifacts reparse their saved source and compare the resulting Core and source mapping when they are read.

## Migration

| Source | Classification | Effect |
| --- | --- | --- |
| `spec/trion.trion`, trion language | Semantic correction | The legacy definition introduced a domain atom for the formal language classification and a state atom for the controlled language classification as axioms. The new statements place both constraints on the trion language as guarantees. The nominal regression requires both properties of the same representative and refutes a negative assertion of either property. |
| `spec/trion.trion`, trion processor | Semantic correction | The old axiom encoded a program classification and a compound action conditional on existence. The new document states the classification, requires reading each specification and retains the separately stated conversion obligation. It therefore no longer leaves reading conditional on the old representative existence trigger. |
| `spec/trion.trion`, contract theory | Semantic correction | The old definition added domain atoms about the theory and `TRION-THEORY` used a different action key from the full name. The revised obligation names `assume-guarantee contract theory` directly. Its citation identifies the report that motivates the requirement. The action retains the trion processor as its system actor. [Inria bibliography](https://prod-rex-app.inria.fr/report/2016/hycomes/bibliography.html) |
| Representative alias sample | Semantics preserved | Swapping `codec` for its alias leaves the action key, guarantee, and responsibility unchanged. |
| Alias in a bounded example | Semantics preserved | The example retains the network's responsibility for its status and return event, and the codec's responsibility for starting. Changing `codec` to its alias leaves each assumption, guarantee, scope, and timing description identical. |
| `spec/words.trion` and `spec/grammar.trion` | Explicit rules | The self-specification has separate requirements for alias resolution, kind checking, specification references, class expansion, and reading target descriptions. The grammar table describes the nominal and definition rules. |
| `stdlib/software` | Semantic correction | The library puts the classifications, ownership relationships and behaviour into ordinary target constraints. It uses representative existence conditions and retains the arguments and manner of each action. |
| `stdlib/formal` | Semantic correction | The library separates the classifications, count and ownership requirements, truth conditions and behaviour. Its mathematics is expressed at the granularity of the representative reading. |
| `stdlib/grpc` | Existing usage preserved, explicit binding added for references | `use grpc` and `bind … as grpc.service` retain the existing gRPC form check. `refer` makes the pinned form role available to `bind`, with checks scoped to the bound target. |
| `stdlib/ears` | Existing usage preserved, explicit binding added for references | `use` applies the existing namespace-wide classification. A pinned reference exposes `ears.syntax` as a target-specific binding. The proof report traces the binding separately from the package's ordinary contracts. |

The migration checks added one prohibition at a time to copies of the baseline and revised specifications. `The trion processor shall not read each specification.` left the baseline's 14 bounded obligations provable. The migrated package refuted consistency and identified `NEGATIVE-READ` and `TRION-READ`. Prohibiting the processor from following `the assume-guarantee contract theory` produced the same difference, with `NEGATIVE-THEORY` and `TRION-THEORY` in the migrated refutation. The theory probe declared the full name in both copies. A separate migrated copy with `The trion language is not a controlled natural language.` refuted consistency with `TRION-CONTROLLED-LANGUAGE`. The other 13 obligations were proved in each migrated probe.


### Standard libraries

The `software` and `formal` packages are available directly at their standard library paths.

| Software definition | New clauses and scope |
| --- | --- |
| `program` | `PROGRAM-TYPE` classifies an existing program as text. `PROGRAM-RUN` requires the computer to run it when the program exists. |
| `command` | `COMMAND-TYPE` gives the program classification. `COMMAND-RUN` keeps the person, command and manner in the same action key. |
| `subcommand` | `SUBCOMMAND-TYPE` supplies the command classification. `SUBCOMMAND-PART` names the relationship to its command. |
| `option` | `OPTION-TYPE` classifies a word, `OPTION-PART` names its command line, and `OPTION-EFFECT` names the change to the command's behaviour. |
| `exit status` | `STATUS-TYPE` classifies the result as a number. `STATUS-RETURN` requires the command to return an existing exit status. |
| `editor` | `EDITOR-TYPE` classifies a program. `EDITOR-DISPLAY` includes the recipient of its display action. |
| `language server` | `SERVER-TYPE` classifies a program. `SERVER-EDITOR` states which kind of target it serves. |
| `file` | `FILE-TYPE`, `FILE-NAME`, and `FILE-KEEP` state its classification, naming relationship and the computer's action. |
| `directory` | `DIRECTORY-TYPE` classifies a set. `DIRECTORY-NAME` adds the naming relationship. `DIRECTORY-CONTENTS` classifies existing members and permits an empty directory. |
| `path` | `PATH-TYPE` classifies a name. `PATH-LOCATES` explicitly permits either kind of target. |
| `digest` | `DIGEST-VALUE` states the relationship between the digest and file. Its SHA-256 name identifies the relationship. |

The preceding clauses correct a reading in which a legacy definition could add vocabulary axioms and imply facts through the spelling of a kind. The new rules state exactly which representative and arguments they constrain. Existence tests connect the statements to the existence of the named representative. A successful check of these contracts gives no calculation rule for a digest and no uniqueness or totality for the locating relation.

| Formal definition | New clauses and scope |
| --- | --- |
| `formula`, `atom` | `FORMULA-TYPE`, `FORMULA-TRUTH`, `ATOM-TYPE` and `ATOM-PART` expose the classification, truth value and exclusion of a formula as a part of an atom. |
| `conjunction`, `disjunction`, `negation` | The `-TYPE` claims classify the respective formulas. The `-TRUTH` clauses state their two-way truth conditions separately. |
| `implication` | `IMPLICATION-TYPE` gives the category. `IMPLICATION-PREMISE` and `IMPLICATION-CONCLUSION` explicitly require one of each part. |
| `formula set`, `model` | `SET-TYPE` and `SET-MEMBER` state the category and membership. `MODEL-TYPE` classifies a situation and `MODEL-SAT` states the satisfaction requirement. |
| `contract`, `assumption`, `guarantee` | `CONTRACT-TYPE` classifies a pair. `CONTRACT-ASSUMPTION` and `CONTRACT-GUARANTEE` require one formula in each role, whose relationship to the contract is stated by `ASSUMPTION-SUPPOSE` and `GUARANTEE-REQUIRE`. |
| `inference rule`, `derivation` | `RULE-TYPE` and `RULE-DERIVES` give classification and action. `DERIVATION-TYPE` and `DERIVATION-STEPS` give classification and structure. |
| `contradiction`, `proof` | `CONTRADICTION-SAT` denies satisfaction of the classified formula. `PROOF-ACCEPT` requires the checker to accept the classified derivation. |
| `proof checker`, `calculus` | `CHECKER-STEPS` states the checking action of the program. `CALCULUS-MEMBER` classifies existing members of the set. |

These are semantic corrections from vocabulary axioms to authored target constraints. Truth conditions that were originally ordinary sentences retain their explicit two-way form. Representative class checks can exclude a denial of the written classifications. They do not establish a quantification over arbitrary formula size, trace length or derivation length.

Seven pre-existing truth conditions preserve their stated contracts. The implication, two formula-set conditions and four calculus conditions have equal assumptions, guarantees, responsibility, bounds of the stated formula, and scope in the baseline and revised readings. Three existing sentences about satisfaction and vacuous holding now use the same representative presence fact as an explicit existence sentence. Their old trigger used an independent `exists` event spelling. This change is a semantic correction to the representative interpretation. The comparison of stated contracts makes no claim that the two packages have the same background axioms.

### Retained definitions

| File | Definition inventory |
| --- | --- |
| `spec/trion.trion` | `documentation of a system` carries an owner and a purpose. `evidence`, `origin` and `rationale` describe provenance and motivations. `validity of a specification` relates a quality to a problem. Definitions outside the class abbreviation grammar require separate constraints. |

The self-specification now states the classifications of `statement`, `author` and `reader` directly. It states the relation of a statement to the trion language and the actions of authors and readers separately. The two system actors in the introduction have explicit existence claims. The EARS library states its six form descriptions directly and keeps the corresponding citations.

## Authoring exercises

The exercises were written and converted locally by the implementation author. They are examples of the authoring workflow.

| Task | First attempt and feedback | Revision and resulting constraint |
| --- | --- | --- |
| Describe a service's classifications, ownership, count and behavior. | The draft tried one sentence for both classes, then individual sentences for membership, queue count and storage. The initial smoke run identified `also` as an unread word despite the parsed relative. The structured predicate walk now reads that relative. | The positive example writes those constraints immediately after declaring responsibility and station existence. It produces `class telemetry service(station)`, `class monitoring service(station)`, `relation member(station, network)`, a queue count equal to one, and a storage guarantee. |
| Reuse a receipt service for two collectors and introduce a violation in the second. | A pinned reference alone leaves the collectors unconstrained by the profile. An application with just `reply = receipt` reports the missing endpoint mapping. | Explicit endpoint assignments create `collector1\|send receipt` and `collector2\|send receipt`. Adding a prohibition to the second names the second application in the refutation. |
| Keep the first of two identically named codecs, use it to send a report and require recovery when the network returns. | `The codec is a monitoring service` was ambiguous. `term marker: value` followed by `The marker shall send a report` had a kind conflict. `The codec is able to recover` asked for unsupported capability semantics. The first repair also elicited `system-undeclared`. | The author qualified `first::codec`, used the codec as the actor, wrote the intended recovery condition, and declared responsibility in each actor's namespace. The resulting formulas are listed below. |
| Reuse a condition that selects telemetry and monitoring services. | Two successive abbreviations gave the class formula a name and an alternate, more specific name for use in the condition. No warning about their position or number was emitted. | The condition of the summary action expands to the conjunction of the two station classifications. The expansion adds no independent predicate to the contract. |
| Describe how starting the API fulfils its operational-state requirement. | A first descriptive attempt read `operational` as a status-domain value. After the requirement was phrased as an obligation, the refinement reported a bounded behaviour in which `start` occurred and the operational status was absent. | Add the operational state as a detail of the reference requirement. The details now constrain both the action and the state. The bounded refinement is proved. A temporal relationship from a particular invocation to an ensuing status would need its own constraint. |

The positive example and its miniature dependency are executable. [Telemetry example](../../spec/examples/symbols/trion.trion)

The first repair exercise was converted with `trion --json`. `AMBIGUOUS_TERM` named `first` and `second` and suggested `first::codec`. The editor's quick fix offers the qualified spelling of each owner. `vocabulary-kind-conflict` reported `value` where the sentence used `marker` as an entity. `UNSUPPORTED_SEMANTICS` named `predicate-able-to` and explained that the reader could express permission but had no capability rule. The requested recovery was conditional behavior, so the revision uses the network's return as a trigger. `trion --properties --json` accepted the final document without diagnostics.

```trion
package exercise
namespace exercise.first:
    system codec
    There is a codec.
    The codec is a service.
namespace exercise.second:
    environment codec
    The codec is a tool.
namespace exercise.app:
    use exercise.first
    use exercise.second
    environment network
    [MONITOR] The first::codec is a monitoring service.
    [SEND] The first::codec shall send a report.
    [RECOVER] When the network returns, the first::codec shall recover.
```

| Statement | Assumption | Guarantee |
| --- | --- | --- |
| `MONITOR` | `⊤` | `class app::monitoring service(first::codec)` |
| `SEND` | `⊤` | `Act(first::codec\|send report) ∧ ¬Forbid(first::codec\|send report) ∧ ¬Discouraged(first::codec\|send report)` |
| `RECOVER` | `Event(app::network return)` | `Act(first::codec\|recover) ∧ ¬Forbid(first::codec\|recover) ∧ ¬Discouraged(first::codec\|recover)` |

## Acceptance evidence

The regression cases use a trace of 3 moments and a requested bound of 2 for declared individuals. The CLI tests check the reported results and, where applicable, the resulting formulas and the MMT subject. [Regression tests](../../crates/trion-cli/tests/symbols.rs)

| ID | Evidence and boundary |
| --- | --- |
| A01 | Telemetry example covers inferred classes, ownership, a numerical possession bound and an independent storage requirement. |
| A02 | The namespace tests resolve an inferred export through an alias to the owning namespace. A second same-named export triggers ambiguity in descriptions, definition bodies, alias targets and application mappings. A qualified missing export is rejected. The JSON and MMT round trip preserves alias identity, the target's constraint origins and an unused predicate's signature. |
| A03 | The compound nominal test proves consistency with two classifications and refutes the same document with a negative classification on the same subject. |
| A04 | The declared vocabulary and definition tests reject kind conflicts. The signature tests check arity, declared subject and argument types, imported predicates, aliases, nominal roles, triggers, passives and relative clauses. The same spelling resolves to distinct predicates in separate owning namespaces. |
| A05 | The representative nominal regression compares the compound guarantee to the conjunction of corresponding simple guarantees and checks that another language can belong to only one class. In the bounded tests the solver excludes the symmetric difference over a shared carrier, including the assumptions and guarantees of a compound condition. A separate test checks explicit existence and the system's responsibility for both the population and the assertions. |
| A06 | A prohibition of the independent storage action provides a counterexample. An explicit refinement from starting an API to its operational state fails with a checked example showing the action and the absent state. Adding the state as a requirement of the details proves that refinement. |
| A07 | The receipt-profile case with a reference alone is consistent with a local prohibition. |
| A08 | One positive mapped application is consistent. A local prohibition of a mapped action refutes the matching application. Tests cover a mapped declared predicate, a transitive `use` requirement, a derived class expanded at the mapped subject, and positive and negative checks of a mapped refinement. An explicit binding to referenced `grpc.service` checks the method name of the bound API. |
| A09 | The two distinct action keys and the second application identifier appear in the representative end-to-end test. Two mappings of the same individual type also give a refutation identifying the second application. The nested-application case maps a shared interface through two targets and tracks their different environmental assumptions. |
| A10 | Aliasing preserves the action formula. Changes to the mapping or dependency content change the input digest. Changes to the proof questions or formulas change the obligation digest. |
| A11 | The tests reject a missing endpoint assignment, mismatched responsibility, an incompatible predicate signature, a value where the source expects an object, and a representative where the source expects a declared individual type. Missing mandatory syntax from an explicitly bound source role reports the mapped subject and the application. A representative role whose activation guard is false leaves the subject free from that form requirement. |
| A12 | A URL cited as evidence leaves exactly the local constraint and an empty application list. Referencing EARS preserves its own source coverage. An explicit binding to `ears.syntax` checks just the bound target using the source enumeration. |
| A13 | Adding an unused name, alias and pair of fresh derived classes leaves the old contract formulas unchanged in the tested package. An unused plural-spelled declaration in another namespace preserves the old action key. An alias for `buffer` leaves `buffer status` independent. |
| A14 | Two adjacent forward-referencing definitions and a chain of 66 definitions are accepted. The implementation has no count rule. |
| A15 | Unknown or ambiguous target classes, a capability in a right-hand side, kind conflicts, redeclarations and cycles are rejected. The cycle test closes a chain of 66 otherwise-unused definitions. |
| A16 | The abbreviation makes a negative statement contradict the asserted body. A one-way inclusion does not imply membership in the narrower class. |
| A17 | The responsibility test checks an environment assumption, a system guarantee and conditions about each. A two-instance test denies one environment's assumption and checks prohibitions in both instances. The active instance's prohibition refutes consistency. An applied shared block narrows its assumption to that block. The definition expansion is recorded separately from the formulas. |
| A18 | The MMT reader preserves application metadata and content identity. The self-specification proofs and denial probes cover the migrated statements. Both structured libraries have tests that deny migrated classifications or behavior. The unmigrated self-specification clauses and semantic limits are listed below. |
| A19 | The finite-domain test compares a nonempty user class and empty guest class against the same case with a guest existence assertion. A mapped inclusion retains its target carrier through independent re-reading at a requested scope of 2 and excludes the corresponding denial. Mixed responsibility declarations for a shared carrier are diagnosed. |
| A20 | The regression permits a third value in the open case and refutes it under explicit enumeration. The independent classifications test covers nonexclusive membership. |

## Verification commands

The telemetry package converts and its two bounded obligations prove with `trion --properties --json --out OUTPUT spec/examples/symbols` followed by `trioc prove OUTPUT --json`. Direct conversion succeeds for `software`, `formal`, `ears` and `grpc`. Running `trion formalize`, `trioc analyze` and `trioc replay` on `tests/fixtures/propositional/card.cnl` reproduces the checked entailment.

`cargo check --workspace --all-targets --offline --locked` passed. The selected Rust suites passed 111 cases after rerunning the form, document and ledger fixtures. The shared grammar and VS Code tests passed 26 and 11 cases respectively. IntelliJ's suite passed 31 of 34 cases. Two preview processes timed out and the glossary integration used a CLI command that the entry point does not provide.

The earlier self-hosting measurements below describe the snapshot before all documents used the same reader. Running `trion --json .` with the current reader reports 260 diagnostics, including 120 unsupported definition bodies, 95 kind conflicts, and 10 failing examples. The member-classification probe reads the current `SPEC-SET` and `SPEC-MEMBER` statements and refutes the denial of membership with the representatives present.

| Command | Result and scope |
| --- | --- |
| `cargo check --workspace --locked --offline` | Passed with the resolved symbol metadata in JSON and MMT. |
| `cargo test --offline --locked -p trion-cli -p trion-language -p trion-lsp -p trioc-cli --test symbols --test pattern_ledger --test lsp --test mmt_form --no-fail-fast` | 86 passed, including all 47 symbol cases, 20 LSP cases, 8 ledger cases and 11 MMT cases. The MMT round trip checks shared alias identity, an unused predicate's signature, target provenance, nested mapping metadata and agreement with the JSON report. |
| `cargo test --offline --locked -p trion-cli -p trion-checker -p trion-verification --test project --test sources --test individual_readings --test definition_rules --test forms --test surface --no-fail-fast` | 99 passed. Covers legacy definitions and imports, source coverage, bounded individual reading, role forms and the independent evaluator. |
| `cargo test --offline --locked -p trion-cli --test symbols migrated_formal_concepts_exclude_a_denial_of_their_classifications -- --exact` | Passed with a comparison of seven preserved contracts and separate bounded refutations of denials for 17 migrated concepts. |
| `trion --properties --json --out OUTPUT .` and `trioc prove OUTPUT --json` | All 14 self-specification obligations proved at the recorded bounds. The reader reports a legacy kind warning for `specification` and a spelling warning for `defines` and `refines`. |
| `cargo test --locked --offline -p trion-language -p trion-lsp -p trion-cli -p trion-checker -p trion-verification --test pattern_ledger --test lsp --test individual_readings --test forms --test surface --no-fail-fast` | 52 passed. Covers the ledger, 19 LSP cases including signature hover, the independent reader, and required role forms. |
| `trion --properties --json --out OUTPUT .` and `trioc prove OUTPUT --json` | The self-specification conforms. All 14 obligations are proved at the recorded bounds.  |
| `cargo test --offline --locked -p trion-cli -p trion-lsp -p trion-verification --test symbols --test sources --test project --test mmt_form --test self_hosting --test reading_account --test vocabulary_rules --test vocabulary --test lsp --no-fail-fast` | 166 passed, including 23 symbol cases and 18 LSP cases. Covers the representative fragment, scope and type diagnostics, mapped class and relationship constraints, reference-only gRPC role binding, MMT round trip, and bounded inclusion and existence. |
| `cargo test --offline --locked -p trion-cli -p trion-lsp -p trion-verification --test symbols --test project --test sources --test lsp --no-fail-fast` | 109 passed after the mapping diagnostics began reporting expected and actual kinds. |
| `cargo test --offline --locked -p trion-cli --test self_hosting` | 12 passed. The migrated self-specification proved all 14 obligations at 3 moments and a bound of 3 individuals. |
| `cargo test --offline --locked -p trion-cli --test mmt_form` | 11 passed, including external MMT validation of the self-specification. |
| `cargo test --offline --locked -p trion-cli -p trion-lsp -p trion-verification --test self_hosting --test mmt_form --test language_spec --no-fail-fast` | 61 passed after revised rule statements were added to the self-specification. |
| `trion --properties --json --out /tmp/trion-symbols-final-example spec/examples/symbols` and `trioc prove /tmp/trion-symbols-final-example` | Conversion and MMT re-reading succeeded. Consistency and compatibility both proved at 3 moments over representatives. The external MMT builds of the telemetry example and the gRPC binding probe succeeded. |
| `trion --format html --out /tmp/trion-symbols-html spec/examples/symbols` | The glossary links `station` to its local target constraints and shows `collector1`'s applied requirement with its source file and line. The `monitored endpoint` entry names its expansion source and links its use. |
| `trioc prove NEW-FORM --against PREVIOUS-RESULT.json` after a change to one target mapping | Refused the saved result with `result-stale` due to the changed revision. |
| The example with a second-collector prohibition | One obligation proved and one refuted. The refutation names the prohibition and `receipt-profile::apply-south/SEND`. |
| `lake build` from `formal/` | Passed, 13 jobs. |
| `npm test` from `editors/grammar/test/` | 26 passed. |
| `npm test` from `editors/vscode/` | 11 passed. |
| `cargo test --offline --locked -p trion-lsp --test lsp` | 18 passed. Includes navigation from an importing namespace to a descriptive origin and hover over the original names in an applied specification's source file. |
| `cargo check --workspace --locked --offline` | Passed on the final implementation. |
| `cargo test --offline --locked -p trion-cli --test grounding_engine --test individual_readings --test definition_rules --test project --test ears --test flow_rules --no-fail-fast` | 83 passed. Covers the legacy namespace and definition paths, bounded individual readings, source loading, EARS, and the gRPC form role and flows. |
| `cargo test --workspace --locked --offline --no-run --message-format=json`, then the reported executables run in their package directories with `PROPTEST_RNG_SEED=19`, `--test-threads 2`, and the two filters below | 131 binaries completed. 1,193 tests passed, 22 were ignored, and the CPC timing test `ten_thousand_proofs_are_read_in_linear_time` exceeded its ratio threshold in the parallel run. |
| `PROPTEST_RNG_SEED=19 cargo test --workspace --locked --offline --doc --no-fail-fast` | 42 passed. |
| `PROPTEST_RNG_SEED=19 cargo test --offline --locked -p cpc --test sessions -- --test-threads 1` | All four session tests passed, including the timing test. |

The existing diagram regression `each_generated_expression_names_the_elements_and_scopes_it_came_from` reproduces in `cargo test --offline --locked -p trion-cli --test diagram_rules each_generated_expression_names_the_elements_and_scopes_it_came_from -- --exact` on the unmodified `4da7c4e` export. The generated sentence writes `exactly 1` and the assertion expects `exactly one`. The workspace run used `--skip each_generated_expression_names_the_elements_and_scopes_it_came_from` and `--skip wide_term_round_trip`. The latter passed in the earlier unfiltered run against the same SMT-LIB implementation.

## Open work

- Application still needs rules for dependencies that supply legacy contracts and for automatic role activations over declared individuals. A bound role that uses a name changing under the application needs a parameter for it.
- The bounded individual reading supports static Boolean membership in assertions and conditions. A predicate that introduces an owned or temporal relative clause, and a population question used as a condition, require further rules. The independent reader reports the expressions it cannot rederive from the surface.
- The refinement report explains action-to-state gaps with a witnessed counterexample. Other forms of missing relations may need more specific explanations.
- The editor offers a qualified spelling when it can identify one matching span on the diagnostic line. Cross-line or repeated spellings require a manual choice of span.
- The remaining self-specification definitions require semantic migration. The libraries use their standard package paths, and gRPC and EARS expose form bindings from references.
- The verification results above are bounded. The conventions that map controlled English to formulas are outside the proofs.
