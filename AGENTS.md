# AGENTS

## Vision

trion is a formal specification language based on controlled natural language. Equipped with rigorous syntax and formal semantics, it expresses specifications in a mechanically verifiable representation.
A trion project and its trion files are a specification document, written in controlled natural language and a dedicated syntax. trion is a compiler of specification documents: its aim is a correct specification document.

Controlled natural language is employed to preserve the inherent expressiveness of natural language while ensuring the reliability of the specified requirements through mathematical rigor.

The baseline is theory: controlled natural language, Assume/Guarantee (A/G) contracts, MMT (https://uniformal.github.io/) and the certificate formats of formal methods. trion reasons by combining these theories and invents no proof of its own. Where the implementation differs from the theory, the implementation is wrong.

trion comprises the `trion` and `trioc` commands. They split the conversion, which examples can demonstrate, from the proof, which other tools must be able to reproduce.

- The `trion` command converts a trion project into arbitrary formats: MMT, Markdown, and other formats such as model code or test code. A project that does not conform to the language specification is an error. The `trion` command proves nothing, and a document does not wait for a proof.
- The `trioc` command reads the MMT form, proves the proof obligations that it states, and issues certificates in arbitrary formats, such as MoXI, Alethe and CPC.

MMT is the convenient baseline that connects `trion` and `trioc`, not an end in itself: what matters is that each result can be reproduced by another tool.

## Principles of the Language

The language is composed of simple sentences and composite vocabulary, under two rules.

1. A simple sentence is always exactly one unique A/G contract.
2. Composite vocabulary rewrites a sentence into a set of simple sentences and has no meaning of its own.

```text:Controlled Natural Language
the API shall store the message.
```

```text:A/G Contracts
A = ⊤
G = Act(API|store message) ∧ ¬Forbid(API|store message) ∧ ¬Discouraged(API|store message)
```

The contracts become proof obligations; within a bound of four moments, the obligation of this sentence reads:

```text:Bounded Proof Obligation
Ok@t ≔ Act(API|store message@t) ∧ ¬Forbid(API|store message@t) ∧ ¬Discouraged(API|store message@t)

f3 ≔ Ok@0 ∨ Ok@1 ∨ Ok@2 ∨ Ok@3
f0..f2 ≔ time@(t+1) − time@t ≥ 0 ms
```

Composite vocabulary serves as an abbreviated notation for specifying multiple requirements within a single sentence.

```text:Controlled Natural Language
The API shall store the message and log the message.
```

```text:A/G Contracts
A = ⊤
G = Act(API|store message) ∧ ¬Forbid(API|store message) ∧ ¬Discouraged(API|store message)

A = ⊤
G = Act(API|log message) ∧ ¬Forbid(API|log message) ∧ ¬Discouraged(API|log message)
```

trion is founded upon these two fundamental rules; broadening the catalog of supported patterns enhances the expressiveness of the controlled natural language. Whether a project works as a specification document is decided by the amount of sentences and composite vocabulary that follow the two rules.

Composite vocabulary is the surface of the two ways that contract theory combines contracts.

- Juxtaposed sentences and `and` between parts of a sentence are conjunction: the plain set of the contracts.
- A shared assumption (a condition clause over several requirements, a shared condition block, a sentence that only assumes) is merging. Merging is the same as giving the shared assumption to each sentence in its scope and then taking the plain set (`formal/Trion/Merging.lean`). A sentence that only assumes is never a contract beside the others: as a member of the set it changes nothing.

Whether a phrase belongs to the assumption or to the guarantee is decided by responsibility.

1. A document declares which actors are the system (`system API`); the others are its environment (`environment user`).
2. A sentence that constrains what the system is responsible for is a guarantee. A sentence that constrains what the environment is responsible for is an assumption. Descriptive and normative sentences follow the same criterion: a descriptive sentence about the system is a guarantee, not an assumption.
3. An assumption sentence is distributed to every guarantee sentence in its scope. The scope is the whole document unless a shared condition block narrows it.
4. A condition clause about the environment is part of the assumption. A condition clause about the system itself is a condition inside the guarantee.
5. The contract of a document is the conjunction of all contracts after expansion and distribution.

## A Correct Specification Document

A correct specification document conforms to the language, is consistent and compatible, and, where it has a reference, is correct and complete against that reference (Benveniste et al., *Contracts for Systems Design*, INRIA RR-8147; `formal/Trion/Document.lean`).

| Property | Meaning | Note |
| - | - | - |
| Consistency | An implementation exists | "A system that satisfies the contract set exists" |
| Compatibility | An environment exists | |
| Correctness | The document refines its reference | Needs a reference |
| Completeness | The document refines its reference, or no consistent and compatible document refines both | Needs a reference |

- The system accepts every input of its environment. As A/G contracts, "when the door opens, the bell shall ring" and "when the door opens, the bell shall not ring" are consistent, kept by a system that never lets the door open; as a specification document they contradict. Consistency is therefore read for a system that cannot refuse its inputs, and satisfiability alone is not consistency.
- Internal references are the two rules against each sentence pattern, and a sentence against the sentences that detail it. External references are sources; a source is checked mechanically only where its quoted text can be read as trion sentences. Evidence traces a sentence to its source and guarantees nothing.

### Reporting

What could not be proved is stated explicitly as not proved.

- `trion` writes the list of proof obligations into the MMT form; the output of `trioc` corresponds to that list one to one.
- Where a certificate format cannot express a result, that format reports an error or a warning. No certificate is issued without a proof.
- A bounded proof is reported as the proof of a bounded proposition, never as the proof of the unbounded one, as in the bounded proof obligation of the first example above.

## Limits of the Mechanism

These are limits of the mechanism, not of the plan: no amount of work removes them.

1. **What is proved is the contract, not the English.** The mapping from a sentence to its contract is a convention and is not an object of proof.
   - A reading that is unique to the machine is not guaranteed to be the reading of a person who reads the English.
   - The conversion is not part of any certificate; examples demonstrate it, and nothing proves it.
   - Writing the specification of trion in trion and verifying it shows that the conventions agree with each other, not that they are right.
2. **"Correct" reaches internal coherence and conformance to references, and no further.**
   - Fitness to real needs and intent is out of scope. A source can be traced, not validated.
   - Completeness is undefined without a reference; a requirement that nobody wrote cannot be found.
   - Correctness assumes that the reference is right.
   - A sentence can be satisfied vacuously, but only where nothing requires its trigger. "When the message is stored, the API shall notify the author" and "When the message is stored, the API shall not notify the author" are kept, alone, by a system that never stores, and are judged consistent and compatible. Once the document says that the API shall store the message, the system that never stores is excluded and the two sentences contradict; if the environment decides the trigger, a system that accepts every input cannot avoid it and they contradict as well. Vacuity is left only for a trigger that the system controls and that no sentence requires; finding it needs a property outside the four, such as a reference that requires the trigger.
   - The implementation that witnesses consistency may be degenerate.
3. **Only properties that one behaviour makes true or false can be written**, because an A/G contract is a set of behaviours.
   - Properties that compare behaviours (determinism, non-interference, probability) cannot be written.
   - Possibility ("must be able to") cannot be written; "may" means only that no other sentence forbids it.
   - Conjunction is monotone: adding a sentence only removes implementations. Defaults, overrides and priorities cannot be meanings.
   - Qualities without a measure ("usable", "fast enough") cannot be written.
4. **The rule of one unique contract removes something from natural prose.**
   - Context-dependent expressions, such as a pronoun or an ellipsis that refers to an earlier sentence, are excluded.
   - Composite vocabulary admits only rewritings whose meaning is proved equal before and after expansion.
   - Growing the catalog adds sentence patterns, not this kind of expression.
   - Uniqueness is a property of the whole catalog, so every new pattern makes it harder to keep together with naturalness.
5. **A term means nothing beyond the relations that the document writes.** "Store" and "is stored" are unrelated unless the document relates them. A contradiction that depends on an unwritten relation is not found, and a proof of consistency may only mean that the relation was not written.
6. **Some documents are neither proved nor refuted.**
   - Whether a system that accepts every input exists is undecidable in general without bounds on time, quantities and individuals. "Not proved" is a permanent possible outcome.
   - "Arbitrary formats" are limited to what each format can express.
   - The reporting rule guarantees honesty, not the range that can be decided.
7. **The responsibility boundary can only be trusted as declared.**
   - A wrong declaration of which actors are the system is not detected, and moving the boundary changes the conclusion for the same sentences.
   - An A/G contract frames one system and its environment. A document in which several systems make promises to each other needs composition, a different operation, and a split of the document.
