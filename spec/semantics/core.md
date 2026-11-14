# The meaning of statements about individuals

This
file states the rules that give a statement its meaning over concrete
behaviours. The rules are the contract of work items W03 to W08 of
`docs/practical/plan.md`: the reading that produces formulas
(`crates/trion-language/src/reading/typed.rs`, `ground.rs`) and the reference
evaluator (`crates/trion-checker/src/eval.rs`) are two implementations of
them, and neither is the definition.

The rules apply to a package that declares the types of its individuals. A
package without such a declaration is read by one representative of each
type (`readings.md`).

## 1 Meaning objects

| object | what it is | where it comes from |
| - | - | - |
| type | a set of individuals | `individuals user, room, message` |
| carrier | the types whose individuals are the same individuals | `Each member is a user.` joins `member` and `user` |
| individual | one element of a carrier, named `<declared noun>#<n>` | the domain of an analysis, or a scenario |
| kind | a property of an individual | a noun: `member`, `administrator` |
| relation | a set of pairs (owner, member) of individuals | `Each room has exactly one owner.` names the relation `owner` |
| state | a value that an individual has at a moment | `the room is archived` |
| occurrence | an event or the completion of an action at a moment, with its participants | `a user posts a message to a room` |
| moment | a point of a finite trace, with a time in milliseconds | — |
| activation | one application of a statement: an assignment of its variables and the moment at which its conditions hold | — |
| quantity | an exact number of thousandths with a unit | `within 2 seconds` is 2000 ms |

A *behaviour* is a finite, complete trace: individuals with their kinds and
relations, and for each moment its time, the states that hold and the
occurrences. What a behaviour does not hold does not exist, does not hold or
does not happen, and nothing happens after its last moment.

A noun without a declared type names one thing (`the system`). It is a
constant of every behaviour.

## 2 Variables and binding

| rule | text |
| - | - |
| `variable` | A noun phrase whose head is a noun of a declared carrier, with `a`, `an`, `the`, `each`, `every` or `any`, is a variable that ranges over the individuals of the carrier that are of the kind that the noun names. |
| `variable-again` | Within one statement a variable is identified by its noun and its ordinal: `a message` and `the message` are one variable, `the second message` is another. An explicit variable (`a message M`) is written out as its noun before the statement is read. |
| `variable-of` | `the R of the T` restricts the variable of R to the individuals that stand in the relation R to the individual of T. With exactly one such individual it names that individual. |
| `attribute` | `the N of the T` with an undeclared N is a property of the individual of T. |
| `constant` | A noun phrase without a declared type names one thing. |

| `variable-other` | Two variables of one statement that are named by one noun with different ordinals name different individuals: `a member` and `a second member` are two members. An assignment that gives both the same individual is no instance of the statement. |

A variable is universal: the statement holds for each assignment. One
kind of variable is not:

| rule | text |
| - | - |
| `variable-some` | `a` or `an` that first names an individual of a declared type in what an obligation requires or advice advises (`shall create a ticket`, `should notify a member of the room`) is a variable that the response chooses. The statement holds for an assignment of its other variables when some individual of the kind, in the named relations, meets the response. In a list of actions the response chooses the individuals of all actions together. |
| `variable-any` | `a` or `an` that first names an individual in what a permission permits names any individual: `may notify a member of the room` permits the notification of each member. |

The individual is chosen for each activation: two activations may be
answered by two individuals or by one. Which individuals there are is
given by the situation and not chosen by a response: a statement that
requires `create a ticket` has no response in a domain without a ticket,
so a package states that there is one (`There is a ticket.`, `Each room
has at least one member.`) or the situation counts as one without a
response. `the` in a response names what a condition named or what a
relation gives (`the author of the message`); `each`, `every` and `any`
name each individual. Under `shall not` and `should not` a noun phrase is
general: no individual is excepted. A statement that introduces an
individual with `the`, among alternative actions (`either … or`) or beside
a share is rejected (`UNSUPPORTED_SEMANTICS`).

### Forms that stand for a plain statement

A relative clause, `no`, a count and a composition add no meaning of their
own. Each statement with one of them stands for a statement without it
(`crates/trion-language/src/reading/normal.rs`), and the two have one
record apart from the steps that say how the plain statement was written.

| rule | form | the plain statement |
| - | - | - |
| `variable-that` | `a T that is <value>`, `… that is [not] a R of the U`, `… that is a K`, `… whose N is <value>` | the clause is a `While` condition about the individual: `While the T is <value>, …`. It holds at the moment at which the statement applies. |
| `variable-that` | `a T that <verb>s …`, `a T that the U <verb>s` | the clause is the event of the statement: `When the T <verb>s …, …`. A statement applies at one event: with an event of its own it has none in a relative clause, and the denial of an event names none. |
| `variable-no` | `No T shall <verb> …`, `… shall <verb> no T` | `Each T shall not <verb> …`: the statement denied of each individual. Beside a denied verb it is rejected. |
| `variable-count` | `While two Ts are …,` | `While a T is … and a second T is …,`: so many different individuals (`variable-other`), each in the clause. |
| `variable-count` | `shall <verb> two Ts`, `should <verb> two Ts` | `shall <verb> a T and <verb> a second T`: the action on each, and the response chooses the individuals. |
| `choice-order` | `shall perform the following actions in order: A; B;` | `shall A and B after <subject> A`: each action, each strictly after the one before it. `all of the following actions` is the list of them, `one or more of the following actions` is `either … or`. |

Rejected over individuals, each with the reason in its message: a
relative clause on an individual that the response chooses, in `unless` or
in an order; a count in the event of a statement, before the subject of a
statement with a modal verb, in what is forbidden or permitted, or of more
than six; `no` in a condition; `exactly one of the following actions`, a
flow and a composition within a composition; a modifier other than an
ordinal; coordinated noun phrases; a content clause; `only when`,
`exactly when` and `even when`.

## 3 Conditions

| rule | form | meaning at a moment t |
| - | - | - |
| `condition-occurs` | a clause with a verb | an occurrence with these participants at t (`does not`: none) |
| `condition-holds` | `X is [not] <value>` | the individual has the state at t |
| `condition-related` | `X is [not] a R of the T`, `X is [not] the R of the T` | the pair stands in the relation; no moment |
| `condition-kind` | `X is [not] a K` | the individual is of the kind; no moment |
| `condition-compares` | a comparison | a bound on a quantity (not evaluated by the reference evaluator) |

`Where`, `While`, `When` and `If` hold their conditions together (`and`) or
as alternatives (`or`). `unless C` applies the statement where C fails.

An *activation* of a statement is an assignment of its variables, of the
named kinds and relations, with:

- each moment at which the event of `When` or `If` occurs and the other
  conditions hold (*triggered*);
- without such a frame, each moment at which the states hold (*standing*);
- without a condition of a moment, the behaviour as a whole
  (*unconditional*).

## 4 Responses

| force | triggered at t | standing at t | unconditional |
| - | - | - | - |
| obligation of an action | completes at a moment after t | completes at t | completes at some moment |
| prohibition of an action | completes at no moment after t | does not complete at t | completes at no moment |
| required state | holds at the moment after t | holds at t | holds at each moment |
| description of a state, a kind or a relation | as a required state; a kind and a relation have no moment | | |

- `response-deadline`: `within d` — the time of the completion minus the
  time of t is at most d. The end is included.
- `response-after`: `after E` — the completion is strictly after an
  occurrence of E that belongs to the activation (for an unconditional
  statement: after some occurrence of E).
- `response-before`: `before E` — no occurrence of E that belongs to the
  activation lies at or before the completion.
- An occurrence *belongs to an activation* at t when it is the occurrence
  that opens the activation (the event of `When` or `If`, at t) or when it
  lies after t. What happens at the moment of the trigger beside the
  trigger answers nothing that the trigger opens. So two actions of one
  activation cannot each come after the other, and they cannot each come
  before the other; the same actions in two activations may alternate.
- A prohibition with an order forbids only at the positions that the order
  names: `shall not A before E` forbids A until an occurrence of E that
  belongs to the activation (a completion at the moment of E is not before
  it), and `shall not A after E` forbids A from the moment after such an
  occurrence.
- `choice-either`: one of the actions is completed as required.
  `choice-each`: each of them.
- `response-values`: an enumeration lists the states of an individual: at
  each moment the individual has exactly one state of the list, and no
  state outside it.

One completion answers every activation whose window holds it: the
completion of `store message#1` answers each earlier posting of `message#1`
that it follows within the deadline. It answers no posting of another
message.

### Status

A prohibition forbids its action at each position of its window (the moments
after t, the moment t, or all moments), and `should not` advises against it
there. The window of a triggered and of an unconditional statement holds the
time after the last moment as one more position.

- A required action completes at a moment at which it is neither forbidden
  nor advised against.
- `may` requires a position of its window at which the action is not
  forbidden.
- `should` requires a position at which the action is not forbidden and a
  position at which it is not advised against.

### Shares

`for at least 99 percent of postings` after a required action bounds a
share (`response-share`). The statement then says nothing of one activation:
it says how many of its activations the response answers.

- The *population* is the set of the activations of the statement in the
  behaviour: each assignment of its variables with each moment at which its
  conditions hold and its exception fails. The declared measure (`measure
  postings`) names it. The window is the behaviour.
- An activation is *answered* when the response meets it as the statement
  requires (within its deadline, in its order). An activation without a
  response stays in the population: the denominator holds each activation.
- A lower bound (`at least`, `more than`) counts the activations that the
  response meets as a requirement: a completion at a position where the
  action is forbidden or advised against answers nothing. An upper bound
  (`at most`, `less than`) counts each activation whose action completes
  in its window, whatever forbids it or advises against it. `exactly` is
  both bounds.
- The bound is compared in whole numbers: `answered · 100 000` against
  `thousandths of a percent · population`. No share is rounded.
- The share of an empty population has no value. A behaviour without an
  activation neither meets the bound nor fails it; a result lists the
  statement as without a value and does not count it as met.
- Two shares of one population whose statements differ only in the
  deadline are ordered: what is answered within the shorter deadline is
  answered within the longer one.

- A measure names one population. Statements that bound a share of one
  measure have the same variables and the same conditions; a statement
  with other conditions counts other activations and is rejected until it
  names a measure of its own.

Over a domain, each assignment of a statement that bounds a share is an
instance that says what one activation is and what answers it. Such an
instance requires nothing: it is *counted*. The formulas count the
population, the unanswered and the completed activations of the trace with
sequential counters and compare them with the bound in whole numbers
(`reading/temporal.rs::share_contract`); no count of the reference
evaluator enters the formulas.

A trace of moments ends in the rest, which stands for moments without
number. Where a behaviour goes on after the trace, its counts are not the
counts of the trace, and a share that the trace fails may hold of the
behaviour. The count therefore binds where the behaviour ends with the
trace, which a scenario always does; where it goes on, only a bound that
leaves no activation out (all of them, or none) binds. The quantity of the
share keeps its bound wherever the population is not empty, and the order
of the shares of one population relates those quantities, so two bounds
that no population meets are found without a count.

In a statement that names no declared type a share has no population to
count, and the statement is rejected (`share-of-representative`).

## 5 Statements about the domain

A statement without a condition that counts or relates the individuals of a
type is a statement about the domain: `Each room has exactly one owner.`,
`The owner of each room is a member of the room.`, `Each member is a user.`,
`No two rooms have the same name.`, `There are at least two rooms.`. Its
meaning is the stated property of the kinds and relations of the behaviour
(`typed::DomainFact`).

## 6 What is not implied

- An action does not change a state: `shall archive the room` does not make
  the room archived. A change is stated as a statement of its own.
- A state does not persist from one moment to the next unless a statement
  says so.
- Two variables of one carrier may name one individual.

## 7 From meaning to formulas

Over a domain of `scope` individuals of each carrier, a typed statement
stands for one *instance* for each assignment of its universal variables: the sentence with each
variable replaced by the name of its individual, under the condition that
the individuals are of the named kinds and stand in the named relations. A
relation and a kind are taken out of the sentence into that condition. An
instance is a short sentence, and the reading of sentences reads it
(`reading/ground.rs`). Where the response chooses an individual, the
instance requires one of its alternatives, one for each individual of the
domain, each under the condition that the individual is one that may be
chosen.

The reading states, for each atom of an instance, the fact of a behaviour
that the atom stands for (`Individuals::atoms`). With that table a formula is
evaluated on a behaviour without reading the name of an atom, and

```text
τ ⊨ S  ⟺  ∃η. (τ, η) ⊨ L(S)
```

is tested behaviour by behaviour (`crates/trion-checker/src/compare.rs`): τ
fixes the atoms of the table, and η is the status of each action, the times
and counts that the reading adds, and the states of the rest of the trace.

The analysed range is the domain of `scope` individuals of each carrier and
the trace of the stated number of moments. A result names both, and nothing
is claimed beyond them.

## 8 Scenarios

A `scenario` block states one behaviour and what its author expects of it.

```text
scenario STORED:
    given a user U1, a room R1, a message M1
    given U1 is a member of R1.
    at 0 ms: R1 is open.
    at 0 ms: U1 posts M1 to R1.
    at 1 seconds: the system stores M1.
    expect allowed
```

- `given a <type> X, …` names the individuals. `given X is a K.` states a
  kind and `given X is a R of Y.` a relation.
- `at <whole number> <ms|seconds|minutes>: …` states a state (`R1 is
  open.`) or an occurrence. A state holds from its time until another state
  of the same individual is stated. The moments of the behaviour are the
  stated times.
- What the block does not state does not exist, does not hold and does not
  happen. An individual is of its declared type, and the member of a
  relation is of the kind that the relation names.
- An enumeration gives each individual one of its states at each moment,
  so a block states the state of each individual that an enumeration
  speaks of, from its first moment on (`at 0 ms: R1 is open.`).
- `expect allowed`: the behaviour fails no statement. `expect forbidden`: it
  fails one. `expect undefined`: it fails none, and a share that a
  statement bounds has no value in it.

A scenario is judged by the reference evaluator and by the formulas of the
reading. The claim `scenario_satisfiable` of the scenario is `proved` when
both allow the behaviour, `refuted` when both forbid it, and `error` when
they differ. It says nothing about whether the behaviour can be reached.

Beside the scenarios, three kinds of behaviours are judged by both sides.

- *The behaviour behind `contract_sat`.* The claim that a behaviour keeps
  every contract rests on a model of the formulas. The model is asked for
  as a complete behaviour (nothing happens after the last moment), with as
  few occurrences as the contracts allow and with a statement that applies
  at the first moment, and it is written down with the table of atoms
  (`crates/trion-checker/src/witness.rs`). The reference evaluator judges
  it. A behaviour that the formulas accept and the meaning refuses is an
  error (`witness-refused`), and the claim is not shown as proved.
- *The variations of a scenario* (`verify --properties`). Each differs from
  the scenario in one fact: an occurrence left out, moved by a moment or
  about another individual, a relation left out, another listed state, a
  moment later by a stated deadline (`crates/trion-checker/src/vary.rs`).
  No expectation belongs to a variation; both judgements agree on it, or
  the reading differs from the meaning on a behaviour that no scenario
  states (`scenario-differs`).
- *The situation of a scenario* (`verify --properties`). The scenario
  without the occurrences that the statements require, forbid or permit,
  with one more moment after each of its moments. Where the statements
  without normative force allow the situation, the formulas are asked for
  a response to it, and the reference evaluator judges the behaviour with
  that response (`witness.rs::respond`).
- *The situations of the statements* (`verify --properties`). For each
  statement with a condition of a moment, and for each two of them, a
  behaviour that the statements without normative force allow and in which
  the conditions hold together at the first moment, without any occurrence
  that a statement requires, forbids or permits (`witness.rs::together`).
  The formulas are asked for a response to it, and the reference evaluator
  judges the behaviour with that response. Advice is left out on both
  sides. A situation without a response, where the claim says that each
  situation has one, is an error (`witness-refused`). The situation is
  found by the formulas of the statements without normative force, so two
  statements that these formulas wrongly keep apart are not examined
  together; three or more statements are examined together only through
  the claim itself and the external prover.

## 9 The order of the reading

The variables of a statement are numbered in the order in which the reading
meets them: the frames (`Where`, `While`, then `When` or `If`), the
exception, the subject, the response. Within a clause the subject stands
before the object and the object before the roles; within a noun phrase the
owner stands before the head; within a response the events that an order
names stand before the action.

## 10 The record of a reading

The text of each statement about individuals is read a second time by a
grammar apart from the parser (`crates/trion-checker/src/surface.rs`),
which knows the closed words of the language and the nouns that the
package declares: where it reads the text and the tree of the parser
brackets the words otherwise, the tree is refused (`derivation-refused`);
where the text is outside that grammar, the result names the statement as
not read from its text. The type of each noun is derived again from the
declarations and the text of the statements of the form `Each A is a B.`

Each typed statement has a record (`typed::Meaning`): its variables, its
restrictions, its frames, its exception, its force, its responses, and the
steps of the reading. A step names the rule of this file, the words that it
read and what it made of them. `verify --json` gives the records under
`individuals.meanings`, the instances under `individuals.instances` and the
table of atoms under `individuals.atoms`.
