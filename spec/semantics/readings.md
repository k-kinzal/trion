# The two readings

A package is read in one of two ways, and its declarations decide which:

| applies to | reading |
| - | - |
| a package that declares no type of individuals | one representative of each type; the reading of `crates/trion-language/src/reading` as `spec/patterns/ledger.toml` describes it |
| a package with an `individuals` declaration | `core.md`: variables over individuals, relations and kinds of the domain, activations, shares as counts |

Adding `individuals user` to a package moves it from the first row to the
second. A result names the meaning rules that read its statements
(`outcome.subject.semantics`) and the digest of the package, and
`verify --against` refuses a saved result about other rules or another
text (`result-stale`).

## What differs

| | one representative of each type | individuals |
| - | - | - |
| `a message` … `the message` | one representative message for the package | one variable of the statement; the statement holds for each message |
| `When a user sends a message M, … store M.` | the storing of the representative message | the storing of the message that was sent |
| `the user is a member of the room` | a state of the user, by name | a relation between two individuals; it selects the instances of the statement |
| `Each room has exactly one owner.` | the representative reading and, where another statement distinguishes individuals, a reading over a bounded domain | the reading over the domain, and no other |
| an action with a role | another action than the action without it, unless a statement requires it | an occurrence with a role is an occurrence of the action without it |
| `for 99 percent of requests` | rejected: no population to count | a count of the activations of the statement that the response answers |
| `shall create a ticket` | the creating of the representative ticket | the creating of some ticket: the response chooses the individual |
| a relative clause on a type, a count before a type in a condition, a composition, an individual that advice or a permission introduces | read by name | rejected: no rule reads them over individuals |
| a result | within traces of N moments | within traces of N moments and domains of K individuals of each carrier |

## Moving a package to the reading over individuals

1. Declare the types whose individuals the statements tell apart:
   `individuals user, room, message`.
2. State what joins the nouns of one carrier (`Each member is a user.`) and
   the relations that the statements use (`Each room has exactly one owner.`).
3. Name in a condition each individual that a response is about, or relate
   it to one that is named (`the author of the message`).
4. State the facts of the domain that the representative reading left
   implicit. The verification names them as conflicts: one message posted by
   two users, one message posted to two rooms (`docs/practical/W12-results.md`).
5. Write a scenario for each behaviour that the package must allow or forbid.

A statement that the reading over individuals rejects keeps its
representative reading only in a package without declared individuals.
Narrowing is not counted as an improvement: `docs/practical/W13-release.md`
lists what the reading over individuals does not read.
