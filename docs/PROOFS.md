# Proof guide

## Invariant

`invariant s` is the conjunction of five independently named components:

1. `logs_consistent`: each log is a prefix of the journal.
2. `local_bounds`: `applied_index <= commit_index <= length log` for every node.
3. `elections_sound`: every historical winner has a majority vote certificate.
4. `leaders_recorded`: every current leader appears in the historical records
   at that node's current term.
5. `messages_safe`: each in-flight payload is a journal prefix, the advertised
   commit is within that payload, and its sender is a historical winner at its
   message term.

`initial_invariant` proves the base case. The five `*_step` lemmas prove each
component is preserved. `safety_preserved` assembles those lemmas, and
`reachable_invariant` inducts over reachable states. No transition takes
`invariant s'` or election uniqueness as a guard.

## Election safety

`vote_persistent` is proved for every step, without requiring reachability.
Only the voting rule changes a ledger slot, and its `None` guard makes
overwriting an existing vote impossible. A majority certificate therefore
survives subsequent steps, including term changes.

`quorum_intersection` supplies a shared voter between two certificates.
`certificates_unique` equates their candidates because the shared ledger slot
cannot simultaneously be `Some c` and `Some d` with `c <> d`.
`election_safety` uses the reachable-state certificate invariant to prove that
two recorded winners in the same term are equal. `at_most_one_leader_per_term`
then connects live leader roles to those historical records. The uniqueness
proof does not rely on a unique-leader field or a no-second-leader guard.

## Log matching and preservation

`logs_append_only` is a direct transition proof. An append extends the journal
and the producer's matching log; delivery uses its explicit prefix guard;
other events leave logs unchanged. This stronger all-node append-only result
is particular to this simplified model.

`prefix_nth` maps a node's entry at position `i` to the journal at `i`.
`log_position_agreement` applies it to two node logs, yielding equality even
without a term hypothesis. `log_matching` gives the conventional implication
with the matching-term hypothesis and additionally proves equality of all
entries through that position with `prefix_firstn`.

`commit_index_monotone` handles commitment and delivery explicitly; delivery
takes `max old_commit advertised_commit`, so an old advertisement cannot undo
commitment. Combining this result with log extension proves
`committed_entries_remain`. Induction over `steps` extends persistence to all
finite futures. `committed_prefix_stable` states prefix preservation directly.

## State-machine safety

`applied_entries_are_committed` connects application to commitment using the
index bounds. `state_machine_safety` uses positional log agreement to show
that any two applied entries at the same index have the same command.
`state_machine_safety_across_time` extends the earlier node's entry along a
finite execution before comparing it to a later application on another node.
These results concern command histories, not an application-specific execution
function or real client responses.

## Non-vacuity and independent verification

`Examples.v` proves a 13-event execution from `initial` to two nodes having
applied command 42. It also proves a six-event leadership change into term 2
and retention of the earlier committed entry. Rejection lemmas use inversion of
the transition relation to show that selected unsafe actions have no successor.
The delayed-message example checks the `max` commit rule with an old zero
commit advertisement after a real commit.

`Audit.v` prints assumptions for 21 principal results. `scripts/check.py` checks
that each is reported closed under the global context. It then runs `rocq check`
(or the legacy `coqchk` compatibility command)
over the compiled modules and their dependencies. All proofs use ordinary
constructive Gallina/Ltac and standard-library arithmetic; there are no
project-defined axioms, classical reasoning, functional extensionality, or
proof-irrelevance dependencies. The trusted foundation is Rocq's kernel and
the standard library, not the source-text hole scan alone.
