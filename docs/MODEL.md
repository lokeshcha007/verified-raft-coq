# Formal model and assumptions

## State and interpretation

`Node` is the concrete three-element type `A | B | C`. A quorum consists of any
two distinct members. `quorum_intersection` is proved by cases over the three
possible pairs; it is not assumed as an axiom. Membership never changes.

Each `Local` has a natural-number current term, a follower/candidate/leader
role, a list of `(term, command)` entries, a commit index, and an applied index.
Commit and applied indexes are **counts**: count 1 includes list position 0.
Term 0 is the initial term; a timeout increments the local term.

`votes : Term -> Node -> option Node` retains every node's choice in every
term. `voted_for s n` projects the choice at `n`'s current term, corresponding
to the usual votedFor field. The persistent ledger is part of this abstraction,
not a proof axiom. It is stronger storage than the single current-term field in
an implementation. Votes can only change from `None` to `Some candidate` once.
Repeated grants, even for the same candidate, are rejected; duplicated request
handling is outside this atomic voting model.

`journal` is a shared sequence, `elections` retains historical `(term, node)`
winners, and `network` retains AppendEntries messages. A message contains source,
destination, sender term, a full log prefix, and the sender's commit count.
`certified s t n` means a majority's persistent votes select `n` in term `t`.

All states start from empty logs, votes, election records, and network; all nodes
are followers in term 0 with commit and application count 0. States satisfying
the invariant but unreachable from this initial state are not asserted to be
Raft executions.

## Explicit assumptions and restrictions

1. **Shared ordering abstraction.** Every local log is a prefix of one global,
   append-only journal. Only an elected leader can append to the journal, and
   its log must equal the journal before appending. This rules out conflicting
   histories by construction of the reachable-state transitions. The journal
   is an abstract specification resource; it is not an implemented network
   service or a verified refinement of distributed Raft log allocation.
2. **Election catch-up.** A candidate may become leader only when its log
   equals the entire journal, including uncommitted entries. Production Raft
   uses a last-log-term/index vote restriction rather than this global equality
   check. Granting votes here does not perform that freshness comparison.
   The equality guard prevents an election with an incomplete log and makes
   this restricted model possibly unable to progress.
3. **Extension-only replication.** Delivery is accepted only when the
   receiver's entire current log is a prefix of the message payload. There is
   no suffix truncation or repair. Full-prefix payloads replace per-entry RPCs
   and the prevLogIndex/prevLogTerm test. Even uncommitted entries never change.
4. **Term-aware, globally guarded append.** Appending requires the producer's
   term to be at least every node's current term. This direct global test is
   stronger than the information available to a real leader. Message sending
   itself may still happen from an old-term leader; stale delivery is rejected.
   Observing a higher term changes the node to follower without changing logs,
   commit indexes, application indexes, or prior votes.
5. **Atomic certification and replication evidence.** Elections inspect the
   vote ledger; commits inspect node log lengths directly. RequestVote RPCs,
   replies, acknowledgement tracking, nextIndex, and matchIndex are abstracted
   away. Majority replication is a guard on the commit transition, not a
   conclusion inferred from unreliable acknowledgements.
6. **Non-Byzantine authenticated messages.** Messages originate only through a
   leader's send transition, or duplication of an existing message. External
   injection is not an event. Delayed, out-of-order, and repeated delivery are
   possible; no fairness or eventual delivery assumption is made. Delivering a
   message does not remove it, so retry is possible. `DropMessages` discards
   the entire network, rather than modeling arbitrary single-packet removal.
7. **Persistent, atomic mathematical state.** There are no crashes or restart
   events, and no storage I/O. A step is atomic. Votes and election records never
   disappear. The model is non-Byzantine and assumes no mutation outside `step`.
8. **Abstract commands and application.** Commands are natural numbers.
   Application advances a per-node count by one within the committed prefix.
   Safety concerns the recorded command at an applied index, not external
   side effects or a particular state-machine implementation.

These are definitions and transition restrictions, not unproved logical axioms.
The assumption audit can be axiom-free while the model still has these important
semantic assumptions.

## Transition guards

| Event | Guard | Effect |
| --- | --- | --- |
| `ObserveTerm n t` | `current_term n < t` | Set term `t`, role follower |
| `Timeout n` | None | Increment term, role candidate; self-vote is a separate event |
| `GrantVote n c t` | Voter is in term `t`; ledger slot is empty | Persist vote for `c` |
| `WinElection n` | Candidate; majority certificate; complete journal | Set leader; retain historical election record |
| `ClientAppend n cmd` | Leader; complete journal; maximal observed term | Append `(current term, cmd)` to journal and leader log |
| `SendAppend n dst` | Sender is leader | Enqueue full log with term and commit count |
| `Deliver m` | Message exists; term is not stale; receiver log is a prefix of payload | Become follower at message term; extend log; take max of commit counts |
| `Commit n k` | Leader; monotone and bounded count; majority holds at least `k` entries; terminal entry is current-term, unless `k = 0` | Advance leader commit count |
| `Apply n` | Applied count is below commit count | Advance applied count by one |
| `DropMessages` | None | Clear all pending messages |
| `Duplicate m` | Message exists | Add another copy |

Because logs are prefixes of the same journal, majority **length** evidence
also establishes agreement of the replicated prefix. This inference would be
invalid for arbitrary divergent logs. The current-term commit condition mirrors
one Raft restriction, but the proof of agreement in this abstraction principally
uses the shared journal, not Raft's complete leader-completeness argument.

A node can become follower on delivery even in its current term. There is no
availability claim. Multiple nodes can retain leader roles in different terms;
the proved uniqueness is per term. The election record is historical and never
forgets a leader when it steps down.

## Excluded claims

No refinement relates `step` to a production Raft implementation. The model
does not cover divergent uncommitted logs, dynamic membership, snapshots,
crash/restart, real durable storage, Byzantine faults, client deduplication,
linearizability, or liveness. It does not establish the full Raft leader
completeness theorem under Raft's actual voting rules. Extending the model to
suffix repair requires replacing the shared-journal/extension-only assumptions
and substantially new proofs.
