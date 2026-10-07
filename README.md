# verified-raft-coq

A compact, machine-checked **Raft-inspired consensus safety core** in Coq/Rocq.
It models a fixed three-node cluster as an event-labelled transition relation
`step : State -> Event -> State -> Prop` and proves safety for every reachable
state and every finite valid execution. It does not implement production Raft.

**Scope boundary:** logs in this model are extension-only prefixes of a shared
append-only journal. This is a deliberate global ordering abstraction, not a
derived property of the complete Raft RPC protocol. Candidate catch-up is an
explicit election guard. The project does **not** prove Raft's handling of
conflicting uncommitted suffixes, crash recovery, or general leader completeness.
See [the precise assumptions](docs/MODEL.md) before interpreting the results.

## Proved properties

All the following results are complete proofs in [Safety.v](theories/Safety.v).
No proof holes or project-defined logical axioms are used.

| Property | Main theorem | Extent |
| --- | --- | --- |
| Terms never decrease | `terms_do_not_decrease`, `trace_terms_monotone` | Every node, one step and finite executions |
| One consistent vote per term | `vote_persistent`, `vote_consistency`, `trace_vote_persistent` | Historical per-term votes survive term changes |
| Log matching | `log_matching` | Same index and term imply identical entry and preceding prefix |
| Leader append-only | `leader_append_only` | In fact every node's log is extension-only in this abstraction |
| Committed entries remain committed | `committed_entries_remain`, `trace_committed_entries_remain` | Same node, same index, same entry, all future valid states |
| Committed prefix never changes | `committed_prefix_stable` | The earlier committed prefix survives every finite execution |
| State-machine safety | `state_machine_safety`, `state_machine_safety_across_time` | Applied commands agree by index, including across time |
| Election safety | `election_safety`, `at_most_one_leader_per_term` | Both historical winners and current leaders are unique per term |
| Preservation of safety | `safety_preserved`, `reachable_invariant`, `trace_safety_preserved` | The invariant holds initially and is preserved by every constructor |

Election uniqueness is derived from intersecting two-of-three quorums and
persistent votes. Log agreement is derived from prefix membership in the shared
journal. The latter is a stronger assumption than production Raft provides; it
is not a substitute for the complete Raft log-repair proof.

## Model and files

The state includes node terms and roles, per-term voted-for state, logs, commit
and applied indexes, the journal, historical election records, and in-flight
AppendEntries messages. Entries carry a term and a natural-number command.

Events model timeouts, observing higher terms, granting votes, winning elections,
client appends, sending/delivering AppendEntries, majority commits, application,
message loss, and duplication. Commit indexes count entries; log positions are
zero-based. Voting is atomic and AppendEntries carries an entire prefix.

| File | Purpose |
| --- | --- |
| [Prelude.v](theories/Prelude.v) | Nodes, majority intersection, finite updates, list-prefix lemmas |
| [Model.v](theories/Model.v) | State, events, initial state, transition relation, reachability |
| [Safety.v](theories/Safety.v) | Invariant preservation and safety theorems |
| [Examples.v](theories/Examples.v) | Successful replication/application, leader change, rejected unsafe actions |
| [Audit.v](theories/Audit.v) | `Print Assumptions` audit of the principal results |
| [docs/MODEL.md](docs/MODEL.md) | Assumptions, transition guards, excluded behavior |
| [docs/PROOFS.md](docs/PROOFS.md) | Proof structure and interpretation |

## Build and independently check

Use **Rocq 9.1.0**, its standard library, and **Python 3.9+**. There are no external
Rocq libraries or Python package dependencies. The `From Stdlib` imports target
Rocq 9; compatibility with earlier Coq releases is not claimed.

For an opam installation, follow the [official installation guide](https://rocq-prover.org/docs/using-opam):

```sh
opam switch create 4.14.2
opam repository add rocq-released https://rocq-prover.org/opam/released
opam install rocq-prover rocq-core.9.1.0 rocq-stdlib.9.1.0
opam exec -- python3 scripts/check.py
```

On Windows, use the [Rocq Platform](https://github.com/rocq-prover/platform/releases/tag/2026.07.0)
and run this command in PowerShell from the project folder:

```powershell
python scripts/check.py --coqc 'C:\path\to\Rocq-Platform\bin\coqc.exe'
```

The script also accepts `COQC`, `COQCHK`, and `--coqchk`. It adds the compiler's
directory to the subprocess PATH so Windows can find the Platform DLLs.
With `coqc` and `coqchk` on PATH, run `python scripts/check.py` or `make check`.

The check compiles all five modules, rejects unfinished proofs and axiom
declarations, requires all 21 audited results to be closed under the global
context, then independently checks the compiled proof objects with `coqchk`.
This verifies the formalization's proof objects, not a deployed Raft service.
The [GitHub Actions workflow](.github/workflows/proofs.yml) repeats the same check.
Use `python scripts/clean.py` to remove generated proof artifacts.

To publish this project to the requested repository from your normal PowerShell
session, run the following after reviewing the files. The script reruns formal
verification, checks `main` and the origin URL, commits the project, and pushes
without force. Its Git commands trust this specific project folder to handle
repositories created under a different account, without changing global Git
configuration:

```powershell
.\scripts\publish.ps1 -Coqc 'C:\path\to\Rocq-Platform\bin\coqc.exe'
```

## Examples and limits

The successful trace elects A in term 1 with A+B votes, appends command 42,
replicates it to B, commits after majority replication, propagates the commit,
and applies it on A and B. A second trace elects B in term 2 and appends command
99 while retaining the committed entry. C may remain behind. Other examples
prove that inconsistent voting, election without a majority, unreplicated
commit, follower append, and stale-term delivery are rejected. A delayed old
commit advertisement cannot decrease B's commit index.

Commands are recorded application histories; no application-specific execution
function or linearizability theorem is included. No liveness, bounded delivery,
fairness, membership changes, snapshots, durability implementation, Byzantine
faults, or correspondence to an executable Raft implementation is claimed.

The conceptual reference is Ongaro and Ousterhout's
[extended Raft paper](https://raft.github.io/raft.pdf), especially its safety
properties. The simplifications here are specific to this formal model.
