From Stdlib Require Import List Arith Lia.
From VerifiedRaft Require Import Prelude.
Import ListNotations.

Definition Term := nat.
Definition Command := nat.
Inductive Role := Follower | Candidate | Leader.
Record Entry := entry { entry_term : Term; entry_command : Command }.

(* Commit and applied indexes count entries; list positions are zero-based. *)
Record Local := local {
  current_term : Term;
  role : Role;
  log : list Entry;
  commit_index : nat;
  applied_index : nat
}.

Record Message := append_entries {
  sender : Node;
  receiver : Node;
  message_term : Term;
  payload : list Entry;
  advertised_commit : nat
}.

Definition Votes := Term -> Node -> option Node.
Record State := state {
  nodes : Node -> Local;
  votes : Votes;
  journal : list Entry;
  elections : list (Term * Node);
  network : list Message
}.

(* Retained per-term votes are persistent model state. The usual votedFor
   field is this view at the node's current term. No term is voted twice. *)
Definition voted_for s n := votes s (current_term (nodes s n)) n.
Definition certified s t c := quorum (fun n => votes s t n = Some c).
Definition committed s n i e :=
  i < commit_index (nodes s n) /\ nth_error (log (nodes s n)) i = Some e.
Definition applied s n i e :=
  i < applied_index (nodes s n) /\ nth_error (log (nodes s n)) i = Some e.

Definition put_local s n l :=
  state (update (nodes s) n l) (votes s) (journal s) (elections s) (network s).
Definition change_term l t r :=
  local t r (log l) (commit_index l) (applied_index l).
Definition put_vote s t n c :=
  state (nodes s)
    (fun u => if Nat.eq_dec u t then update (votes s u) n (Some c) else votes s u)
    (journal s) (elections s) (network s).
Definition elect s n :=
  state (update (nodes s) n (change_term (nodes s n) (current_term (nodes s n)) Leader))
    (votes s) (journal s) ((current_term (nodes s n), n) :: elections s) (network s).
Definition append s n cmd :=
  let l := nodes s n in
  let xs := journal s ++ [entry (current_term l) cmd] in
  state (update (nodes s) n (local (current_term l) Leader xs (commit_index l) (applied_index l)))
    (votes s) xs (elections s) (network s).
Definition outgoing s n dst :=
  append_entries n dst (current_term (nodes s n)) (log (nodes s n)) (commit_index (nodes s n)).
Definition put_network s msgs :=
  state (nodes s) (votes s) (journal s) (elections s) msgs.
Definition deliver s m :=
  let l := nodes s (receiver m) in
  put_local s (receiver m)
    (local (message_term m) Follower (payload m)
      (Nat.max (commit_index l) (advertised_commit m)) (applied_index l)).
Definition mark_commit s n k :=
  let l := nodes s n in
  put_local s n (local (current_term l) (role l) (log l) k (applied_index l)).
Definition apply_one s n :=
  let l := nodes s n in
  put_local s n (local (current_term l) (role l) (log l) (commit_index l) (S (applied_index l))).

Inductive Event :=
| ObserveTerm (n : Node) (t : Term)
| Timeout (n : Node)
| GrantVote (voter candidate : Node) (t : Term)
| WinElection (candidate : Node)
| ClientAppend (leader : Node) (cmd : Command)
| SendAppend (leader follower : Node)
| Deliver (m : Message)
| Commit (leader : Node) (k : nat)
| Apply (n : Node)
| DropMessages
| Duplicate (m : Message).

(* These guards specify the abstraction; none asks for the safety invariant
   or the desired conclusion as a premise. In particular, election uniqueness
   is derived from quorum intersection and irreversible per-term votes. *)
Inductive step : State -> Event -> State -> Prop :=
| step_observe s n t :
    current_term (nodes s n) < t ->
    step s (ObserveTerm n t) (put_local s n (change_term (nodes s n) t Follower))
| step_timeout s n :
    step s (Timeout n)
      (put_local s n (change_term (nodes s n) (S (current_term (nodes s n))) Candidate))
| step_vote s n c t :
    current_term (nodes s n) = t ->
    votes s t n = None ->
    step s (GrantVote n c t) (put_vote s t n c)
| step_elect s n :
    role (nodes s n) = Candidate ->
    certified s (current_term (nodes s n)) n ->
    log (nodes s n) = journal s ->
    step s (WinElection n) (elect s n)
| step_append s n cmd :
    role (nodes s n) = Leader ->
    log (nodes s n) = journal s ->
    (forall m, current_term (nodes s m) <= current_term (nodes s n)) ->
    step s (ClientAppend n cmd) (append s n cmd)
| step_send s n dst :
    role (nodes s n) = Leader ->
    step s (SendAppend n dst) (put_network s (outgoing s n dst :: network s))
| step_deliver s m :
    In m (network s) ->
    current_term (nodes s (receiver m)) <= message_term m ->
    prefix (log (nodes s (receiver m))) (payload m) ->
    step s (Deliver m) (deliver s m)
| step_commit s n k :
    role (nodes s n) = Leader ->
    commit_index (nodes s n) <= k ->
    k <= length (log (nodes s n)) ->
    quorum (fun m => k <= length (log (nodes s m))) ->
    (k = 0 \/ exists e, nth_error (log (nodes s n)) (k - 1) = Some e /\
                       entry_term e = current_term (nodes s n)) ->
    step s (Commit n k) (mark_commit s n k)
| step_apply s n :
    applied_index (nodes s n) < commit_index (nodes s n) ->
    step s (Apply n) (apply_one s n)
| step_drop s : step s DropMessages (put_network s [])
| step_duplicate s m :
    In m (network s) ->
    step s (Duplicate m) (put_network s (m :: network s)).

Definition initial : State :=
  state (fun _ => local 0 Follower [] 0 0) (fun _ _ => None) [] [] [].

Inductive reachable : State -> Prop :=
| reachable_initial : reachable initial
| reachable_step s ev s' : reachable s -> step s ev s' -> reachable s'.

Inductive steps : State -> State -> Prop :=
| steps_refl s : steps s s
| steps_next s ev s' s'' : step s ev s' -> steps s' s'' -> steps s s''.
