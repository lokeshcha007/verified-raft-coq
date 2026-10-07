From Stdlib Require Import List Arith Lia.
From VerifiedRaft Require Import Prelude Model Safety.
Import ListNotations.

(* A concrete, inhabited path: A wins term 1 with A+B, appends command 42,
   replicates to B, commits, advertises the commit, and both nodes apply it. *)
Definition s1 := put_local initial A (change_term (nodes initial A) 1 Candidate).
Definition s2 := put_local s1 B (change_term (nodes s1 B) 1 Follower).
Definition s3 := put_vote s2 1 A A.
Definition s4 := put_vote s3 1 B A.
Definition s5 := elect s4 A.
Definition s6 := append s5 A 42.
Definition data_message := outgoing s6 A B.
Definition s7 := put_network s6 (data_message :: network s6).
Definition s8 := deliver s7 data_message.
Definition s9 := mark_commit s8 A 1.
Definition commit_message := outgoing s9 A B.
Definition s10 := put_network s9 (commit_message :: network s9).
Definition s11 := deliver s10 commit_message.
Definition s12 := apply_one s11 A.
Definition s13 := apply_one s12 B.

Lemma transition_1 : step initial (Timeout A) s1.
Proof. apply step_timeout. Qed.
Lemma transition_2 : step s1 (ObserveTerm B 1) s2.
Proof. apply step_observe; vm_compute; lia. Qed.
Lemma transition_3 : step s2 (GrantVote A A 1) s3.
Proof. apply step_vote; reflexivity. Qed.
Lemma transition_4 : step s3 (GrantVote B A 1) s4.
Proof. apply step_vote; reflexivity. Qed.
Lemma transition_5 : step s4 (WinElection A) s5.
Proof.
  apply step_elect; try reflexivity.
  unfold certified, quorum; left; split; reflexivity.
Qed.
Lemma transition_6 : step s5 (ClientAppend A 42) s6.
Proof. apply step_append; try reflexivity; intro n; destruct n; vm_compute; lia. Qed.
Lemma transition_7 : step s6 (SendAppend A B) s7.
Proof. apply step_send; reflexivity. Qed.
Lemma transition_8 : step s7 (Deliver data_message) s8.
Proof.
  apply step_deliver.
  - left; reflexivity.
  - vm_compute; lia.
  - apply prefix_nil.
Qed.
Lemma transition_9 : step s8 (Commit A 1) s9.
Proof.
  apply step_commit.
  - reflexivity.
  - vm_compute; lia.
  - vm_compute; lia.
  - unfold quorum; left; split; vm_compute; lia.
  - right; exists (entry 1 42); split; reflexivity.
Qed.
Lemma transition_10 : step s9 (SendAppend A B) s10.
Proof. apply step_send; reflexivity. Qed.
Lemma transition_11 : step s10 (Deliver commit_message) s11.
Proof.
  apply step_deliver.
  - left; reflexivity.
  - vm_compute; lia.
  - change (prefix [entry 1 42] [entry 1 42]); apply prefix_refl.
Qed.
Lemma transition_12 : step s11 (Apply A) s12.
Proof. apply step_apply; vm_compute; lia. Qed.
Lemma transition_13 : step s12 (Apply B) s13.
Proof. apply step_apply; vm_compute; lia. Qed.

Theorem successful_trace : steps initial s13.
Proof.
  eapply steps_next; [exact transition_1 |].
  eapply steps_next; [exact transition_2 |].
  eapply steps_next; [exact transition_3 |].
  eapply steps_next; [exact transition_4 |].
  eapply steps_next; [exact transition_5 |].
  eapply steps_next; [exact transition_6 |].
  eapply steps_next; [exact transition_7 |].
  eapply steps_next; [exact transition_8 |].
  eapply steps_next; [exact transition_9 |].
  eapply steps_next; [exact transition_10 |].
  eapply steps_next; [exact transition_11 |].
  eapply steps_next; [exact transition_12 |].
  eapply steps_next; [exact transition_13 |].
  apply steps_refl.
Qed.

Theorem successful_trace_reachable : reachable s13.
Proof. eapply trace_reachable; [apply successful_trace | apply reachable_initial]. Qed.

Example two_nodes_apply_42 :
  applied s13 A 0 (entry 1 42) /\ applied s13 B 0 (entry 1 42).
Proof. vm_compute; repeat split; lia. Qed.

Example follower_lags : log (nodes s13 C) = [] /\ applied_index (nodes s13 C) = 0.
Proof. split; reflexivity. Qed.

Example inconsistent_vote_rejected : forall target, ~ step s4 (GrantVote B C 1) target.
Proof. intros target H; inversion H; vm_compute in *; discriminate. Qed.

Example election_without_majority_rejected : forall target, ~ step s3 (WinElection A) target.
Proof. intros target H; inversion H; vm_compute in *; intuition discriminate. Qed.

Example unreplicated_commit_rejected : forall target, ~ step s6 (Commit A 1) target.
Proof. intros target H; inversion H; vm_compute in *; intuition lia. Qed.

Example follower_append_rejected : forall target, ~ step initial (ClientAppend B 7) target.
Proof. intros target H; inversion H; vm_compute in *; discriminate. Qed.

Definition advanced := put_local s13 B (change_term (nodes s13 B) 2 Follower).
Lemma advanced_reachable : reachable advanced.
Proof.
  eapply reachable_step; [apply successful_trace_reachable |].
  apply step_observe; vm_compute; lia.
Qed.

Example stale_message_rejected : forall target, ~ step advanced (Deliver data_message) target.
Proof. intros target H; inversion H; vm_compute in *; lia. Qed.

Example delayed_commit_cannot_uncommit :
  step s13 (Deliver data_message) (deliver s13 data_message) /\
  commit_index (nodes (deliver s13 data_message) B) = 1.
Proof.
  split; [| reflexivity]. apply step_deliver.
  - vm_compute; auto.
  - vm_compute; lia.
  - change (prefix [entry 1 42] [entry 1 42]); apply prefix_refl.
Qed.

Example duplicate_delivery_safe : invariant (deliver s13 data_message).
Proof.
  eapply safety_preserved.
  - apply reachable_invariant; apply successful_trace_reachable.
  - exact (proj1 delayed_commit_cannot_uncommit).
Qed.

(* A second election is possible: B times out into term 2, receives A+B votes,
   wins with the complete journal, and appends a new command in the new term. *)
Definition s14 := put_local s13 B (change_term (nodes s13 B) 2 Candidate).
Definition s15 := put_local s14 A (change_term (nodes s14 A) 2 Follower).
Definition s16 := put_vote s15 2 A B.
Definition s17 := put_vote s16 2 B B.
Definition s18 := elect s17 B.
Definition s19 := append s18 B 99.

Theorem leadership_change_trace : steps s13 s19.
Proof.
  eapply steps_next with (ev := Timeout B) (s' := s14); [apply step_timeout |].
  eapply steps_next with (ev := ObserveTerm A 2) (s' := s15).
  { apply step_observe; vm_compute; lia. }
  eapply steps_next with (ev := GrantVote A B 2) (s' := s16).
  { apply step_vote; reflexivity. }
  eapply steps_next with (ev := GrantVote B B 2) (s' := s17).
  { apply step_vote; reflexivity. }
  eapply steps_next with (ev := WinElection B) (s' := s18).
  { apply step_elect; try reflexivity.
    unfold certified, quorum; left; split; reflexivity. }
  eapply steps_next with (ev := ClientAppend B 99) (s' := s19).
  { apply step_append; try reflexivity; intro n; destruct n; vm_compute; lia. }
  apply steps_refl.
Qed.

Example committed_entry_survives_new_leader : committed s19 B 0 (entry 1 42).
Proof.
  eapply trace_committed_entries_remain; [apply leadership_change_trace |].
  vm_compute; split; [lia | reflexivity].
Qed.
