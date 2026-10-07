From Stdlib Require Import List Arith Lia.
From VerifiedRaft Require Import Prelude Model.
Import ListNotations.

Definition logs_consistent s := forall n, prefix (log (nodes s n)) (journal s).
Definition local_bounds s := forall n,
  applied_index (nodes s n) <= commit_index (nodes s n) /\
  commit_index (nodes s n) <= length (log (nodes s n)).
Definition elections_sound s := forall t n,
  In (t, n) (elections s) -> certified s t n.
Definition leaders_recorded s := forall n,
  role (nodes s n) = Leader -> In (current_term (nodes s n), n) (elections s).
Definition messages_safe s := forall m, In m (network s) ->
  prefix (payload m) (journal s) /\
  advertised_commit m <= length (payload m) /\
  In (message_term m, sender m) (elections s).

Record invariant s : Prop := {
  inv_logs : logs_consistent s;
  inv_bounds : local_bounds s;
  inv_elections : elections_sound s;
  inv_leaders : leaders_recorded s;
  inv_messages : messages_safe s
}.

(* Case splitting on finite map updates is constructive; no functional
   extensionality, classical axioms, or proof irrelevance are needed. *)
Ltac maps :=
  repeat match goal with
  | |- context [node_eq_dec ?x ?y] => destruct (node_eq_dec x y); subst
  | |- context [Nat.eq_dec ?x ?y] => destruct (Nat.eq_dec x y); subst
  end.
Ltac model_simpl :=
  cbv beta iota zeta delta [put_local change_term put_vote elect append outgoing put_network
       deliver mark_commit apply_one update] in *; cbn in *.

Theorem vote_persistent s ev s' t n c :
  step s ev s' -> votes s t n = Some c -> votes s' t n = Some c.
Proof.
  intros Hstep Hv. inversion Hstep; subst; model_simpl; try exact Hv.
  maps; model_simpl; congruence.
Qed.

Theorem terms_do_not_decrease s ev s' n :
  step s ev s' -> current_term (nodes s n) <= current_term (nodes s' n).
Proof.
  intro Hstep; inversion Hstep; subst; model_simpl; maps; model_simpl; lia.
Qed.

Lemma elections_persistent s ev s' t n :
  step s ev s' -> In (t, n) (elections s) -> In (t, n) (elections s').
Proof. intros Hstep H; inversion Hstep; subst; model_simpl; auto. Qed.

Lemma journal_append_only s ev s' : step s ev s' -> prefix (journal s) (journal s').
Proof.
  intro Hstep; inversion Hstep; subst; model_simpl; try apply prefix_refl.
  eexists; reflexivity.
Qed.

Theorem logs_append_only s ev s' n :
  step s ev s' -> prefix (log (nodes s n)) (log (nodes s' n)).
Proof.
  intro Hstep; inversion Hstep; subst; model_simpl; maps; model_simpl;
    try apply prefix_refl; try assumption.
  match goal with H : log (nodes _ _) = journal _ |- _ => rewrite H end.
  eexists; reflexivity.
Qed.

Theorem commit_index_monotone s ev s' n :
  step s ev s' -> commit_index (nodes s n) <= commit_index (nodes s' n).
Proof.
  intro Hstep; inversion Hstep; subst; model_simpl; maps; model_simpl;
    try lia; apply Nat.le_max_l.
Qed.

Theorem applied_index_monotone s ev s' n :
  step s ev s' -> applied_index (nodes s n) <= applied_index (nodes s' n).
Proof.
  intro Hstep; inversion Hstep; subst; model_simpl; maps; model_simpl; lia.
Qed.

Lemma logs_consistent_step s ev s' :
  logs_consistent s -> messages_safe s -> step s ev s' -> logs_consistent s'.
Proof.
  intros Hlogs Hmsgs Hstep n.
  inversion Hstep; subst; model_simpl; maps; model_simpl; try apply Hlogs.
  - apply prefix_refl.
  - eapply prefix_trans; [apply Hlogs | eexists; reflexivity].
  - match goal with H : In ?m (network s) |- _ => exact (proj1 (Hmsgs m H)) end.
Qed.

Lemma local_bounds_step s ev s' :
  local_bounds s -> messages_safe s -> step s ev s' -> local_bounds s'.
Proof.
  intros Hbounds Hmsgs Hstep n.
  inversion Hstep; subst; model_simpl; maps; model_simpl; try apply Hbounds.
  - rewrite length_app; simpl.
    match goal with H : log (nodes s ?who) = journal s |- _ =>
      pose proof (Hbounds who) as Hb; rewrite H in Hb end.
    lia.
  - pose proof (Hbounds (receiver m)) as [Ha Hc].
    match goal with H : In m (network s) |- _ =>
      pose proof (proj1 (proj2 (Hmsgs m H))) as Hmc end.
    match goal with H : prefix _ (payload m) |- _ =>
      pose proof (prefix_length _ _ H) as Hlen end.
    split; [eapply Nat.le_trans; [exact Ha | apply Nat.le_max_l] |].
    apply Nat.max_lub; lia.
  - match goal with |- applied_index (nodes s ?who) <= _ /\ _ =>
      pose proof (Hbounds who); lia end.
  - match goal with |- S (applied_index (nodes s ?who)) <= _ /\ _ =>
      pose proof (Hbounds who); lia end.
Qed.

Lemma elections_sound_step s ev s' :
  elections_sound s -> step s ev s' -> elections_sound s'.
Proof.
  intros Hsound Hstep t n Hin.
  inversion Hstep; subst; model_simpl.
  all: try solve [apply Hsound; exact Hin].
  - apply (quorum_mono _ _ (fun voter H => vote_persistent s _ _ t voter n Hstep H)).
    apply Hsound; exact Hin.
  - destruct Hin as [Heq | Hin]; [injection Heq as Heq1 Heq2; subst; assumption |].
    apply Hsound; exact Hin.
Qed.

Lemma leaders_recorded_step s ev s' :
  leaders_recorded s -> step s ev s' -> leaders_recorded s'.
Proof.
  intros Hleaders Hstep n Hleader.
  inversion Hstep; subst; model_simpl; unfold update in *;
    repeat match goal with H : context [node_eq_dec ?x ?y] |- _ =>
      destruct (node_eq_dec x y); subst; model_simpl end;
    maps; model_simpl; try discriminate;
    try solve [apply Hleaders; assumption | left; reflexivity | right; apply Hleaders; assumption].
Qed.

Lemma messages_safe_step s ev s' :
  logs_consistent s -> local_bounds s -> leaders_recorded s ->
  messages_safe s -> step s ev s' -> messages_safe s'.
Proof.
  intros Hlogs Hbounds Hleaders Hmsgs Hstep m Hin.
  inversion Hstep; subst; model_simpl;
    try solve [apply Hmsgs; exact Hin].
  - destruct (Hmsgs m Hin) as [Hp [Hb He]].
    split; [exact Hp | split; [exact Hb | right; exact He]].
  - destruct (Hmsgs m Hin) as [Hp [Hb He]].
    split; [eapply prefix_trans; [exact Hp | eexists; reflexivity] | auto].
  - destruct Hin as [<- | Hin]; [| apply Hmsgs; exact Hin].
    model_simpl. split; [apply Hlogs |].
    split; [exact (proj2 (Hbounds n)) | apply Hleaders; assumption].
  - contradiction.
  - destruct Hin as [-> | Hin]; apply Hmsgs; assumption.
Qed.

Theorem initial_invariant : invariant initial.
Proof.
  constructor; unfold logs_consistent, local_bounds, elections_sound,
    leaders_recorded, messages_safe, initial; simpl.
  - intro; apply prefix_refl.
  - intro; lia.
  - contradiction.
  - discriminate.
  - contradiction.
Qed.

Theorem safety_preserved s ev s' : invariant s -> step s ev s' -> invariant s'.
Proof.
  intros [Hlogs Hbounds Helections Hleaders Hmessages] Hstep.
  constructor; eauto using logs_consistent_step, local_bounds_step,
    elections_sound_step, leaders_recorded_step, messages_safe_step.
Qed.

Theorem reachable_invariant s : reachable s -> invariant s.
Proof.
  intro H; induction H; eauto using initial_invariant, safety_preserved.
Qed.

Theorem vote_consistency s ev s' t n c d :
  step s ev s' -> votes s t n = Some c -> votes s' t n = Some d -> c = d.
Proof.
  intros Hstep Hc Hd. pose proof (vote_persistent _ _ _ _ _ _ Hstep Hc).
  congruence.
Qed.

Theorem certificates_unique s t c d :
  certified s t c -> certified s t d -> c = d.
Proof.
  intros Hc Hd. destruct (quorum_intersection _ _ Hc Hd) as [n [Hn Hd']].
  congruence.
Qed.

(* Historical election safety is stronger than uniqueness of current roles. *)
Theorem election_safety s t c d :
  reachable s -> In (t, c) (elections s) -> In (t, d) (elections s) -> c = d.
Proof.
  intros Hr Hc Hd. pose proof (inv_elections _ (reachable_invariant _ Hr)) as H.
  eapply certificates_unique; eauto.
Qed.

Theorem at_most_one_leader_per_term s c d :
  reachable s -> role (nodes s c) = Leader -> role (nodes s d) = Leader ->
  current_term (nodes s c) = current_term (nodes s d) -> c = d.
Proof.
  intros Hr Hc Hd Ht. pose proof (inv_leaders _ (reachable_invariant _ Hr)) as H.
  eapply election_safety; [exact Hr | apply H; exact Hc |].
  rewrite Ht; apply H; exact Hd.
Qed.

(* This model proves a stronger, term-independent positional agreement. *)
Theorem log_position_agreement s n m i e f :
  reachable s -> nth_error (log (nodes s n)) i = Some e ->
  nth_error (log (nodes s m)) i = Some f -> e = f.
Proof.
  intros Hr He Hf. pose proof (inv_logs _ (reachable_invariant _ Hr)) as Hlogs.
  pose proof (prefix_nth _ _ _ _ (Hlogs n) He).
  pose proof (prefix_nth _ _ _ _ (Hlogs m) Hf). congruence.
Qed.

Theorem log_matching s n m i e f :
  reachable s -> nth_error (log (nodes s n)) i = Some e ->
  nth_error (log (nodes s m)) i = Some f -> entry_term e = entry_term f ->
  e = f /\ firstn (S i) (log (nodes s n)) = firstn (S i) (log (nodes s m)).
Proof.
  intros Hr He Hf Hterm. split; [eapply log_position_agreement; eauto |].
  pose proof (inv_logs _ (reachable_invariant _ Hr)) as Hlogs.
  assert (Hn : S i <= length (log (nodes s n))).
  { assert (i < length (log (nodes s n))) by
      (apply nth_error_Some; rewrite He; discriminate). lia. }
  assert (Hm : S i <= length (log (nodes s m))).
  { assert (i < length (log (nodes s m))) by
      (apply nth_error_Some; rewrite Hf; discriminate). lia. }
  rewrite (prefix_firstn _ _ _ (Hlogs n) Hn), (prefix_firstn _ _ _ (Hlogs m) Hm).
  reflexivity.
Qed.

Theorem leader_append_only s ev s' n :
  step s ev s' -> role (nodes s n) = Leader ->
  prefix (log (nodes s n)) (log (nodes s' n)).
Proof. intros Hstep _; eapply logs_append_only; eauto. Qed.

Theorem committed_entries_remain s ev s' n i e :
  step s ev s' -> committed s n i e -> committed s' n i e.
Proof.
  intros Hstep [Hidx Hentry]. split.
  - pose proof (commit_index_monotone _ _ _ n Hstep); lia.
  - eapply prefix_nth; [eapply logs_append_only; eauto | exact Hentry].
Qed.

Theorem state_machine_safety s n m i e f :
  reachable s -> applied s n i e -> applied s m i f -> entry_command e = entry_command f.
Proof.
  intros Hr [_ He] [_ Hf].
  pose proof (log_position_agreement _ _ _ _ _ _ Hr He Hf); now subst.
Qed.

Theorem applied_entries_are_committed s n i e :
  reachable s -> applied s n i e -> committed s n i e.
Proof.
  intros Hr [Hi He]. split; [| exact He].
  pose proof (proj1 (inv_bounds _ (reachable_invariant _ Hr) n)); lia.
Qed.

Theorem trace_terms_monotone s s' n :
  steps s s' -> current_term (nodes s n) <= current_term (nodes s' n).
Proof.
  intro H; induction H; [lia |].
  pose proof (terms_do_not_decrease _ _ _ n H); lia.
Qed.

Theorem trace_vote_persistent s s' t n c :
  steps s s' -> votes s t n = Some c -> votes s' t n = Some c.
Proof.
  intros H; induction H; intros Hv; [exact Hv |].
  apply IHsteps; eapply vote_persistent; eauto.
Qed.

Theorem trace_committed_entries_remain s s' n i e :
  steps s s' -> committed s n i e -> committed s' n i e.
Proof.
  intros H; induction H; intro Hc; [exact Hc |].
  apply IHsteps; eapply committed_entries_remain; eauto.
Qed.

Theorem trace_logs_append_only s s' n :
  steps s s' -> prefix (log (nodes s n)) (log (nodes s' n)).
Proof.
  intro H; induction H; [apply prefix_refl |].
  eapply prefix_trans; [eapply logs_append_only; eauto | exact IHsteps].
Qed.

Theorem trace_safety_preserved s s' :
  steps s s' -> invariant s -> invariant s'.
Proof.
  intro H; induction H; intro Hi; [exact Hi |].
  apply IHsteps; eapply safety_preserved; eauto.
Qed.

Theorem trace_reachable s s' : steps s s' -> reachable s -> reachable s'.
Proof.
  intro H; induction H; intro Hr; [exact Hr |].
  apply IHsteps; eapply reachable_step; eauto.
Qed.

Theorem state_machine_safety_across_time s s' n m i e f :
  reachable s -> steps s s' -> applied s n i e -> applied s' m i f ->
  entry_command e = entry_command f.
Proof.
  intros Hr Htrace [_ He] [_ Hf].
  assert (He' : nth_error (log (nodes s' n)) i = Some e).
  { eapply prefix_nth; [apply trace_logs_append_only; exact Htrace | exact He]. }
  assert (Hr' : reachable s') by (eapply trace_reachable; eauto).
  pose proof (log_position_agreement _ _ _ _ _ _ Hr' He' Hf); now subst.
Qed.

Theorem committed_prefix_stable s s' n :
  reachable s -> steps s s' ->
  firstn (commit_index (nodes s n)) (log (nodes s n)) =
  firstn (commit_index (nodes s n)) (log (nodes s' n)).
Proof.
  intros Hr Htrace. apply prefix_firstn.
  - apply trace_logs_append_only; exact Htrace.
  - exact (proj2 (inv_bounds _ (reachable_invariant _ Hr) n)).
Qed.
