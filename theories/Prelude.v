From Stdlib Require Import List Arith Lia.
Import ListNotations.

Inductive Node := A | B | C.
Definition node_eq_dec : forall x y : Node, {x = y} + {x <> y}.
Proof. decide equality. Defined.

(* A strict majority in the fixed, non-Byzantine, three-node cluster. *)
Definition quorum (P : Node -> Prop) : Prop :=
  (P A /\ P B) \/ (P A /\ P C) \/ (P B /\ P C).

Lemma quorum_intersection P Q :
  quorum P -> quorum Q -> exists n, P n /\ Q n.
Proof. unfold quorum; intuition eauto. Qed.

Lemma quorum_mono P Q :
  (forall n, P n -> Q n) -> quorum P -> quorum Q.
Proof. unfold quorum; intuition eauto. Qed.

Definition update {X : Type} (f : Node -> X) n x : Node -> X :=
  fun m => if node_eq_dec m n then x else f m.

Lemma update_same {X} (f : Node -> X) n x : update f n x n = x.
Proof. unfold update; destruct (node_eq_dec n n); congruence. Qed.

Lemma update_other {X} (f : Node -> X) n x m :
  m <> n -> update f n x m = f m.
Proof. unfold update; destruct (node_eq_dec m n); congruence. Qed.

Definition prefix {X : Type} (xs ys : list X) : Prop :=
  exists tail, ys = xs ++ tail.

Lemma prefix_refl {X} (xs : list X) : prefix xs xs.
Proof. exists []; now rewrite app_nil_r. Qed.

Lemma prefix_nil {X} (xs : list X) : prefix [] xs.
Proof. exists xs; reflexivity. Qed.

Lemma prefix_trans {X} (xs ys zs : list X) :
  prefix xs ys -> prefix ys zs -> prefix xs zs.
Proof.
  intros [a ->] [b ->]. exists (a ++ b). now rewrite app_assoc.
Qed.

Lemma prefix_length {X} (xs ys : list X) :
  prefix xs ys -> length xs <= length ys.
Proof. intros [tail ->]; rewrite length_app; lia. Qed.

Lemma prefix_nth {X} (xs ys : list X) i x :
  prefix xs ys -> nth_error xs i = Some x -> nth_error ys i = Some x.
Proof.
  intros [tail ->] H. rewrite nth_error_app1; auto.
  apply nth_error_Some; rewrite H; discriminate.
Qed.

Lemma prefix_firstn {X} (xs ys : list X) k :
  prefix xs ys -> k <= length xs -> firstn k xs = firstn k ys.
Proof.
  intros [tail ->] H. rewrite firstn_app.
  replace (k - length xs) with 0 by lia. simpl. now rewrite app_nil_r.
Qed.

Lemma firstn_prefix {X} (xs : list X) k : prefix (firstn k xs) xs.
Proof. exists (skipn k xs); symmetry; apply firstn_skipn. Qed.
