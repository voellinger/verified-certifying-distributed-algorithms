Require Import GraphBasics.Graphs.
Require Import GraphBasics.Connected.
Require Import Coq.Logic.Classical_Prop.




Section Help.

Definition Component := Vertex.

Lemma neq_symm: forall (X : Type) {p q: X}, p <> q -> q <> p.
Proof.
  intros X p q pq.
  unfold not.
  intros.
  apply pq.
  symmetry.
  apply H.
Qed.

Lemma not_even_and_odd: forall (n : nat),
  Nat.even n = Nat.odd n -> False.
Proof.
  intros n H.
  induction n.
  simpl in H.
  rewrite Nat.odd_0 in H.
  inversion H.
  apply IHn.
  rewrite Nat.even_succ in H.
  rewrite Nat.odd_succ in H.
  symmetry.
  apply H.
Qed.

Axiom Connected_no_loops: forall (v: V_set) (a: A_set) (c : Connected v a) (x y : Vertex),
  a (A_ends x y) -> x <> y.
(* if all else fails, the x <> y part could be put into gamma_2 *)

(* Lemma Connected_no_loops: forall (v: V_set) (a: A_set) (c : Connected v a) (x y : Vertex),
  a (A_ends x y) -> x <> y.
Proof.
  intros v a c x y arc.
  induction c.

  inversion arc.

(*   apply A_in_union_edge in arc.
  apply IHc.
  apply arc.
  intuition.
  destruct H.
  destruct arc.
  destruct x1.
  unfold E_set in H. *)
  admit.

  admit.

  apply IHc.
  rewrite <- e0 in arc.
  apply arc.
Qed. *)

End Help.