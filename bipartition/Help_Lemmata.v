Require Import GraphBasics.Graphs.
Require Import GraphBasics.Connected.
Require Import Coq.Logic.Classical_Prop.

Require FunInd.


Section Help.


Function get_end_vertex (a : Arc) (b : bool) : Vertex :=
  match a with
  | A_ends x y => match b with
	      | true => x
	      | false => y
        end
  end.

Lemma get_end_vertex_correct : forall (a : Arc) (b : bool) (x y : Vertex),
  a = A_ends x y ->
  get_end_vertex a b = x \/ get_end_vertex a b = y.
Proof.
  intros.
  rewrite H.
  simpl.
  destruct b.
  + left.
    reflexivity.
  + right.
    reflexivity.
Qed.

(* Our terminology for members of a network (graph). *)
Definition Component := Vertex.

(* Unequalness is symmetric. *)
Lemma neq_symm: forall (X : Type) {p q: X}, p <> q -> q <> p.
Proof.
  intros X p q pq.
  unfold not.
  intros.
  apply pq.
  symmetry.
  apply H.
Qed.

(* A natural number can't be even and odd at the same time. *)
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

(* A natural number is either odd or even. *)
Lemma even_or_odd: forall(n : nat),
  Nat.even n = true \/ Nat.odd n = true.
Proof.
  intros n.
  induction n.
  left.
  reflexivity.
  destruct IHn.
  right.
  rewrite Nat.odd_succ.
  apply H.
  left.
  rewrite Nat.even_succ.
  apply H.
Qed.

(* The definition of Connected doesn't allow loops (edges from some vertex to itself). *)
Lemma Connected_no_loops: forall (v: V_set) (a: A_set) (c : Connected v a) (x y : Vertex),
  a (A_ends x y) -> x <> y.
Proof.
  intros v a c x y arc.
  assert (g:= c).
  apply Connected_Isa_Graph in g.
  assert (v x). 
  apply (G_ina_inv1 v a g) in arc.
  apply arc.
  rename H into vx.
  assert (v y).
  apply (G_ina_inv2 v a g) in arc.
  apply arc.
  rename H into vy.
  induction c.

  inversion arc.

  assert (x0 <> y0).
  unfold not. intros.
  rewrite H in v0. intuition.

  inversion arc.
  inversion H0.
  rewrite H3 in H. rewrite H4 in H. apply H.
  rewrite H3 in H. rewrite H4 in H. intuition.
  apply IHc.
  apply H0.
  apply Connected_Isa_Graph in c. apply c.
  destruct vx.
  inversion H2.
  rewrite <- H3 in H0.
  apply (G_ina_inv1 v a) in H0.
  intuition.
  apply Connected_Isa_Graph in c. apply c.
  apply H2.
  destruct vy.
  inversion H2.
  rewrite <- H3 in H0.
  apply (G_ina_inv2 v a) in H0.
  intuition.
  apply Connected_Isa_Graph in c. apply c.
  apply H2.

  inversion arc.
  inversion H.
  rewrite H2 in n. rewrite H3 in n. apply n.
  rewrite H2 in n. rewrite H3 in n. intuition.
  apply (IHc H).
  apply Connected_Isa_Graph in c. apply c.
  apply vx. apply vy.

  apply IHc.
  rewrite <- e0 in arc.
  apply arc.
  rewrite <- e0 in g. rewrite <- e in g.
  apply g.
  rewrite <- e in vx.
  apply vx.
  rewrite <- e in vy.
  apply vy.
Qed.

End Help.