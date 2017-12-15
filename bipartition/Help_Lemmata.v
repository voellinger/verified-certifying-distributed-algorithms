Require Import GraphBasics.Graphs.
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

Lemma Connected_no_loops: forall (v: V_set) (a: A_set) (c : Connected v a),
  a (A_ends x y) -> x <> y.
Proof.
  intros v a c



Inductive Connected : V_set -> A_set -> Set :=
  | C_isolated : forall x : Vertex, Connected (V_single x) A_empty
  | C_leaf :
      forall (v : V_set) (a : A_set) (co : Connected v a) (x y : Vertex),
      v x ->
      ~ v y -> Connected (V_union (V_single y) v) (A_union (E_set x y) a)
  | C_edge :
      forall (v : V_set) (a : A_set) (co : Connected v a) (x y : Vertex),
      v x ->
      v y ->
      x <> y ->
      ~ a (A_ends x y) ->
      ~ a (A_ends y x) -> Connected v (A_union (E_set x y) a)
  | C_eq :
      forall (v v' : V_set) (a a' : A_set),
      v = v' -> a = a' -> Connected v a -> Connected v' a'.

End Help.