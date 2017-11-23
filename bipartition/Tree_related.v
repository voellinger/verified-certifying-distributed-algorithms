Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.

Load "/home/lanpirot/Uni/COQ/verified-certifying-distributed-algorithms/bipartition/Path_Walk_related".


Section Tree_related.


Lemma tree_walk : forall (v: V_set) (a : A_set) (t : Tree v a) (x y: Component),
  v x -> v y -> {vl : V_list & {el : E_list & Walk v a x y vl el}}.
Proof.
  intros.
  apply Tree_isa_connected in t.
  apply Connected_walk.
  apply t.
  apply H.
  apply H0.
Qed.


Lemma v_not_empty : forall (v:V_set) (a:A_set) (c:Connected v a),
  exists (x:Component), v x.
Proof.
  intros v a c.
  assert (c':=c).
  induction c.
  exists x.
  unfold V_single.
  intuition.

  exists x.
  apply V_in_right.
  apply v0.
  

  exists x.
  apply v0.
  
  rewrite <- e.
  apply IHc.
  apply c.
Qed.


Variable root : Component.

Definition distance (v: V_set) (a: A_set) (c0 : Component) (n : nat) :=
  distance2 v a root c0 n.

Lemma distance_root_0: forall (v: V_set) (a: A_set), v root -> distance v a root 0.
Proof.
  intros v0 a0.
  unfold distance.
  unfold distance2.
  intros.
  assert (Path v0 a0 root root V_nil E_nil).
  apply P_null.
  apply H.
  exists V_nil. exists E_nil. exists H0.
  split.
  unfold shortest_path2.
  intros.
  simpl.
  intuition.
  reflexivity.
Qed.

Axiom nearly_all_connected_rooted': forall (v:V_set) (a:A_set) (x : Component) (g:Connected v a),
  v x -> v root.
(* Axiom root_is_unique ?? *)

Lemma nearly_all_trees_rooted: forall (v:V_set) (a:A_set) (x:Component) (t: Tree v a),
  v x -> v root.
Proof.
  intros v a x0 t vx.
  apply Tree_isa_connected in t.
  apply (nearly_all_connected_rooted' v a) in vx.
  apply vx.
  apply t.
Qed.

Lemma all_trees_rooted: forall (v:V_set) (a:A_set) (t: Tree v a),
  v root.
Proof.
  intros v a t.
  assert (exists (x : Component), v x).
  apply (v_not_empty v a).
  apply Tree_isa_connected in t.
  apply t.
  destruct H.
  apply (nearly_all_trees_rooted v a x t).
  apply H.
Qed.

End Tree_related.