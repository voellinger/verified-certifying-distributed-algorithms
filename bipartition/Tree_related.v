Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.

Load "Path_Walk_related".


Section Tree_related.

(* All components of a tree have a connecting walk in between them. *)
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

(* All Connected have at least one component (therefore root exists). *)
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

(* A (special) component of a tree. *)
Variable root : Component.

(* The distance of the shortest path from c0 to root is n long. *)
Definition distance (v: V_set) (a: A_set) (c0 : Component) (n : nat) :=
  distance2 v a root c0 n.

(* The shortest path from root to root (the empty path) is of length 0. *)
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

End Tree_related.