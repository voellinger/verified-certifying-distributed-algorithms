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


Axiom Tree_only_one_path : forall (v:V_set) (a:A_set) (x y : Component) (t : Tree v a) (vl vl' : V_list) (el el' : E_list)
  (p1 : Path v a x y vl el) (p2 : Path v a x y vl' el'),
  path_same v a vl vl' el el' x y p1 p2.

Lemma connected_path :
 forall (v : V_set) (a : A_set) (g : Connected v a) (x y : Component),
 v x -> v y -> {vl : V_list &  {el : E_list &  Path v a x y vl el}}.
Proof.
  intros; elim (Connected_walk v a g x y H H0); intros.
  elim p; intros.
  apply (Walk_to_path v a x y x0 x1 p0).
Qed.

Lemma connected_min_path: forall (v: V_set) (a: A_set) (x : Component) (t : Tree v a),
 v x -> {vl : V_list &  {el : E_list &  {p : Path v a root x vl el & distance2 v a root x (length el)}}}.
Proof.
  intros v a xx t vxx.
  assert (v root) as vroot.
  apply (all_trees_rooted v a).
  apply t.
  assert (t2 := t).
  apply Tree_isa_connected in t.
  apply (connected_path v a t root xx vroot) in vxx.
  destruct vxx.
  destruct s.
  exists x.
  exists x0.
  exists p.
  unfold distance2.
  exists x. exists x0. exists p.
  split.
  unfold shortest_path2.
  intros vl el p2.
  assert (vl = x /\ el = x0).
  apply (Tree_only_one_path v a root xx t2).
  apply p2.
  apply p.
  destruct H.
  unfold length_p.
  rewrite H0.
  reflexivity.
  reflexivity.
Qed.

Lemma connected_min_path2: forall (v: V_set) (a: A_set) (x : Component) (t : Tree v a),
 v x -> {vl : V_list &  {el : E_list &  {p : Path v a x root vl el & distance2 v a root x (length el)}}}.
Proof.
  intros v a x t vx.
  apply (connected_min_path v a x t) in vx.
  destruct vx.
  destruct s.
  destruct s.
  rename x0 into vl. rename x1 into el.
  exists (cdr Component(rev(root::vl))).
  exists (E_reverse el).
  assert (Path v a x root (cdr Component (rev (root :: vl))) (E_reverse el)).
  apply Path_reverse in x2.
  apply x2.
  apply Tree_isa_graph in t.
  apply t.
  exists H.
  unfold distance2.
  exists vl. exists el. exists x2.
  split.
  unfold shortest_path2.
  intros vl0 el0 p2.
  assert (vl = vl0 /\ el = el0).
  apply (Tree_only_one_path v a root x t).
  apply x2.
  apply p2.
  destruct H0.
  unfold length_p.
  rewrite H1.
  reflexivity.
  rewrite E_rev_len.
  reflexivity.
Qed.

End Tree_related.