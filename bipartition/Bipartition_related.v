Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.
Require Import Coq.Logic.Classical_Pred_Type.

Load "Tree_related".
Load "Spanning_Tree_related".




(* INTUITION OF THIS FILE
  -  neighbors in a bipartite graph are different colored
  -> every node of a walk alternates colors
  -> same color in even length walks for start and finish /
     diff color in odd  length walks for start and finish
  -  odd_closed_walk has odd length
  -> odd_closed_walk has different color for start/finish
  -> odd_closed_walk is not bipartite
  -  if subgraph is not bipartite -> the graph is not bipartite
  -> odd_closed_walk makes graph not bipartite

  -  neighbors_with_same_color makes odd_closed_walk
  -> neighbors_with_same_color makes graph not bipartite
*)

Section Bipartion_related.

(* a special component of a tree - its own parent, see next function *)
Variable root: Component.

(* a function that points towards the root of a tree *)
Variable parent : Component -> Component.
(* a function that holds the distance of the parent-path from this component to the root of a tree *)
Variable distance : Component -> nat.






(* a bipartition that colors a component in one of two colors: true or false,
  all neighboring components are of different color *)
Definition bipartition (a: A_set) (color : Component -> bool) : Prop :=
  forall (ar : Arc), a ar -> color (A_tail ar) <> color (A_head ar).

(* there can be a coloring that is a bipartition *)
Definition bipartite (a: A_set) := exists color : Component -> bool, bipartition a color.
(* Definition bipartite (a: A_set) := {color : Component -> bool & bipartition a color}. *)
(* a closed walk of odd length *)
Definition odd_closed_walk {v : V_set} {a : A_set} (x y : Component) (vl : V_list) (el : E_list) (w : Walk v a x y vl el)
 := Closed_walk v a x y vl el w /\ Nat.odd (length el) = true.
(* two neighboring components with both even or both odd length to the root *)
Definition neighbors_with_same_color (v:V_set) (a:A_set)(c: Connected v a) (t : spanning_tree v a root parent distance c) (v1 v2: Component) :=
  v v1 /\ v v2 /\ a (A_ends v1 v2) /\ Nat.odd (distance v1) = Nat.odd (distance v2).

(* a tree, that spans all components of the graph *)
Definition Gamma_2 := spanning_tree.
(* some component has a neighboring component, which has the evenness or oddity of distance towards the root *)
Definition gamma_3 (v:V_set) (a:A_set)(c: Connected v a) (t : spanning_tree v a root parent distance c) (v1 : Component) :=
 {v2 : Component & neighbors_with_same_color v a c t v1 v2}.
(* there exist some neighboring components, which both have the same evenness or oddity of distance towards the root *)
Definition Gamma_3 (v:V_set) (a:A_set)(c: Connected v a) (t : spanning_tree v a root parent distance c) :=
 {v1 : Component & gamma_3 v a c t v1}.
(* there exists a closed walk of odd length in the graph *)
Definition Gamma v a := {x:Component & {vl:V_list & {el : E_list & {w: Walk v a x x vl el & odd_closed_walk x x vl el w}}}}.

(* the graph is bipartite *)
Definition Psi1 a := bipartite a.
(* the graph is not bipartite *)
Definition Psi2 a := ~bipartite a.




(* 
  In a bipartite graph every component pair that is connected in the graph, must be of different color. Otherwise the very edge between the components is 
  in conflict with the definition of bipartiteness.
*)
Lemma neighbors_different: forall (v:V_set)(a:A_set)(x y: Component) (c : Connected v a) (color : Component -> bool),
  a (A_ends y x) -> v x -> v y -> bipartition a color -> color x <> color y.
Proof.
  intros v a x y c col ar vx vy bi.
  unfold bipartition in bi.
  
  specialize (bi (A_ends y x)).
  unfold A_tail in bi.
  unfold A_head in bi.
  unfold not.
  intros cxcy.
  intuition.
Qed.

(* 
  In a bipartite graph, if a walk is of even length its start (x) and its end (y) have the same color. If the walk is of odd length, x and y are of different
  color. 
  IStart: A walk of length 0 has x == y and therefore x and y are colored similarly.
  IStep : A walk of length n (w') has its end at y'. A walk of length n + 1 (w) uses (wlog) y'-y as its final edge. Therefore, using neighbors_different, 
  we know that color y' != color y. 
    1. If w' is of odd length, then color x != color y' != color y. Therefore w is of even length and color x = color y.
    2. If w' is of even length, then color x = color y' != color y. Therefore w is of odd length and color x != color y. Qed.
*)
Lemma walk_colored_ends: forall (v: V_set) (a: A_set) (vl : V_list) (el: E_list) (x y : Component) (c : Connected v a) 
                                (w: Walk v a x y vl el) (color : Component -> bool),
  bipartition a color -> ((Nat.odd (length el) = true -> color x <> color y) /\ (Nat.even (length el) = true -> color x = color y)).
Proof.
  intros v a vl el x y c w color H.

  elim w.
  intros.
  split.
  intros H0.
  inversion H0.
  reflexivity.
  
  intros.

  destruct H0.
  apply (neighbors_different v a y0 x0 c color) in a0.
  split.
  
  destruct (color x0).
  destruct (color z).
  destruct (color y0).
  intuition.
  intros.
  simpl in H2.
  rewrite Nat.odd_succ in H2.
  apply H1 in H2.
  inversion H2.
  destruct (color y0).
  intuition.
  intros.
  simpl in H2.
  rewrite Nat.odd_succ in H2.
  apply H1 in H2.
  intuition.
  destruct (color z).
  destruct (color y0).
  intuition.
  intuition.
  destruct (color y0).
  intros.
  simpl in H2.
  rewrite Nat.odd_succ in H2.
  apply H1 in H2.
  intuition.
  intros.
  simpl in H2.
  rewrite Nat.odd_succ in H2.
  apply H1 in H2.
  intuition.

  destruct (color x0).
  destruct (color z).
  destruct (color y0).
  intuition.
  intros.
  reflexivity.

  destruct (color y0).
  intuition.
  intros.
  
  destruct el0.
  simpl in H2.
  intuition.
  simpl in H2.
  simpl in H0.
  rewrite Nat.odd_succ in H0.
  apply H0 in H2.
  intuition.
  destruct (color z).
  destruct (color y0).
  intros.
  destruct el0.
  simpl in H2.
  intuition.
  simpl in H2.
  simpl in H0.
  rewrite Nat.odd_succ in H0.
  apply H0 in H2.
  intuition.
  intuition.
  reflexivity.


  apply (W_endx_inv ) in w0.
  apply w0.
  apply v0.
  apply H.
Qed.

(* odd_closed_walk is an odd cycle, meaning it ends at the same component, it started at and of odd length. Suppose the graph containing the closed_walk is bipartite.
Call the first and last component of the odd_closed_walk x. As it is a walk of odd length, we know by walk_colored_ends, that the first and last component 
must have different colors. As both first and last components are the same, we have a contradiction and the graph cannot be bipartite after all. *)
Lemma odd_closed_walk_no_bipartitition: forall (v : V_set) (a : A_set) (vl : V_list) (el: E_list) (x : Component) (c : Connected v a) (w: Walk v a x x vl el),
  odd_closed_walk x x vl el w -> ~ bipartite a.
Proof.
  intros.
  unfold odd_closed_walk in H.
  destruct H.
  unfold not.
  intros.
  unfold bipartite in H1.
  destruct H1 as [color bipartition].
  apply (walk_colored_ends v a vl el x x c w color) in bipartition.
  destruct bipartition.
  apply H1 in H0.
  intuition.
Qed.

(* If there is some non-bipartite graph, if you add more arcs there still won't be a bipartition possible. This is, because the old conflict of two neighbors, 
with the same color still exists in the smaller graph. Each arc added in fact can only possibly add new conflicts or be neutral at best. *)
Lemma graph_not_bi_graph_plus_not_bi: forall (v v' : V_set) (a a' : A_set) (c : Connected v a) (d : Connected (V_union v v') (A_union a a')),
  ~ bipartite a -> ~ bipartite (A_union a a').
Proof.
  intros.
  unfold not.
  intros.
  unfold bipartite in H0.
  unfold not in H.
  apply H.
  unfold bipartite.
  destruct H0.
  exists x.
  unfold bipartition in *.
  intros.
  apply H0.
  apply A_in_left.
  apply H1.
Qed.

(* Here we just combine the last two lemmas: we know an odd_closed_walk is not bipartite, if we add more arcs, then it still isn't bipartite, as per graph_not_bi_graph_plus_not_bi. *)
Lemma odd_closed_walk_rest_graph_not_bi: 
  forall (v v' : V_set) (a a' : A_set) (c : Connected v a) (vl : V_list) (el: E_list) (x :Component) (w : Walk v a x x vl el) (o: odd_closed_walk x x vl el w) 
    (d : Connected (V_union v v') (A_union a a')),
  ~ bipartite (A_union a a').
Proof.
  intros.
  apply (odd_closed_walk_no_bipartitition v a vl el x c w) in o.
  apply (graph_not_bi_graph_plus_not_bi v v' a a' c d) in o.
  intuition.
Qed.

(* Here we show that if there are two components in a tree, with both odd or both even distance to the root and they share an edge,
  (together they are gamma_3) that there must be an odd_closed_walk in the graph.
  Let distance(x, root) = 2*k distance(y, root) = 2*l then: 2*k + 2*l + 1 is odd (the cycle root----x-y----root)
  Let distance(x, root) = 2*k+1 distance(y, root) = 2*l+1 then: 2*k + 2*l + 2 + 1 is odd *)
Lemma gamma_3_makes_odd_closed_walk: 
  forall (v:V_set) (a:A_set) (c : Connected v a) (t : spanning_tree v a root parent distance c)(x : Component), 
  gamma_3 v a c t x -> 
{y: Component & {vlx : V_list & {vly : V_list & {elx: E_list & {ely: E_list & {w: Walk v a y y (x :: (vlx ++ vly)) ((E_ends y x) :: (elx ++ ely)) & 
odd_closed_walk y y (x :: (vlx ++ vly)) ((E_ends y x) :: (elx ++ ely)) w}}}}}}.
Proof.
  intros v a c t x H.

  unfold gamma_3 in H.
  destruct H.
  destruct n.
  destruct H0.
  destruct H1.
  assert (H4 := H2).

  assert (temp'' := t).
  unfold spanning_tree in t.
  destruct t.
  unfold root_prop in H3.
  rename H3 into rooted.

  apply (path_to_root2 v a c root parent distance) in H.
  destruct H.
  apply (Connection_to_walk v a parent (distance x) x root x1) in c0.
  destruct c0.
  destruct s.
  destruct s.
  rename x2 into vlx.
  rename x3 into elx.

  apply (path_to_root2 v a c root parent distance) in H0.
  destruct H0.
  apply (Connection_to_walk v a parent (distance x0) x0 root x2) in c0.
  destruct c0.
  destruct s.
  destruct s.
  assert (c' := c).
  apply Connected_Isa_Graph in c'.
  apply (Walk_reverse v a c' x0 root x3 x5) in x6.
  rename x3 into vly.
  rename x5 into ely.

  rename x0 into y.
  exists y.
  exists vlx.
  set (vlyy := (Paths.cdr (rev (y :: vly)))).
  exists (vlyy).
  exists elx.
  set (elyy := E_reverse ely).
  exists elyy.




  assert (temp := x4).
  apply (Walk_append v a x root y vlx vlyy elx elyy) in x4.
  
  apply (Walk_append v a y x y (x :: V_nil) (vlx ++ vlyy) (E_ends y x :: E_nil) (elx ++ elyy)) in x4.



  simpl in x4.
  exists x4.

  unfold odd_closed_walk.
  split.
  unfold Closed_walk.
  reflexivity.

  simpl.
  rewrite Nat.odd_succ.
  rewrite <- e0 in H4.
  rewrite <- e in H4.

  assert (Nat.even (length elx) = true \/ Nat.odd (length elx) = true).
  apply even_or_odd.
  destruct H.

  rewrite app_length.
  rewrite Nat.even_add.
  assert (Nat.even (length elyy) = true \/ Nat.odd (length elyy) = true).
  apply even_or_odd.
  destruct H0.
  apply Bool.eqb_true_iff.
  rewrite H.
  rewrite H0.
  reflexivity.
  assert (length (elyy) = length (ely)).

  unfold elyy in H0.
  rewrite E_rev_len in H0.
  rewrite <- H4 in H0.
  rewrite <- H0 in H.
  apply not_even_and_odd in H.
  inversion H.


  rewrite <- H3 in H4.
  rewrite <- H4 in H0.
  rewrite <- H0 in H.
  apply not_even_and_odd in H.
  inversion H.

  rewrite app_length.
  rewrite Nat.even_add.
  rewrite H in H4.
  unfold elyy.
  rewrite E_rev_len.
  apply Bool.eqb_true_iff.
  rewrite <- H in H4.
  rewrite <- Nat.negb_even in H4.
  rewrite <- Nat.negb_even in H4.
  destruct (Nat.even (length elx)).
  destruct (Nat.even (length ely)).
  reflexivity.
  inversion H4.
  destruct (Nat.even (length ely)).
  inversion H4.
  reflexivity.
  simpl.

  apply (W_step v a y x x (V_nil) (E_nil)).
  apply W_null.
  apply (W_endx_inv v a x root vlx elx) in temp.
  apply temp.
  apply (W_endy_inv v a x y (vlx ++ vlyy) (elx ++ elyy)) in x4.
  apply x4.

  apply (G_non_directed v a) in H1.
  apply H1.
  apply c'.

  auto.

  apply temp''.
  apply temp''.
Qed.

(* If there is a correct spanning tree (Gamma_2) and we have two components with both even or both odd length to root in this tree (Gamma_3), there exists
a closed walk of odd length (Gamma). *)
Theorem Gamma_2_Gamma_3_Gamma: forall (v: V_set) (a: A_set) (c: Connected v a) (G1: Gamma_2 v a root parent distance c),
  Gamma_3 v a c G1 -> Gamma v a.
Proof.
  intros v a c G1 G2.
  unfold Gamma.
  destruct G2.
  apply gamma_3_makes_odd_closed_walk in g.
  destruct g.
  destruct s.
  destruct s.
  destruct s.
  destruct s.
  destruct s.
  exists x0.
  exists (x :: x1 ++ x2).
  exists (E_ends x0 x :: x3 ++ x4).
  exists x5.
  apply o.
Qed.

(* If there exists a closed walk of odd length in the graph (Gamma), the graph itself is not bipartite (Psi). *)
Theorem Gamma_implies_Psi: forall (v :V_set) (a :A_set) (c: Connected v a),
  Gamma v a -> ~bipartite a.
Proof.
  intros v a c Gamma.
  destruct Gamma.
  destruct s.
  destruct s.
  destruct s.
  apply (odd_closed_walk_no_bipartitition v a x0 x1 x c x2) in o.
  apply o.
Qed.








Definition gamma_1 (v:V_set) (a:A_set) (c: Connected v a) (v1 : Component) (color : Component -> bool) :=
  forall (v2 : Component), v v2 /\ a (A_ends v1 v2) -> color v1 <> color v2.

Definition Gamma_1 (v:V_set) (a:A_set)(c: Connected v a) (color : Component -> bool) :=
  forall (v1 : Component), v v1 -> gamma_1 v a c v1 color.

Theorem Gamma_1_Psi1 : forall (v : V_set) (a : A_set) (c : Connected v a) (color : Component -> bool),
  Gamma_1 v a c color -> bipartite a.
Proof.
  intros v a c color G2'.
  unfold Gamma_1 in G2'.
  unfold bipartite.
  intros.
  unfold gamma_1 in G2'.
  exists color.
  unfold bipartition. intros.
  destruct ar.
  simpl in *.
  apply Connected_Isa_Graph in c.
  assert (v v0).
  apply (G_ina_inv1 v a) in H ; auto.
  assert (v v1).
  apply (G_ina_inv2 v a) in H ; auto.
  specialize (G2' v0). intuition.
  specialize (H5 v1). intuition.
Qed.

End Bipartion_related.