Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.
Require Import Coq.Logic.Classical_Pred_Type.

Load "/home/lanpirot/Uni/COQ/verified-certifying-distributed-algorithms/bipartition/Tree_related".
Load "/home/lanpirot/Uni/COQ/verified-certifying-distributed-algorithms/bipartition/Spanning_Tree_related".

Section Bipartion_related.


(* 

Lemma path_to_root:
forall (n:nat) (x:Vertex) (prop1 : v x),
distance x = n -> {al : A_list & Connection x root al n }.

Lemma Connection_to_walk: forall (n:nat)(x y:Vertex)(al:A_list),
  (Connection x y al n) -> {vl : V_list & {el: E_list & {w: Walk v a x y vl el & length el = n}}}.



 *)


Variable parent : Vertex -> Vertex.
Variable distance : Vertex -> nat.
Variable color : Component -> bool.



Variable root: Vertex.




Definition bipartite (a: A_set) := forall (ar : Arc), a ar -> color (A_tail ar) <> color (A_head ar).
Definition bipartite2 (a: A_set) := ~exists (ar : Arc), a ar /\ color (A_tail ar) = color (A_head ar).

Lemma bipartite_eq_bipartite2: forall (a: A_set), bipartite a <-> bipartite2 a.
Proof.
  intros a.
  unfold bipartite; unfold bipartite2.
  split.
  intros H.
  intros H0.
  destruct H0.
  specialize (H x).
  destruct H0.
  apply H in H0.
  intuition.

  intros H ar H0.
  unfold not in H.
  unfold not.
  intros.
  apply H.
  exists ar.
  split.
  apply H0.
  apply H1.
Qed.


Definition neighbors_with_same_color (v:V_set) (a:A_set)(c: Connected v a) (t : spanning_tree v a root parent distance c) (v1 v2: Vertex) :=
  v v1 /\ v v2 /\ a (A_ends v1 v2) /\ Nat.odd (distance v1) = Nat.odd (distance v2).

Definition gamma_2 (v:V_set) (a:A_set)(c: Connected v a) (t : spanning_tree v a root parent distance c) (v1 : Vertex) :=
 {v2 : Vertex & neighbors_with_same_color v a c t v1 v2}.


Lemma gamma_2_no_parents: forall (v:V_set) (a:A_set)(c: Connected v a) (t : spanning_tree v a root parent distance c) (v1 v2: Vertex),
  neighbors_with_same_color v a c t v1 v2 -> (~parent v1 = v2 /\ ~ parent v2 = v1).
Proof.
  intros v a c t v1 v2 neighbors.
  unfold neighbors_with_same_color in neighbors.
  unfold spanning_tree in t.
  destruct t.
  assert (H1 := H0).
  rename H0 into H2.
  specialize (H1 v1).
  destruct H1.
  destruct neighbors.
  apply H0.
  specialize (H2 v2).
  destruct H2.
  destruct neighbors.
  destruct H3.
  apply H3.
  unfold distance_prop in H0.
  destruct neighbors.
  destruct H5.
  destruct H6.
  unfold distance_prop in H2.

  split.
  unfold not.
  intros.
  rewrite H8 in H0.
  destruct H0.
  destruct H0.
  rewrite H9 in H7.
  rewrite plus_comm in H7.
  simpl in H7.
  rewrite Nat.odd_succ in H7.
  apply not_even_and_odd in H7.
  inversion H7.

  destruct H0.
  rewrite H9 in H7.
  
  apply (Connected_no_loops v a c) in H6.
  unfold parent_prop in H1.
  destruct H1.
  destruct H1.
  intuition.
  destruct H1.
  rewrite H8 in H10.
  intuition.



  unfold not.
  intros.
  rewrite H8 in H2.
  destruct H2.
  destruct H2.
  rewrite H9 in H7.
  rewrite plus_comm in H7.
  simpl in H7.
  rewrite Nat.odd_succ in H7.
  symmetry in H7.
  apply not_even_and_odd in H7.
  inversion H7.

  destruct H2.
  rewrite H9 in H7.
  
  apply (Connected_no_loops v a c) in H6.
  unfold parent_prop in H3.
  destruct H3.
  destruct H3.
  intuition.
  destruct H3.
  rewrite H8 in H10.
  intuition.
Qed.


Definition odd_closed_walk {v : V_set} {a : A_set} (x y : Component) (vl : V_list) (el : E_list) (w : Walk v a x y vl el)
 := Closed_walk v a x y vl el w /\ Nat.odd (length el) = true.


(* 
  In a bipartite graph every vertex pair that is connected in the graph, must be of different color. Otherwise the very edge between the vertices is 
  in conflict with the definition of bipartiteness.
*)
Lemma neighbors_different: forall (v:V_set)(a:A_set)(x y: Component) (c : Connected v a),
  a (A_ends y x) -> v x -> v y -> bipartite a -> color x <> color y.
Proof.
  intros v a x y c ar vx vy bi.
  unfold bipartite in bi.
  specialize (bi (A_ends y x)).
  unfold A_tail in bi.
  unfold A_head in bi.
  unfold not.
  intros cxcy.
  intuition.
Qed.

(* 
  In a bipartite graph, if a walk is of even length its start (x) and its end (y) have the same color. If the walk is of odd length x and y are of different
  color. 
  IStart: A walk of length 0 has x == y and therefore x and y are colored similarly.
  IStep : A walk of length n (w') has its end at y'. A walk of length n + 1 (w) uses (wlog) y'-y as its final edge. Therefore, using neighbors_different, 
  we know that color y' != color y. 
    1. If w' is of odd length, then color x != color y' != color y. Therefore w is of even length and color x = color y.
    2. If w' is of even length, then color x = color y' != color y. Therefore w is of odd length and color x != color y. Qed.
*)
Lemma walk_colored_ends: forall (v: V_set) (a: A_set) (vl : V_list) (el: E_list) (x y : Component) (c : Connected v a) (w: Walk v a x y vl el),
  bipartite a -> ((Nat.odd (length el) = true -> color x <> color y) /\ (Nat.even (length el) = true -> color x = color y)).
Proof.
  intros v a vl el x y c w H.

  elim w.
  intros.
  split.
  intros H0.
  inversion H0.
  reflexivity.
  
  intros.

  destruct H0.
  apply (neighbors_different v a y0 x0 c) in a0.
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


(* odd_closed_walk is an odd cycle, meaning it ends at the same component, it startet at and of odd length. Suppose the graph containing the closed_walk is bipartite.
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
  apply (walk_colored_ends v a vl el x x) in H1.
  destruct H1.
  apply H1 in H0.
  intuition.
  apply c.
  apply w.
Qed.

(* is there a better subgraph function for this, maybe? *)
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
  unfold not.
  intros.
  apply (odd_closed_walk_no_bipartitition v a vl el x c w) in o.
  apply (graph_not_bi_graph_plus_not_bi v v' a a' c d) in o.
  intuition.
Qed.



(* Here we show that if there are two vertices in a tree, with both odd or both even distance to the root and they share an edge,
  (together they are gamma_2) that there must be an odd_closed_walk altogether.
  Let distance(x, root) = 2*k distance(y, root) = 2*l then: 2*k + 2*l + 1 is odd (the cycle root----x-y----root)
  Let distance(x, root) = 2*k+1 distance(y, root) = 2*l+1 then: 2*k + 2*l + 2 + 1 is odd *)
Lemma gamma_2_make_odd_closed_walk: 
  forall (v:V_set) (a:A_set) (c : Connected v a) (t : spanning_tree v a root parent distance c)(x : Component), 
  gamma_2 v a c t x -> 
{y: Vertex & {vlx : V_list & {vly : V_list & {elx: E_list & {ely: E_list & {w: Walk v a y y (x :: (vlx ++ vly)) ((E_ends y x) :: (elx ++ ely)) & 
odd_closed_walk y y (x :: (vlx ++ vly)) ((E_ends y x) :: (elx ++ ely)) w}}}}}}.
Proof.
  intros v a c t x H.

  unfold gamma_2 in H.
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

(* if there are gamma_2 in some subgraph, then the supergraph cannot be bipartite *)
(* this should be remade with c as a subgraph of connected d instead of doing it by hand*)
(* also: a bipartiteness should be about graphs and not their arcs *)
Lemma gamma_2_make_connected_not_bi: forall (v v':V_set) (a a':A_set)(e: Connected v a) (t : spanning_tree v a root parent distance e) (x : Component)
  (d : Connected (V_union v v') (A_union a a')),
  gamma_2 v a e t x -> ~ bipartite (A_union a a').
Proof.
  intros v0 v' a0 a' e t x d H.
  apply gamma_2_make_odd_closed_walk in H.
  destruct H.
  rename x0 into y.
  destruct s.
  destruct s.
  destruct s.
  destruct s.
  destruct s.

  apply (odd_closed_walk_rest_graph_not_bi v0 v' a0 a' e (x :: x0 ++ x1) (E_ends y x :: x2 ++ x3) y x4 o d).
Qed.

End Bipartion_related.

(* INTUITION OF THIS FILE
  - neighbors in bipartite graph different
  - walk every node alternates
  - same color in even length walks for start and finish /
    diff color in odd  length walks for start and finish
  - odd_closed_walk has odd length
  - odd_closed_walk has different color for start/finish
  - odd_closed_walk is not bipartite
  - if graph not bipartite -> graph+x not bipartite
  - odd_closed_walk makes graph not bipartite

  - special edge makes odd closed
  - special edge makes graph not bipartite
*)