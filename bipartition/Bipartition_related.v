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




Definition bipartite3 (a: A_set) := forall (ar : Arc), a ar -> color (A_tail ar) <> color (A_head ar).
Definition bipartite4 (a: A_set) := ~exists (ar : Arc), a ar /\ color (A_tail ar) = color (A_head ar).

Lemma bipar3_eq_bipar4: forall (a: A_set), bipartite3 a <-> bipartite4 a.
Proof.
  intros a.
  unfold bipartite3; unfold bipartite4.
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


Definition special_vertices (v:V_set) (a:A_set)(c: Connected v a) (t : spanning_tree v a root parent distance c) (x y : Component) :=
  v x /\ v y /\ a (A_ends x y) /\ odd (distance x) = odd (distance y) /\ x <> y.

Definition odd_closed {v : V_set} {a : A_set} (x y : Component) (vl : V_list) (el : E_list) (w : Walk v a x y vl el)
 := Closed_walk v a x y vl el w /\ odd (length el).


(* 
  In a bipartite graph every vertex pair that is connected in the graph, must be of different color. Otherwise the very edge between the vertices is 
  in conflict with the definition of bipartiteness.
*)
Lemma neighbours_different: forall (v:V_set)(a:A_set)(x y: Component) (c : Connected v a),
  a (A_ends y x) -> v x -> v y -> bipartite3 a -> color x <> color y.
Proof.
  intros v a x y c ar vx vy bi.
  unfold bipartite3 in bi.
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
  IStep : A walk of length n (w') has its end at y'. A walk of length n + 1 (w) uses (wlog) y'-y as its final edge. Therefore, using neighbours_different, 
  we know that color y' != color y. 
    1. If w' is of odd length, then color x != color y' != color y. Therefore w is of even length and color x = color y.
    2. If w' is of even length, then color x = color y' != color y. Therefore w is of odd length and color x != color y. Qed.
*)
Lemma walk_colored_ends: forall (v: V_set) (a: A_set) (vl : V_list) (el: E_list) (x y : Component) (c : Connected v a) (w: Walk v a x y vl el),
  bipartite3 a -> ((odd (length el) -> color x <> color y) /\ (even (length el) -> color x = color y)).
Proof.
  intros v a vl el x y c w H.

  elim w.
  intros.
  split.
  intros H0.
  inversion H0.
  reflexivity.
  
  intros .
  simpl.

  destruct H0.
  apply (neighbours_different v a y0 x0 c) in a0.
  split.
  
  destruct (color x0).
  destruct (color z).
  destruct (color y0).
  intuition.
  intros.
  apply S_even in H2.
  apply H1 in H2.
  inversion H2.
  destruct (color y0).
  intuition.
  intros.
  apply S_even in H2.
  apply H1 in H2.
  intuition.
  destruct (color z).
  destruct (color y0).
  intuition.
  intuition.
  destruct (color y0).
  intros.
  apply S_even in H2.
  apply H1 in H2.
  intuition.
  intros.
  apply S_even in H2.
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
  apply S_odd in H2.
  apply H0 in H2.
  intuition.
  destruct (color z).
  destruct (color y0).
  intros.
  apply S_odd in H2.
  apply H0 in H2.
  intuition.
  intuition.
  reflexivity.


  apply (W_endx_inv ) in w0.
  apply w0.
  apply v0.
  apply H.
Qed.

(* odd_closed is an odd cycle, meaning it ends at the same component, it startet at and of odd length. Suppose the graph containing the closed_walk is bipartite.
Call the first and last component of the odd_closed x. As it is a walk of odd length, we know by walk_colored_ends, that the first and last component 
must have different colors. As both first and last components are the same, we have a contradiction and the graph cannot be bipartite after all. *)
Lemma odd_closed_no_bipartitition: forall (v : V_set) (a : A_set) (vl : V_list) (el: E_list) (x : Component) (c : Connected v a) (w: Walk v a x x vl el),
  odd_closed x x vl el w -> ~ bipartite3 a.
Proof.
  intros.
  unfold odd_closed in H.
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
(* If there is some non-bipartite graph, if you add more arcs there still won't be a bipartition possible. This is, because the old conflict of two neighbours, 
with the same color still exists in the smaller graph. Each arc added in fact can only possibly add new conflicts or be neutral at best. *)
Lemma graph_not_bi_graph_plus_not_bi: forall (v v' : V_set) (a a' : A_set) (c : Connected v a) (d : Connected (V_union v v') (A_union a a')),
  ~ bipartite3 a -> ~ bipartite3 (A_union a a').
Proof.
  intros.
  unfold not.
  intros.
  unfold bipartite3 in H0.
  unfold not in H.
  apply H.
  unfold bipartite3.
  intros.
  apply H0.
  apply A_in_left.
  apply H1.
Qed.

(* Here we just combine the last two lemmas: we know an odd_closed is not bipartite, if we add more arcs, then it still isn't bipartite, as per graph_not_bi_graph_plus_not_bi. *)
Lemma odd_closed_rest_graph_not_bi: 
  forall (v v' : V_set) (a a' : A_set) (c : Connected v a) (vl : V_list) (el: E_list) (x :Component) (w : Walk v a x x vl el) (o: odd_closed x x vl el w) 
    (d : Connected (V_union v v') (A_union a a')),
  ~ bipartite3 (A_union a a').
Proof.
  intros.
  unfold not.
  intros.
  apply (odd_closed_no_bipartitition v a vl el x c w) in o.
  apply (graph_not_bi_graph_plus_not_bi v v' a a' c d) in o.
  intuition.
Qed.



(* Here we show that if there are two vertices in a tree, with both odd or both even distance to the root and they share an edge,
  (together they are special_vertices) that there must be an odd_closed altogether.
  Let distance(x, root) = 2*k distance(y, root) = 2*l then: 2*k + 2*l + 1 is odd (the cycle root----x-y----root)
  Let distance(x, root) = 2*k+1 distance(y, root) = 2*l+1 then: 2*k + 2*l + 2 + 1 is odd *)
Lemma special_vertices_make_odd_closed: 
  forall (v:V_set) (a:A_set) (c : Connected v a) (t : spanning_tree v a root parent distance c)(x y: Component), 
  special_vertices v a c t x y -> 
{vlx : V_list & {vly : V_list & {elx: E_list & {ely: E_list & {w: Walk v a y y (x :: (vlx ++ vly)) ((E_ends y x) :: (elx ++ ely)) & 
odd_closed y y (x :: (vlx ++ vly)) ((E_ends y x) :: (elx ++ ely)) w}}}}}.
Proof.
  intros v a c t x y H.

  unfold special_vertices in H.
  destruct H.
  destruct H0.
  destruct H1.
  destruct H2.
  assert (H4 := H2). assert (H5 := H3).

  assert (temp'' := t).
  unfold spanning_tree in t.
  destruct t.
  unfold root_prop in H6.
  rename H6 into rooted.

  apply (path_to_root2 v a c root parent distance) in H.
  destruct H.
  apply (Connection_to_walk v a parent (distance x) x root x0) in c0.
  destruct c0.
  destruct s.
  destruct s.
  rename x1 into vlx.
  rename x2 into elx.

  apply (path_to_root2 v a c root parent distance) in H0.
  destruct H0.
  apply (Connection_to_walk v a parent (distance y) y root x1) in c0.
  destruct c0.
  destruct s.
  destruct s.
  assert (c' := c).
  apply Connected_Isa_Graph in c'.
  assert (temp' := x5).
  apply (Walk_reverse v a c' y root x2 x4) in x5.
  rename x2 into vly.
  rename x4 into ely.

  exists vlx.
  set (vlyy := (Paths.cdr (rev (y :: vly)))).
  exists (vlyy).
  exists elx.
  set (elyy := E_reverse ely).
  exists elyy.




  assert (temp := x3).
  apply (Walk_append v a x root y vlx vlyy elx elyy) in x3.
  
  apply (Walk_append v a y x y (x :: V_nil) (vlx ++ vlyy) (E_ends y x :: E_nil) (elx ++ elyy)) in x3.



  simpl in x3.
  exists x3.

  unfold odd_closed.
  split.
  unfold Closed_walk.
  reflexivity.

  simpl.
  apply odd_S.
  rewrite <- e0 in H4.
  rewrite <- e in H4.

  assert (even (length elx) \/ odd (length elx)).
  apply even_or_odd.
  destruct H.


  rewrite app_length.
  apply even_even_plus.
  apply H.
  assert (even (length elyy) \/ odd (length elyy)).
  apply even_or_odd.
  destruct H0.
  apply H0.
  assert (length (elyy) = length (ely)).

  unfold elyy in H0.
  rewrite E_rev_len in H0.
  rewrite <- H4 in H0.
  apply not_even_and_odd in H0.
  inversion H0.
  apply H.
  rewrite <- H6 in H4.
  rewrite <- H4 in H0.
  apply not_even_and_odd in H0.
  inversion H0.
  apply H.

  rewrite app_length.
  apply odd_even_plus.
  apply H.
  rewrite H4 in H.
  unfold elyy.
  rewrite E_rev_len.
  apply H.
  simpl.

  apply (W_step v a y x x (V_nil) (E_nil)).
  apply W_null.
  apply (W_endx_inv v a x root vlx elx) in temp.
  apply temp.
  apply (W_endy_inv v a root y vlyy elyy) in x5.
  apply x5.

  apply (G_non_directed v a) in H1.
  apply H1.
  apply c'.

  apply x5.
  apply temp''.
  apply temp''.
Qed.

(* if there are special_vertices in some subgraph, then the supergraph cannot be bipartite *)
(* this should be remade with c as a subgraph of connected d instead of doing it by hand*)
(* also: a bipartiteness should be about graphs and not their arcs *)
Lemma special_vertices_make_connected_not_bi: forall (v v':V_set) (a a':A_set)(e: Connected v a) (t : spanning_tree v a root parent distance e) (x y : Component)
  (d : Connected (V_union v v') (A_union a a')),
  special_vertices v a e t x y -> ~ bipartite3 (A_union a a').
Proof.
  intros v0 v' a0 a' e t x y d H.
  apply special_vertices_make_odd_closed in H.
  destruct H.
  destruct s.
  destruct s.
  destruct s.
  destruct s.

  apply (odd_closed_rest_graph_not_bi v0 v' a0 a' e (x :: x0 ++ x1) (E_ends y x :: x2 ++ x3) y x4 o d).
Qed.

Definition bipartite (v : V_set) (a : A_set) (g: Graph v a) :=
  bipartite3 a.

Definition colored_spanning_tree (v: V_set) (a:A_set) (c: Connected v a):=
  spanning_tree v a root parent distance c -> (color root = true /\ forall (x : Component), (v x /\ x <> root) -> color x <> color (parent x)).

Definition colored_spanning_tree2 (v: V_set) (a:A_set) (c: Connected v a):=
  spanning_tree v a root parent distance c -> forall (x : Component), odd (distance x) -> color x = false /\ even (distance x) -> color x = true.

Lemma spanning_trees_can_be_colored: forall (v : V_set) (a : A_set) (c: Connected v a),
  spanning_tree v a root parent distance c -> colored_spanning_tree v a c.
Admitted.

Lemma no_special_vertices_make_connected_bi: forall (v : V_set) (a : A_set) (c: Connected v a) (t: spanning_tree v a root parent distance c),
  ~ (exists (x : Component), exists (y : Component), special_vertices v a c t x y) -> bipartite3 a.
Proof.
  intros v a c t H.
  assert (cst := t).
  apply (spanning_trees_can_be_colored v a c) in cst.
  unfold colored_spanning_tree in cst.
  destruct cst as [cst1 cst2].
  apply t.
  unfold not in H.
  unfold special_vertices in H.
  unfold bipartite3.
  unfold spanning_tree in t.
  destruct t as [t1 t2].
  unfold root_prop in t1.
  destruct ar.
  intros.
  exists v0 in H.
  specialize (cst2 v0).
  specialize (t2 v0).


(* INTUITION OF THIS FILE
  - neighbours in bipartite graph different
  - walk every node alternates
  - same color in even length walks for start and finish /
    diff color in odd  length walks for start and finish
  - odd_closed has odd length
  - odd_closed has different color for start/finish
  - odd_closed is not bipartite
  - if graph not bipartite -> graph+x not bipartite
  - odd_closed makes graph not bipartite

  - special edge makes odd closed
  - special edge makes graph not bipartite
*)

(* TODO: 
  - intros -> intros v a ...
  - define coloring
    - from a connected c get root
    - from root build a spanning tree t
    - color t bipartite
    - prove that: if there are no odd_closed in c -> this coloring is indeed a bipartition 
  - organize Variables and Axioms usefully
  - how to use global Variables?
  - how to generate Tree of some Connected : a -> ta --- maybe use Samira's work?
  - combine local and global properties:
    - from a connected c v a' get root
    - from root build a spanning tree t v a of c
    - there exists a special_vertices v a t x y /\ a' (A_ends x y)
    - it follows that c is not bipartite / there is no coloring for c that is bipartite
*)