Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.Even.
Require Import Coq.Logic.Classical_Pred_Type.

Load "/home/lanpirot/Uni/COQ/verified-certifying-distributed-algorithms/bipartition/help_lemmas".

Section Test.













Variable root : Component.
Variable color : Component -> bool.


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

(* could be remade without m and n, just use shortest_path *)
Definition special_vertices (v:V_set) (a:A_set) (t : Tree v a) (x y : Component) (n m : nat) :=
  v x /\ v y /\ ~ a (A_ends x y) /\ distance root v a x m /\ distance root v a y n /\ odd m = odd n /\ x <> y.

Definition odd_closed {v : V_set} {a : A_set} (x y : Vertex) (vl : V_list) (el : E_list) (w : Walk v a x y vl el)
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
  forall (v:V_set) (a:A_set) (t : Tree v a) (x y: Component) (m n : nat), 
  special_vertices v a t x y m n -> 
{vlx : V_list & {vly : V_list & {elx: E_list & {ely: E_list & {w: Walk v (A_union a (E_set x y)) y y (x :: (vlx ++ vly)) ((E_ends y x) :: (elx ++ ely)) & 
odd_closed y y (x :: (vlx ++ vly)) ((E_ends y x) :: (elx ++ ely)) w}}}}}.
Proof.
  intros v a t x y m n H.

  unfold special_vertices in H.
  destruct H.
  destruct H0.
  destruct H1.
  destruct H2.
  destruct H3.
  destruct H4.

  assert (rooted:=H).
  apply (nearly_all_trees_rooted root v a x t) in rooted.

  apply (connected_min_path2 root v a x t) in H.
  destruct H.
  destruct s.
  destruct s.
  apply (connected_min_path root v a y t) in H0.
  destruct H0.
  destruct s.
  destruct s.
  rename x0 into vlx.
  rename x1 into elx.
  rename x3 into vly.
  rename x4 into ely.
  exists vlx.
  exists vly.
  exists elx.
  exists ely.

  assert (temp := x2).
  apply Path_isa_walk in x2.
  apply (Walk_append v a x root y vlx vly elx ely) in x2.
  
  apply (Walk_subgraph v v a (A_union a (E_set x y)) x y) in x2.
  apply (Walk_append v (A_union a (E_set x y)) y x y (x :: V_nil) (vlx ++ vly) (E_ends y x :: E_nil) (elx ++ ely)) in x2.



  simpl in x2.
  exists x2.

  unfold odd_closed.
  split.
  unfold Closed_walk.
  reflexivity.

  simpl.
  apply odd_S.
  unfold distance in H2.
  unfold distance in H3.
  apply (distance_no_dup v a root x (length elx) n d) in H2.
  apply (distance_no_dup v a root y (length ely) m d0) in H3.

  rewrite <- H2 in H4.
  rewrite <- H3 in H4.

  assert (even (length elx) \/ odd (length elx)).
  apply even_or_odd.
  destruct H.


  rewrite app_length.
  apply even_even_plus.
  apply H.
  assert (even (length ely) \/ odd (length ely)).
  apply even_or_odd.
  destruct H0.
  apply H0.
  rewrite <- H4 in H0.
  apply not_even_and_odd in H0.
  inversion H0.
  apply H.

  rewrite app_length.
  apply odd_even_plus.
  apply H.
  rewrite H4 in H.
  apply H.
  simpl.

  apply (W_step v (A_union a (E_set x y)) y x x (V_nil) (E_nil)).
  apply W_null.
  apply (P_endx_inv v a x root vlx elx) in temp.
  apply temp.
  apply (P_endy_inv v a root y vly ely) in x5.
  apply x5.
  unfold A_union.
  apply A_in_right.
  apply E_left.
  unfold V_included.
  unfold Included.
  intros.
  apply H.
  unfold A_included.
  unfold Included.
  intros.
  apply A_in_left.
  apply H.
  apply Path_isa_walk in x5.
  apply x5.
Qed.

(* if there are special_vertices in some subgraph, then the supergraph cannot be bipartite *)
(* this should be remade with c as a subgraph of connected d instead of doing it by hand*)
Lemma special_vertices_make_graph_not_bi: forall (v v':V_set) (a a':A_set) (t : Tree v a) (x y : Component) (c: Connected v (A_union a (E_set x y)))
  (d : Connected (V_union v v') (A_union (A_union a (E_set x y)) a')) (vl : V_list) (el: E_list) (m n : nat),
  special_vertices v a t x y m n -> ~ bipartite3 (A_union (A_union a (E_set x y)) a').
Proof.
  intros v0 v' a0 a' t x y c d vl el m n H.
  apply special_vertices_make_odd_closed in H.
  destruct H.
  destruct s.
  destruct s.
  destruct s.
  destruct s.

  apply (odd_closed_rest_graph_not_bi v0 v' (A_union a0 (E_set x y)) a' c (x :: x0 ++ x1) (E_ends y x :: x2 ++ x3) y x4 o d).
Qed.

Definition spanning_tree: forall (v:V_set) (a:A_set) (c: Connected v a) := Tree v (sub_set a).

Definition colorable : forall (v : V_set) (a : A_set) (c: Connected v a) (x y : Component),
  exists c : color, bipartite3 a.

Lemma no_odd_closed_means_bi : forall (v : V_set) (a : A_set) (t : Tree v a) 
(d : Connected v a),
  ~(exists (x : Component) (el: E_list) (vl : V_list) (w: Walk v a x x vl el), odd_closed x x vl el w) -> "exists coloring which is bipartite / our coloring process is bipartite".
Proof.
  intros v a t d.
  unfold not.
  intros H.
  unfold bipartite3.
  intros ar.
  intros aar.
  unfold not.
  intros diff.
  apply H.
  
  


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