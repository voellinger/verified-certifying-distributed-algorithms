Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.Even.

(* Load "/home/lanpirot/Uni/COQ/verified-certifying-distributed-algorithms/leader-election/composition_witness_prop_leader_election". *)


Section Help.

Definition Component := Vertex.





Lemma Path_isa_walk: 
  forall (v: V_set) (a: A_set) (x y : Vertex) (vl : V_list) (el : E_list),
  Path v a x y vl el -> Walk v a x y vl el.
Proof.
  intros.
  apply Path_isa_trail in H.
  apply Trail_isa_walk in H.
  apply H.
Qed.

Lemma Path_appended_isa_walk :
 forall (v: V_set) (a: A_set) (x y z : Vertex) (vl vl' : V_list) (el el' : E_list),
 Path v a x y vl el ->
 Path v a y z vl' el' -> Walk v a x z (vl ++ vl') (el ++ el').
Proof.
        intros v a x0 y0 z0 vl vl' el el' Hw; elim Hw; simpl; intros.
        apply Path_isa_walk in H.
        trivial.

        apply W_step.
        apply H.
        apply H0.
        apply v0.
        apply a0.
Qed.



Definition append_w (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (x y z:Vertex) (w1: Walk v a x y vl el) (w2: Walk v a y z vl' el') :=
  Walk v a x z (vl ++ vl') (el ++ el').

Definition append_p (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (x y z:Vertex) (p1: Path v a x y vl el) (p2: Path v a y z vl' el') :=
  Walk v a x z (vl ++ vl') (el ++ el').

Lemma Path_append (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (x y z:Vertex) (p1: Path v a x y vl el) (p2: Path v a y z vl' el'):
 Walk v a x z (vl ++ vl') (el ++ el') = append_p v a vl vl' el el' x y z p1 p2.
Proof.
  intros.
  unfold append_p.
  reflexivity.
Qed.

Function length_w {v: V_set} {a: A_set} {vl : V_list} {el: E_list} {c1 c2: Component} (p: Walk v a c1 c2 vl el) := length vl.
Function length_p {v: V_set} {a: A_set} {vl : V_list} {el: E_list} {c1 c2: Component} (p: Path v a c1 c2 vl el) := length vl.
(* Function distance {v: V_set} {a: A_set} (c: Component) := minimum length of all sets of Walks from c to root*)


Lemma Path_append_lengthsum (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (x y z:Vertex) (p1: Path v a x y vl el) (p2: Path v a y z vl' el') (p3: append_p v a vl vl' el el' x y z p1 p2):
  length_p p1 + length_p p2 = length_w p3.
Proof.
  intros.
  unfold length_p.
  unfold length_w.
  symmetry.
  rewrite app_length.
  reflexivity.
Qed.

Lemma W_inel_ina :
 forall (v: V_set) (a: A_set) (x y : Component) (vl : V_list) (el : E_list),
 Walk v a x y vl el ->
 forall x' y' : Component, In (E_ends x' y') el -> a (A_ends x' y').
Proof.
  intros v a x0 y0 vv e w; elim w; intros.
  inversion H.

  inversion H0.
  inversion H1.
  rewrite <- H3; rewrite <- H4; trivial.

  auto.
Qed.

Lemma W_endx_inv :
 forall (v: V_set) (a: A_set) (x y : Component) (vl : V_list) (el : E_list), Walk v a x y vl el -> v x.
Proof.
        intros. inversion H. apply H0. apply H1.
Qed.

Lemma W_endy_inv :
 forall (v: V_set) (a: A_set) (x y : Component) (vl : V_list) (el : E_list), Walk v a x y vl el -> v y.
Proof.
        intros. elim H. intros. apply v0. intros. apply H0.
Qed.

Lemma S_even : forall n: nat, odd (S n) -> even n.
Proof.
  intros.
  inversion H.
  apply H1.
Qed.

Lemma S_odd : forall n: nat, even (S n) -> odd n.
Proof.
  intros.
  inversion H.
  apply H1.
Qed.

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
Axiom nearly_all_connected_rooted': forall (v:V_set) (a:A_set) (x : Component) (g:Connected v a),
  v x -> v root.

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

Definition shortest_path2 {v: V_set} {a:A_set} {vl : V_list} {el : E_list} (c0 c1 : Component) {p: Path v a c0 c1 vl el} := 
  forall (vl': V_list) (el' : E_list), Path v a c0 c1 vl' el' -> length vl <= length vl'.

Definition distance2 (v: V_set) (a: A_set) (c0 c1 : Component) (n : nat) :=
  forall (vl : V_list) (el : E_list) (p: Path v a c0 c1 vl el), n <= length el.

Lemma distance_root_0: forall (v: V_set) (a: A_set) (root:Component), distance2 v a root root 0.
Proof.
  intros v0 a0.
  unfold distance2.
  intros.
  inversion p.
  simpl.
  reflexivity.
  simpl.
  intuition.
Qed.

Lemma Path_append2 : forall (v: V_set) (a: A_set) (x y z : Vertex) (vl vl' : V_list) (el el' : E_list),
  (forall (c: Component), In c vl -> ~ In c vl') -> (forall u u': Edge, In u el -> In u' el' -> ~ E_eq u' u) ->
  (x = y -> vl = V_nil) -> 
  Path v a x y vl el ->  Path v a y z vl' el' -> (In x vl' -> x = z) ->
  Path v a x z (vl ++ vl') (el ++ el').
Proof.
  intros v a x y z vl vl' el el' H0 H3 c1 p1 p2 lasso.



  induction p1.
  simpl.
  apply p2.


  simpl.
  apply P_step.
  apply IHp1.
  intros.
  apply H0.
  unfold In.
  right.
  apply H.


  intros.
  apply H3.
  unfold In.
  right.
  apply H.
  apply H1.

  intros.
  rewrite <- H in p1.
  destruct vl.
  reflexivity.

  apply P_iny_vl in p1.
  intuition.
  unfold not.
  intros.
  inversion H1.

  apply p2.


  intros.
  apply (H0 y) in H.
  inversion H.
  unfold In.
  left.
  reflexivity.




  apply v0.
  apply a0.
  apply n.
  unfold not.
  intros.
  apply in_app_or in H.
  destruct H.
  intuition.
  unfold not in H0.
  apply (H0 y).
  simpl.
  left.
  reflexivity.
  apply H.

  intros.
  apply in_app_or in H.
  destruct H.
  apply e in H.
  apply c1 in H.
  inversion H.
  
  apply lasso in H.
  inversion H.
  reflexivity.
  
  intros.
  apply in_app_or in H.
  destruct H.
  assert (In u (E_ends x y :: el)).
  unfold In.
  right.
  apply H.
  apply n1.
  apply H.

  apply (H3 (E_ends x y) u).
  unfold In.
  left.
  reflexivity.
  apply H.
Qed.

Lemma E_eq2 : forall (e1 e2 : Edge),
  E_eq e1 e2 -> E_eq e2 e1.
Proof.
  intros e1 e2 eq.
  inversion eq.
  apply E_refl.
  apply E_rev.
Qed.

Lemma neq_symm: forall {p q: V_list}, p <> q -> q <> p.
Proof.
  intros p q pq.
  unfold not.
  intros.
  apply pq.
  symmetry.
  apply H.
Qed.

Lemma E_rev_cons: forall(u:Edge)(el:E_list),
  E_reverse (u :: el) = (E_reverse el) ++ (E_reverse (u :: nil)).
Proof.
  intros u el.
  induction el.
  simpl.
  reflexivity.
  destruct u.
  destruct a.
  unfold E_reverse.
  reflexivity.
Qed.


Lemma E_rev_in2: forall (x y : Vertex) (el : E_list),
  In (E_ends x y) (E_reverse el) -> In (E_ends y x) el.
Proof.
  intros x y el i.
  induction el.
  simpl in i.
  inversion i.

  destruct a.
  simpl.
  simpl in i.
  apply in_app_or in i.
  destruct i.
  right.
  apply IHel.
  apply H.
  left.
  unfold In in H.
  destruct H.
  inversion H.
  reflexivity.
  inversion H.
Qed.

Lemma E_rev_in: forall (u: Edge) (x y : Vertex) (el : E_list),
(forall v:Edge, In v el -> ~ E_eq v (E_ends x y)) -> In u (E_reverse el) -> ~ E_eq u (E_ends y x).
Proof.
  intros u x y el vv uu.
  unfold not.
  intros.
  destruct u.
  apply E_rev_in2 in uu.
  apply vv in uu.
  inversion H.
  rewrite H2 in uu.
  rewrite H3 in uu.
  assert (E_eq (E_ends x y) (E_ends x y)).
  apply E_refl.
  apply uu in H1.
  inversion H1.
  rewrite H3 in uu.
  rewrite H4 in uu.
  assert (E_eq (E_ends y x) (E_ends x y)).
  apply E_rev.
  apply uu in H0.
  inversion H0.
Qed.



Lemma Path_cons : forall (v: V_set) (a: A_set) (x y z: Vertex) (vl : V_list) (el : E_list),
  v z -> a (A_ends y z) -> (x = y -> vl = V_nil) -> y <> z -> ~ In z vl -> (forall u : Edge, In u el -> ~ E_eq u (E_ends y z)) ->
  Path v a x y vl el -> Path v a x z (vl ++ z :: nil) (el ++ (E_ends y z) :: nil).
Proof.
  intros v a x y z vl el vz ayz xy yz zvl uu p.

  induction p.
  simpl.
  apply P_step.
  apply P_null.
  apply vz.
  apply v0.
  apply ayz.
  apply yz.
  unfold not.
  intros.
  inversion H.
  intros.
  inversion H.
  apply uu.

  simpl.
  apply P_step.
  apply IHp.
  apply ayz.
  intros.
  rewrite <- H in p.
  inversion p.
  reflexivity.
  apply P_iny_vl in p.
  apply n0 in p.
  inversion p.
  symmetry in H9.
  unfold not.
  intros.
  rewrite H11 in H9.
  inversion H9.
  apply yz.
  unfold not.
  intros.
  apply zvl.
  unfold In.
  right.
  apply H.
  intros.
  apply uu.
  unfold In.
  right.
  apply H.
  apply v0.
  apply a0.
  apply n.
  unfold not.
  intros.
  apply in_app_or in H.
  destruct H.
  apply n0 in H.
  inversion H.
  inversion H.
  rewrite H0 in zvl.
  apply zvl.
  simpl.
  left.
  reflexivity.
  inversion H0.
  intros.
  apply in_app_or in H.
  destruct H.
  apply e in H.
  apply xy in H.
  inversion H.
  inversion H.
  symmetry.
  apply H0.
  inversion H0.
  intros.
  apply in_app_or in H.
  destruct H.
  apply n1 in H.
  apply H.
  destruct H.
  unfold not.
  intros.
  rewrite <- H in H0.
  apply E_eq2 in H0.
  apply uu in H0.
  inversion H0.
  unfold In.
  left.
  reflexivity.
  inversion H.
Qed.


Lemma cdr_rev: forall (x:Vertex) (vl:V_list),
  In x (cdr (rev vl)) -> In x vl.
Proof.
  intros x vl i.
  induction vl.
  simpl in i.
  inversion i.
  unfold In.
  simpl in i.
  destruct vl.
  simpl in i.
  inversion i.
  rewrite cdr_app in i.
  apply in_app_or in i.
  destruct i.
  right.
  apply IHvl.
  apply H.
  left.
  inversion H.
  apply H0.
  inversion H0.
  apply neq_symm.
  apply app_cons_not_nil.
Qed.

Lemma P_xz_or_xnz2 : forall (v: V_set) (a:A_set) (x y z: Vertex) (vl : V_list) (el : E_list),
  Path v a x y vl el -> ~ In x (cdr (rev vl)) -> Path v a x z (vl ++ z :: nil) (el ++ (E_ends y z) :: nil) ->
  ~ In x (cdr (rev (vl ++ z :: nil))).
Proof.
  intros v a x y z vl el p1 i p2.
  induction p1.
  unfold not.
  intros.
  rewrite rev_unit in H.
  simpl in H.
  inversion H.

  unfold not. intros.
  rewrite rev_unit in H.
  simpl in H.
  (* H & n -> x in vl, x in vl & e -> x = z0, x = z0 & p2 -> p1 empty (vl = V_nil), 
    vl = V_nil $%&\u00a7 H *)

  apply in_app_or in H.
  destruct H.
  apply in_rev in H.
  assert (H' := H).
  apply e in H'.
  rewrite <- H' in p2.
  assert (vl = V_nil).
  admit.
  rewrite H0 in H.
  inversion H.
  inversion H.
  symmetry in H0.
  apply n in H0.
  inversion H0.
  inversion H0.
Admitted.

Lemma cdr_rev2: forall (vl : V_list) (x y : Vertex),
  ~ In x (cdr (rev vl)) -> x <> y -> ~ In x (cdr (rev (y::vl))).
Proof.
  intros vl x y i xy.
  unfold not. intros.

  assert (vl = nil \/ vl <> nil).
  apply classic.
  destruct H0.
  rewrite H0 in H.
  inversion H.
  
  simpl in H.
  rewrite cdr_app in H.
  apply in_app_or in H.
  destruct H.
  apply i in H.
  inversion H.
  inversion H.
  intuition.
  intuition.
  unfold not.
  intros.
  unfold V_nil in H1.
  assert (rev vl = nil -> vl = nil).
  intros.
  induction vl.
  reflexivity.
  inversion H1.
  symmetry in H4.
  apply app_cons_not_nil in H4.
  inversion H4.
  apply H2 in H1.
  apply H0 in H1.
  inversion H1.
Qed.

(* Lemma cdr_rev4: forall (vl : V_list) (x y : Vertex),
  In x (cdr (rev vl)) -> In x (cdr (rev (y :: vl))).
Proof.
  intros vl x y i.
  induction vl.
  intuition.
  
  

Lemma cdr_rev3: forall (vl : V_list) (x y : Vertex),
  ~ In x (cdr (rev (y::vl))) -> ~ In x (cdr (rev vl)).
Proof.
  intros vl x y i.
  unfold not. intros.
  apply i.
  destruct vl.
  intuition.

  simpl.

  induction vl.
  intuition.
  apply IHvl.
  unfold not. intros.
  apply i.
  admit.
  simpl in H.
  rewrite cdr_app in H.
  apply in_app_or in H.
  destruct H.
  apply H.
  inversion H.
  simpl in i.
  rewrite cdr_app in i.
  rewrite cdr_app in i.
(*   assert ~ In (a ++ b) -> ~ In a /\ ~ In b. *)
  admit. *)
  

(*  P_xz_or_xnz: In x vl -> x = last (length vl) v0 vl
    no element can be in vl twice *)


(* Lemma P_not_y_in_cdrvl : forall (v: V_set) (a:A_set) (x y z: Vertex) (vl : V_list) (el : E_list),
  Path v a y z vl el -> ~ In z (cdr (rev vl)) -> Path v a x z (y::vl) ((E_ends x y :: el)) ->
  ~ In z (cdr (rev (y :: vl))).
Proof.
  intros v a x y z vl el p1 i p2.

  assert (x = z \/ x <> z).
  apply classic.
  destruct H.

  induction p1.
  unfold not.
  intros.
  simpl in H0.
  inversion H0.

  apply (cdr_rev2 (y::vl) z x0) in i.
  apply i.
  apply P_backstep in p2.
  inversion p2.

Lemma P_not_y_in_cdrvl : forall (v: V_set) (a:A_set) (x y : Vertex) (vl : V_list) (el : E_list),
  Path v a x y vl el -> ~ In y (cdr (rev vl)).
Proof.
  intros v a x y vl el p.
  unfold not. intros. *)


Lemma P_xz_or_xnz : forall (v: V_set) (a:A_set) (x y : Vertex) (vl : V_list) (el : E_list),
  Path v a x y vl el -> ~ In x (cdr (rev vl)).
Proof.
  intros v a x y vl el p.
(*   elim p.
  unfold not.
  intros.
  inversion H.
  unfold not.
  intros.
  clear p. clear x. clear y. clear vl. clear el.
  rename x0 into x.
  rename y0 into y.
  rename vl0 into vl.
  rename el0 into el.

  unfold not.
  intros.
  assert (x = z \/ x <> z).
  apply classic.
  destruct H1. *)



  unfold not.
  intros.
  induction p.
  simpl in H.
  inversion H.
  (* assert (

Lemma cdr_rev2: forall (vl : V_list) (x y : Vertex),
  ~ In x (cdr (rev vl)) -> x <> y -> ~ In x (cdr (rev (y::vl))). *)


Admitted.

Lemma Path_reverse :
 forall (v: V_set) (a: A_set) (x y : Vertex) (vl : V_list) (el : E_list) (g: Graph v a),
 Path v a x y vl el -> Path v a y x (cdr (rev (x :: vl))) (E_reverse el).
Proof.
  intros v a x y vl el g p.

  induction p.
  simpl.
  apply P_null.
  apply v0.
  

  simpl.
  rewrite cdr_app.
  apply (Path_cons).
  apply v0.
  apply (G_non_directed v a g) in a0.
  apply a0.
  intros.
  rewrite H in p.
  inversion p.
  reflexivity.
  apply P_iny_vl in p.
  apply n0 in p.
  inversion p.
  unfold not.
  intros.
  rewrite H11 in H9.
  inversion H9.
  auto.

  unfold not.
  intros.
  rewrite cdr_app in H.
  apply in_app_or in H.
  destruct H.
  assert (Path v a x z (y :: vl) ((E_ends x y)::el)).
  apply P_step.
  apply p.
  apply v0.
  apply a0.
  apply n.
  apply n0.
  apply e.
  apply n1.
  apply (P_xz_or_xnz v a x z) in H0.
  apply H0.
  simpl.
  rewrite cdr_app.
  apply in_or_app.
  left.
  apply H.
  unfold not.
  intros.
  rewrite H1 in H.
  simpl in H.
  inversion H.


  inversion H.
  symmetry in H0.
  apply n in H0.
  inversion H0.
  inversion H0.
  destruct vl.
  simpl in H.
  inversion H.
  apply neq_symm.
  apply app_cons_not_nil.
  intros.
  apply (E_rev_in u x y el).
  apply n1.
  apply H.
  apply IHp.
  apply neq_symm.
  apply app_cons_not_nil.
Qed.

(* There can only be one path in a tree t, ending in vertices x and y.

Suppose there are two paths from x to y: p1 and p2. p1 and p2 must be out of three parts: el_p1 = a b1 c, el_p2 = a b2 c.
With b1 completely different from b2.
b1 (rev b2) makes a cycle. This cycle must be of length 0, because t is acyclic as it is a tree. therefore el_p1 = el_p2.

I Suppose we only have a root. There is only the path from root to root and that is equivalent to all other such paths.
II Suppose we add v as a leaf to t. For all paths not containing v we use IS. If v is contained in a path, then at its start
or at its end, otherwise it is no path, as v is a leaf and only has degree 1. Let v = y. All paths from x to the neighbor of
y are the same. As y has degree of 1, there is only one possible extension to those paths. Therefore all paths from x to y
are the same.
 *)

Lemma Paths_into_three_parts : forall (v:V_set) (a:A_set) (x y : Component) (vla vlb : V_list) (ela elb : E_list)
  (pa : Path v a x y vla ela) (pb : Path v a x y vlb elb),
  exists (vl1 vl2a vl2b vl3 : V_list) (x1 x2 : Vertex) (el2a el2b : E_list)
  (p2a: Path v a x1 x2 vl2a el2a) (p2b: Path v a x1 x2 vl2b el2b), 
  vla = vl1 ++ vl2a ++ vl3 /\ vlb = vl1 ++ vl2b ++ vl3 /\ 
  (forall z: Vertex, In z vl2a -> ~ In z vl2b) /\ (forall z: Vertex, In z vl2b -> ~ In z vl2a).
Proof.
  intros.
Admitted.

Lemma Tree_only_one_path : forall (v:V_set) (a:A_set) (x y : Component) (t : Tree v a) (vl vl' : V_list) (el el' : E_list)
  (p1 : Path v a x y vl el) (p2 : Path v a x y vl' el'),
  vl = vl' /\ el = el'.
Proof.
  intros v a x y t vl vl' el el' p1 p2.
  assert (three_parts := p2).
  apply (Paths_into_three_parts v a x y vl vl' el el' p1) in three_parts.
Admitted.

Lemma connected_min_path': forall (v: V_set) (a: A_set) (x : Component) (t : Tree v a),
 v x -> {vl : V_list &  {el : E_list &  {p : Path v a root x vl el & distance2 v a root x (length el)}}}.
Proof.
  intros v a xx t vxx.
  assert (v root) as vroot.
  apply (all_trees_rooted v a).
  apply t.
  assert (t2:=t).
  apply Tree_isa_connected in t2.
  assert (vxx2:=vxx).
  apply (Connected_path v a t2 root xx) in vxx.
  destruct vxx.
  destruct s.
  exists x.
  exists x0.
  exists p.
  unfold distance2.
  intros vl el p2.
  assert (vl = x /\ el = x0).
  apply (Tree_only_one_path v a root xx t).
  apply p2.
  apply p.
  destruct H.
  rewrite H0.
  reflexivity.
  apply vroot.
Qed.

Lemma Connected_path :
 forall (v : V_set) (a : A_set) (g : Connected v a) (x y : Vertex),
 v x -> v y -> {vl : V_list &  {el : E_list &  Path v a x y vl el}}.
Proof.
        intros; elim (Connected_walk v a g x y H H0); intros.
        elim p; intros.
        apply (Walk_to_path v a x y x0 x1 p0).
Qed.


Axiom distance_means_walk2 : forall (v: V_set) (a: A_set) (vl : V_list) (el : E_list) (x root: Component) (t : Tree v a),
 v root -> v x -> {p : Path v a x root vl el &  distance2 v a x root (length el)}.

Axiom distance_means_walk2' : forall (v: V_set) (a: A_set) (vl : V_list) (el : E_list) (x root: Component) (t : Tree v a),
 v root -> v x -> {p : Path v a root x vl el & distance2 v a root x (length el)}.


(* Lemma W_endy_endyel : forall (v: V_set) (a: A_set) (vl : V_list) (el: E_list) (x y : Component) (w : Walk v a x y vl el),
  vl <> nil -> Walk v a x y (rev (y :: nil ++ cdr(rev(x :: vl)))) el.
Proof.
  intros.
  apply Walk_reverse in w.
  apply Walk_reverse in w.
  simpl in w.
  destruct vl.
  intuition.
  simpl in w.
  rewrite rev_app_distr in w. *)



(* Lemma distance_means_walk2'' : forall (v: V_set) (a: A_set) (vl : V_list) (el : E_list) (x : Component) (t : Tree v a) (n : nat),
  v x -> {p : Walk v a root x vl el & length el = distance x}.
Proof.
  intros.
  apply (distance_means_walk2 v0 a0 (cdr (rev (root :: vl))) (E_reverse el) x0 t) in H.
(* Walk v a x y vl el -> Walk v  a  (cdr (rev (x :: vl))) (E_reverse el) *)
  destruct H.
  apply Walk_reverse in x1.

  
  simpl in x1.
  assert (E_reverse (E_reverse el) = el).
  admit.
  rewrite H in x1.

  destruct vl.
  simpl in x1.
  exists x1.
  assert (length (E_reverse el) = length el).
  admit.
  rewrite H0 in e.
  apply e.

  simpl in x1.
  rewrite <- rev_app_distr in x1.

  assert (vl = vl ++ x0 :: nil).
  admit.
  rewrite H0 in x1.
  rewrite rev_app_distr in x1.
  simpl in x1. 
  rewrite rev_app_distr in x1.
  simpl in x1.
  rewrite rev_involutive in x1.
  symmetry in H0.
  rewrite H0 in x1.
  
  exists x1.
  admit.
  simpl in x1.
Admitted. *)

End Help.