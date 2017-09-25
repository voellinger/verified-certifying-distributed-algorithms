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
  admit.
  admit. (* n1 *)
  apply IHp.
  apply neq_symm.
  apply app_cons_not_nil.
Admitted.
  


  apply (Path_append2 v a z y x).
  
  intros.
  (* Path v a y z vl el -> (vl = V_nil \/ vl = vl' :: z :: nil) *)
  unfold not.
  intros.
  unfold In in H0.
  destruct H0.
    rewrite <- H0 in H.
    clear H0. clear c.
    assert (x = z) as H0.
    admit.
    rewrite <- H0 in IHp.
    rewrite <- H0 in p.
    inversion IHp.
    apply n in H3.
    assert (vl = V_nil). (* H0 *)
    admit.
    inversion p.
    symmetry in H9.
    apply n in H9.
    inversion H9.
  
(*     destruct vl.
      simpl in H.
      inversion H.

      rewrite cdr_app in H.
      apply in_app_or in H.
      destruct H.
        rewrite <- H0 in H.
        clear H0. clear c.
        admit.

        simpl in H.
        destruct H.
          rewrite <- H in H0.
          apply n in H0.
          inversion H0.

          inversion H.
      simpl.
      unfold not.
      intros.
      symmetry in H1.
      unfold V_nil in H1.
      apply app_cons_not_nil in H1.
      inversion H1. *)

    inversion H0.



  intros.
  assert (E_eq u' u -> E_eq u u').
  intros.
  inversion H1.
  apply E_refl.
  apply E_rev.
  unfold not.
  intros.
  apply H1 in H2.
  unfold not in n1. 
  assert (In u (E_reverse el) -> In u el).
  admit.
  apply H3 in H.
  apply n1 in H.
  inversion H.
  unfold In in H0.
  destruct H0.
  rewrite <- H0 in H2.
  inversion H2.
  apply E_rev.
  apply E_refl.
  inversion H0.

  intros.
  rewrite H in p.
  inversion p.
  simpl.
  reflexivity.
  assert (vl <> nil).
  rewrite <- H9.
  unfold not.
  intros.
  symmetry in H11.
  apply nil_cons in H11.
  inversion H11. 
  fold V_nil in H11.
  apply (P_iny_vl v a y y vl el p) in H11.
  apply n0 in H11.
  inversion H11.

  apply IHp.
  
  apply P_step.
  apply P_null.
  apply v0.
  apply P_endx_inv in p.
  apply p.
  apply (G_non_directed v a g) in a0.
  apply a0.
  auto.
  auto.
  intros.
  inversion H.
  intros.
  inversion H.

  intros.
  inversion H.
  symmetry.
  apply H0.
  inversion H0.

  unfold not.
  intros.
  symmetry in H.
  apply app_cons_not_nil in H.
  inversion H.
Admitted.

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
Lemma Tree_only_one_path : forall (v:V_set) (a:A_set) (x y : Component) (t : Tree v a) (vl vl' : V_list) (el el' : E_list)
  (p1 : Path v a x y vl el) (p2 : Path v a x y vl' el'),
  v x -> v y -> (vl = vl' /\ el = el').
Proof.
  intros v a x y t vl vl' el el' p1 p2 vx vy.
  assert (p1':= p1). assert (p2':= p2).
  assert (p3: Path v a x x (vl ++ (cdr (rev (x :: vl')))) (el ++ (E_reverse el'))).
  apply (Path_append2 v a x y x).
  apply p1.
  apply (Path_reverse ) in p2.
  apply p2.


  apply (Path_reverse ) in p1'.
  assert (p3': Path v a y y ((cdr (rev (x :: vl))) ++ vl') ((E_reverse el) ++ el')).
  apply (Path_append2 v a y x y).
  apply p1'.
  apply p2'.

  apply (Tree_isa_acyclic ) in t.
(*   rewrite Cycle in p3.
  apply (Acyclic_no_cycle v a t x x (vl ++ cdr (rev (x :: vl'))) (el ++ E_reverse el')) in p3.


Definition Cycle (x y : Vertex) (vl : V_list) (el : E_list)
  (p : Path x y vl el) := x = y.


Lemma Acyclic_no_cycle :
 forall (v : V_set) (a : A_set) (Ac : Acyclic v a) 
   (x y : Vertex) (vl : V_list) (el : E_list) (p : Path v a x y vl el),
 Cycle v a x y vl el p -> vl = V_nil.

  apply (Tree_isa_graph ) in t.
  apply t. *)
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
  apply vroot.
  apply vxx2.
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