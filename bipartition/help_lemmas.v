Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.Even.

(* Load "/home/lanpirot/Uni/COQ/verified-certifying-distributed-algorithms/leader-election/composition_witness_prop_leader_election". *)


Section Help.

Definition Component := Vertex.



Variable x y z: Component.
Variable distance : Component -> nat.

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



Definition append_w (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (w1: Walk v a x y vl el) (w2: Walk v a y z vl' el') :=
  Walk v a x z (vl ++ vl') (el ++ el').

Definition append_p (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (p1: Path v a x y vl el) (p2: Path v a y z vl' el') :=
  Walk v a x z (vl ++ vl') (el ++ el').

Lemma Path_append (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (p1: Path v a x y vl el) (p2: Path v a y z vl' el'):
 Walk v a x z (vl ++ vl') (el ++ el') = append_p v a vl vl' el el' p1 p2.
Proof.
  intros.
  unfold append_p.
  reflexivity.
Qed.

Function length_w {v: V_set} {a: A_set} {vl : V_list} {el: E_list} {c1 c2: Component} (p: Walk v a c1 c2 vl el) := length vl.
Function length_p {v: V_set} {a: A_set} {vl : V_list} {el: E_list} {c1 c2: Component} (p: Path v a c1 c2 vl el) := length vl.
(* Function distance {v: V_set} {a: A_set} (c: Component) := minimum length of all sets of Walks from c to root*)


Lemma Path_append_lengthsum (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (p1: Path v a x y vl el) (p2: Path v a y z vl' el') (p3: append_p v a vl vl' el el' p1 p2):
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
  exists x0.
  unfold V_single.
  intuition.

  exists x0.
  apply V_in_right.
  apply v0.
  

  exists x0.
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
  apply (nearly_all_trees_rooted v a x0 t).
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

Lemma Tree_only_one_path : forall (v:V_set) (a:A_set) (x y : Component) (t : Tree v a) (vl vl' : V_list) (el el' : E_list)
  (p1 : Path v a x y vl el) (p2 : Path v a x y vl' el'),
  v x -> v y -> (vl = vl' /\ el = el').
Proof.
Admitted.

Axiom connected_min_path: forall (v: V_set) (a: A_set) (x root: Component) (t : Tree v a),
 v root -> {vl : V_list &  {el : E_list &  {p : Path v a root x vl el & length el = distance x}}}.

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
  exists x0.
  exists x1.
  exists p.
  unfold distance2.
  intros vl el p2.
  assert (vl = x0 /\ el = x1).
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
 v root -> v x -> {p : Path v a x root vl el & length el = distance x}.

Axiom distance_means_walk2' : forall (v: V_set) (a: A_set) (vl : V_list) (el : E_list) (x root: Component) (t : Tree v a),
 v root -> v x -> {p : Path v a root x vl el & length el = distance x}.


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




(* 

  maybe rewrite Samira's stuff like this ... ??

  Inductive Component: Vertex -> Set :=
  | root  : forall x : Vertex, v x -> Component x
  | other : forall x : Vertex, v x -> Component x.



  Definition leader : (c : Component) := parent c = c.
  Function distance : (c : Component) :=


*)


(* 

Variable g : Connected v a.
Variable root: Component.



Variable leader :Component -> Component.
Variable parent : Component -> Component.
Variable distance : Component -> nat. *)

End Help.