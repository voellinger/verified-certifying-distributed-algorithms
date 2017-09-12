Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.Even.

Load "/home/lanpirot/Uni/COQ/verified-certifying-distributed-algorithms/leader-election/composition_witness_prop_leader_election".
















Section Help.

Variable x y z: Component.
Variable root: Component.
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
        intros. elim H. intros. apply v1. intros. apply H0.
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

(* Lemma distance_means_walk : forall (v: V_set) (a: A_set) (vl : V_list) (el : E_list) (x : Component) (t : Tree v a) (n : nat) (w : Walk v a x root vl el),
  distance x = n -> length el = n.
Proof.
  intros.
  apply W_endx_inv in w.
  apply (path_to_root n x0 w) in H.

Lemma path_to_root:
forall (n:nat) (x:Component) (prop1 : v x),
distance x = n -> {el : A_list & Connection x root el n }.

  assert (forall (vl'' : V_list) (el'' :E_list) (w' : Walk v a x0 root vl'' el''),  length el'' = n).
  admit.
  apply (H0 vl el w).
  apply W_endx_inv in w.
  admit.
Qed. *)


Axiom root_prop: forall (v : V_set), v root.



(* Lemma Connected_min_path: forall (x : Component) (t : Tree v a) (n : nat),
  distance x = n -> {vl : V_list &  {el : E_list &  {p : Path v a root x vl el & length el = n}}}.
Proof.
  intros.
  induction n.
  exists V_nil.
  exists E_nil.
  apply distance_root_ in H.
  rewrite H.
  assert (Path v a root root V_nil E_nil).
  apply P_null.
  apply rootprop.
  exists H0.
  trivial.
Qed. *)



Axiom connected_min_path: forall (v: V_set) (a: A_set) (vl : V_list) (el : E_list) (x : Component) (t : Tree v a) (n : nat),
  {vl : V_list &  {el : E_list &  {p : Path v a root x vl el & length el = distance x}}}.

Axiom distance_means_walk2 : forall (v: V_set) (a: A_set) (vl : V_list) (el : E_list) (x : Component) (t : Tree v a) (n : nat) (vl : V_list) (el : E_list),
  v x -> {p : Walk v a x root vl el & length el = distance x}.

Axiom distance_means_walk2' : forall (v: V_set) (a: A_set) (vl : V_list) (el : E_list) (x : Component) (t : Tree v a) (n : nat) (vl : V_list) (el : E_list),
  v x -> {p : Walk v a root x vl el & length el = distance x}.



(* Axiom Component_Graph: forall (c:Component), v c. *)

(* Lemma distance_means_walk2' : forall (x : Component) (t : Tree v a) (n : nat) (vl : V_list) (el : E_list),
  v x -> {p : Walk v a root x vl el & length el = distance x}.
Proof.
  intros.
  apply (distance_means_walk2 x0 t n (cdr (rev (root :: vl0))) (E_reverse el0)) in H.
  destruct H.
  apply Walk_reverse in x1.

  destruct vl0.
  simpl in x1.
  assert (E_reverse (E_reverse el0) = el0).
  admit.
  rewrite H in x1.
  exists x1.
  admit.
  simpl in x1.
Admitted. *)

Lemma tree_walk : forall (v: C_set) (a : A_set) (t : Tree v a) (x y: Component),
  v x -> v y -> {vl : V_list & {el : E_list & Walk v a x y vl el}}.
Proof.
  intros.
  apply Tree_isa_connected in t.
  apply Connected_walk.
  apply t.
  apply H.
  apply H0.
Qed.


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