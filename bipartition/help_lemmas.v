Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.Even.

(* Load "/home/lanpirot/Uni/COQ/verified-certifying-distributed-algorithms/leader-election/composition_witness_prop_leader_election". *)


Section Help.

Definition Component := Vertex.
Definition c_index (c : Component):nat := match c with
                          | index x => x
                          end.



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




Axiom indices_diff : forall (c c' : Component), c <> c' -> c_index c <> c_index c'.

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

(* Inductive Connected : V_set -> A_set -> Set :=
  | C_isolated : forall x : Vertex, Connected (V_single x) A_empty *)


Definition is_root (v:V_set) (root : Component) := v root /\ forall (c:Component), v c -> c_index root <= c_index c.



(* only one of the two preconditions is needed*)
Lemma set_has_min : forall (s : U_set nat) (n' : nat), s n' -> s <> Empty nat -> {n : nat & s n /\ n <= n'}.
Proof.
  intros.
  exists n'.
  split.
  apply H.
  reflexivity.
Qed.




(* Axiom nearly_all_graphs_rooted: forall (v:C_set) (x : Component),
  v x -> (exists (root : Component), is_root root).

Fixpoint indify (v : V_set) : (s : U_set nat) :=
  match v with
  | Empty => Empty
  |  *)

(* Lemma nearly_all_graphs_rooted': forall (v:V_set) (x : Component) (g:Graph v a),
  v x -> (exists (root : Component), v root /\ is_root v root).
Proof.
  intros.
  unfold is_root.
  unfold V_set in v.
  unfold U_set in v.
  (* v0 is not empty ... minimum{index x | x in v0} exists ... take this minimum and show rest with it *)
Admitted. *)
Axiom nearly_all_graphs_rooted': forall (v:V_set) (a:A_set) (x : Component) (g:Graph v a),
  v x -> (exists (root : Component), v root /\ is_root v root).

Lemma nearly_all_trees_rooted: forall (v:V_set) (a:A_set) (x:Component) (t: Tree v a),
  v x -> (exists (root : Component), v root /\ is_root v root).
Proof.
  intros v a x0 t vx.
  apply Tree_isa_graph in t.
  apply (nearly_all_graphs_rooted' v a) in vx.
  apply vx.
  apply t.
Qed.

Lemma all_trees_rooted: forall (v:V_set) (a:A_set) (t: Tree v a),
  (exists (root : Component), v root /\ is_root v root).
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

(* Lemma ex_min : forall (v: V_set), exists (root2 : Component), v root2 -> forall (c : Component), v c -> index root2 <= index c.
Proof.
  intros. *)

(* Lemma nearly_all_trees_rooted2: forall (v:C_set) (a:A_set) (t: Tree v a) (x : Component),
  exists (x : Component), v x -> (exists (root: Component), v root /\ is_root root).
Proof.
  intros v0 a0 t x. exists x. intro v. unfold is_root. intros. rename x into root2. apply (ex_min c). *)

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



Axiom connected_min_path: forall (v: V_set) (a: A_set) (vl : V_list) (el : E_list) (x root: Component) (t : Tree v a),
 is_root v root -> {vl : V_list &  {el : E_list &  {p : Path v a root x vl el & length el = distance x}}}.

Axiom distance_means_walk2 : forall (v: V_set) (a: A_set) (vl : V_list) (el : E_list) (x root: Component) (t : Tree v a),
 is_root v root -> v x -> {p : Walk v a x root vl el & length el = distance x}.

Axiom distance_means_walk2' : forall (v: V_set) (a: A_set) (vl : V_list) (el : E_list) (x root: Component) (t : Tree v a),
 is_root v root -> v x -> {p : Walk v a root x vl el & length el = distance x}.


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