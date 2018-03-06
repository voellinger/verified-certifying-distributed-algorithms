Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.
Require Import Coq.Logic.Classical_Prop.
Require Export Coq.Bool.BoolEq.


(* part of the network model that represents the underlying network graph *)
(* we model the topology of a network as a connected undirected graph *)
Section Topology.

Notation "a =/= b" := (beq_nat (Some a) (Some b)) (at level 70).
Notation "a == b" := (beq_nat a b) (at level 70).


(* a component is modelled as a vertex (of a graph) *)
Definition Component := Vertex.

(* each component has a unique identifier *)
Definition component_index (c : Component):nat := match c with
                          | index x => x
                          end.

(* from vertices to components *)
(* our universe is a set of components *)
Definition C_set := U_set Component.
Definition C_list := U_list Component.
Definition C_nil:= V_nil.

(* it is decidable whether two components x,y are the same or different *)
Lemma C_eq_dec : forall x y : Component, {x = y} + {x <> y}.
Proof.
        simple destruct x; simple destruct y; intros.
        case (eq_nat_dec n n0); intros.
        left; rewrite e; trivial.
        right; injection; trivial.
Qed.

(* CA_list is a list of the set of arcs a *)
(* we match over the constructors of the connected graph c *)
Fixpoint CA_list (v : V_set) (a : A_set) (c : Connected v a) {struct c} :
 A_list :=
  match c with
  | C_isolated x => A_nil
  | C_leaf v' a' c' x y _ _ => A_ends x y :: A_ends y x :: CA_list v' a' c'
  | C_edge v' a' c' x y _ _ _ _ _ =>
      A_ends x y :: A_ends y x :: CA_list v' a' c'
  | C_eq v' _ a' _ _ _ c' => CA_list v' a' c'
  end.

(* CV_list is a list of the set vertices v *)
Fixpoint CV_list (v : V_set) (a : A_set) (c: Connected v a) {struct c} :
 V_list :=
  match c with
  | C_isolated x => x::V_nil
  | C_leaf v' a' c' x y _ _ => y :: CV_list v' a' c'
  | C_edge v' a' c' x y _ _ _ _ _  => CV_list v' a' c'
  | C_eq v' _ a' _ _ _ c' => CV_list v' a' c'
  end.

(* necessary as an Axiom?
Variable Component_prop: forall (c:Component)(v : V_set) (a : A_set)(g : Connected v a),
In c (CV_list v a g). *)

(* connected graph is symmetric and thereby represents an undirected graph *)
Lemma C_non_directed: forall (v : V_set) (a : A_set) (c : Connected v a) (x y : Vertex),
 a (A_ends x y) -> a (A_ends y x).
Proof.
intros.
apply Connected_Isa_Graph in c.
apply G_non_directed with (v:=v).
apply c.
apply H.
Qed.

(**)
Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

(* true iff components n and m are equal *)
Definition beq (n m : Component) : bool :=
beq_nat (component_index n) (component_index m). 


(* Basic properties for beq: maybe these arent used*)
(*
(* alternatively to the definition of beq *)
Variable beq : Component -> Component -> bool.
Variable beq_refl : forall x:Component, true = beq x x.

Variable beq_eq : forall x y:Component, true = beq x y -> x = y.

Variable beq_eq_true : forall x y:Component, x = y -> true = beq x y.

Variable beq_eq_not_false : forall x y:Component, x = y -> false <> beq x y.

Variable beq_false_not_eq : forall x y:Component, false = beq x y -> x <> y.

Variable exists_beq_eq : forall x y:Component, {b : bool | b = beq x y}.

Variable not_eq_false_beq : forall x y:Component, x <> y -> false = beq x y.

Variable eq_dec : forall x y:Component, {x = y} + {x <> y}. 
*)

(* true iff component a is in list l *)
Fixpoint In_bool (a: Component) (l:C_list) : bool:=
  match l with
  | nil => false
  | b :: m => beq b a || In_bool a m
  end.

(* list of neighbors of component c *)
Definition neighbors (v : V_set) (a : A_set) (g : Connected v a) (c: Component) : C_list :=
(A_in_neighborhood c (CA_list v a g)).

(* since the graph is symmetric, the in- and out-neighborhood is the same*)
Lemma neighbors_connected_prop :
forall k (v : V_set) (a : A_set)(g : Connected v a) (c: Component),
 In k (A_out_neighborhood c (CA_list v a g)) <-> In k (A_in_neighborhood c (CA_list v a g)).
Proof.
  split.
{ intros.
  induction g.
  - auto.
  - simpl in *.
    destruct (V_eq_dec c y).
    destruct (V_eq_dec c x).
    simpl in *.
    repeat destruct H; auto.
    simpl in *; auto.
    repeat destruct H; auto.
    destruct (V_eq_dec c x).
    simpl in *; auto.
    repeat destruct H; auto.
    apply (IHg H).
  - simpl in *.
    destruct (V_eq_dec c y).
    destruct (V_eq_dec c x).
    simpl.
    simpl in H.
    destruct H.
    right.
    left.
    apply H.
    destruct H.
    left.
    apply H.
    apply IHg in H.
    right.
    right.
    apply H.

    simpl in *.
    destruct H.
    left. apply H.
    right. apply (IHg H).

    destruct (V_eq_dec c x).
    simpl in *.
    destruct H.
    left. apply H.
    right. apply (IHg H).
    apply (IHg H).
  - rewrite <- e.
    rewrite <- e0.
    apply (IHg H). }

{ intros.
  induction g.
  - auto.
  - simpl in *.
    destruct (V_eq_dec c x).
    destruct (V_eq_dec c y).
    simpl in *.
    repeat destruct H; auto.
    simpl in *.
    repeat destruct H; auto.
    destruct (V_eq_dec c y).
    simpl in *.
    repeat destruct H; auto.
    apply (IHg H).
  - simpl in *.
    destruct (V_eq_dec c x).
    destruct (V_eq_dec c y).
    simpl in *.
    repeat destruct H; auto.
    simpl in *.
    repeat destruct H; auto.
    destruct (V_eq_dec c y).
    simpl in *.
    repeat destruct H; auto.
    apply (IHg H).
  - rewrite <- e.
    rewrite <- e0.
    apply (IHg H). }
Qed.

(* for a parent k of c holds that k is also a neighbor of c *)
Lemma parent_neighbors_: forall (v: V_set) (a: A_set)(g: Connected v a) (c k:Component),
a (A_ends c k) <-> In k (A_in_neighborhood c (CA_list v a g)).
Proof.
  split; intros.
{ induction g.
  - auto.
    inversion H.
  - simpl in *.
    destruct (V_eq_dec c y).
    destruct (V_eq_dec c x).
    simpl in *.
    inversion H.
    inversion H0.
    right. left. reflexivity.
    left. reflexivity.
    right. right. apply (IHg H0).
    simpl in *.
    inversion H.
    inversion H0.
    symmetry in H3. intuition.
    left. auto.
    right. apply (IHg H0).
    destruct (V_eq_dec c x).
    simpl in *.
    inversion H.
    inversion H0.
    left. reflexivity.
    symmetry in H3. intuition.
    right. apply (IHg H0).
    inversion H.
    inversion H0; symmetry in H3; intuition.
    apply (IHg H0).
  - simpl in *.
    destruct (V_eq_dec c y).
    destruct (V_eq_dec c x).
    simpl in *.
    inversion H.
    inversion H0.
    right. left. reflexivity.
    left. reflexivity.
    right. right. apply (IHg H0).
    simpl in *.
    inversion H.
    inversion H0.
    symmetry in H3. intuition.
    left. auto.
    right. apply (IHg H0).
    destruct (V_eq_dec c x).
    simpl in *.
    inversion H.
    inversion H0.
    left. reflexivity.
    symmetry in H3. intuition.
    right. apply (IHg H0).
    inversion H.
    inversion H0; symmetry in H3; intuition.
    apply (IHg H0).
  - rewrite <- e.
    rewrite <- e0.
    rewrite <- e0 in H.
    simpl.
    apply (IHg H). }
{ induction g.
  - auto.
    inversion H.
  - simpl in *.
    destruct (V_eq_dec c y).
    destruct (V_eq_dec c x).
    rewrite e in *. rewrite e0 in *.
    apply n in v0. intuition.
    rewrite e in *. simpl in *.
    destruct H. apply In_left. rewrite H in *. apply E_left.
    apply In_right. apply (IHg H).
    destruct (V_eq_dec c x).
    simpl in *; destruct H; auto.
    rewrite e in *; rewrite H in *.
    apply In_left. apply E_right.
    apply In_right. apply (IHg H).
    apply In_right. apply (IHg H).
  - simpl in *.
    destruct (V_eq_dec c y).
    destruct (V_eq_dec c x).
    rewrite e in *. rewrite e0 in *.
    intuition.
    rewrite e in *. simpl in *.
    destruct H. apply In_left. rewrite H in *. apply E_left.
    apply In_right. apply (IHg H).
    destruct (V_eq_dec c x).
    simpl in *; destruct H; auto.
    rewrite e in *; rewrite H in *.
    apply In_left. apply E_right.
    apply In_right. apply (IHg H).
    apply In_right. apply (IHg H).
  - rewrite <- e in *.
    rewrite <- e0 in *.
    simpl in *.
    apply (IHg H). }
Qed.


(* true iff list l contains (multiple times) only component c *)
Fixpoint forallb_neighbors (l:C_list) (c:Component) : bool :=
      match l with
        | nil => true
        | a::k => beq a c && forallb_neighbors k c
      end.

(*  *)
Lemma forallb_forall_ : forall (l:C_list) (c:Component), 
(forallb_neighbors l c = true) <-> (forall x, In x l ->  x = c).
Proof.
  split; intros.
{ induction l.
  - inversion H0.
  - simpl in H.
    apply andb_prop in H.
    destruct H.
    unfold beq in H.
    apply Nat.eqb_eq in H.
    destruct (a).
    destruct (c).
    unfold component_index in H.
    simpl in H0.
    destruct H0.
    rewrite <- H. rewrite <- H0. reflexivity.
    apply (IHl H1 H0). }
{ induction l.
  - reflexivity.
  - intuition.
    simpl. apply andb_true_intro.
    split.
    symmetry. apply beq_eq_true.
    simpl in H. intuition.
    destruct x.
    unfold beq.
    simpl.
    symmetry.
    apply <- Nat.eqb_eq.
    reflexivity.
    specialize (H a).
    apply H.
    simpl.
    left.
    reflexivity.
    apply IHl.
    intros.
    apply H.
    simpl. right. apply H0. }
Qed.

(* if an arc is in the arc set a, then it is also in the arc list CA_list *)
Lemma arc_list_set: forall (v: V_set)(a: A_set)(g: Connected v a) (x y : Component),
a (A_ends x y) -> In (A_ends x y) (CA_list v a g).
Proof.
  intros.
  induction g.
  - inversion H.
  - simpl in *.
    inversion H.
    inversion H0.
    auto.
    auto.
    right. right. apply (IHg H0).
  - simpl in *.
    inversion H.
    inversion H0 ; auto.
    right. right. apply (IHg H0).
  - rewrite <- e in *. rewrite <- e0 in *.
    apply (IHg H).
Qed.

(* if there is an arc from y to x in the list CA_list, then x is a neighbor of y *)
Lemma arc_list_neighbors:
forall (v: V_set)(a: A_set)(g: Connected v a) x y,
In (A_ends x y) (CA_list v a g) -> In x (neighbors v a g y).
Proof.
intros.
unfold neighbors.
unfold A_in_neighborhood.
induction ( (CA_list v a g)).
contradiction.
destruct a0.
destruct (V_eq_dec y v1).
destruct H.
unfold In.
left.
inversion H.
destruct H.
trivial.
unfold In.
right.
unfold In in IHa0.
apply IHa0.
unfold In in H.
trivial.
destruct H.
inversion H.
rewrite H2 in n.
contradiction.
apply IHa0.
trivial.
Qed. 

(* if there is an arc from y to x in a, then comp1 is a neighbor of comp2 *)
Lemma neighbourslist_prep:
forall (v: V_set)(a: A_set)(g: Connected v a)(comp1 comp2: Component),
a (A_ends comp1 comp2) -> In comp1 (neighbors v a g comp2).
Proof.
unfold neighbors.
intros.
apply (arc_list_set v a g) in H.
apply arc_list_neighbors in H. 
unfold neighbors in H.
trivial.
Qed.

(* if there is a path from comp1 to comp2 with x being the first component on the path,
 * then comp1 is a neighbor of x *)
Lemma neighbourslist2:
forall (v: V_set)(a: A_set)(g: Connected v a)(x comp1 comp2: Component)  (el : E_list) (clist: list Component),
 Path v a comp1 comp2 (x::clist) el -> In comp1  (neighbors v a g x).
Proof.
intros.
apply neighbourslist_prep.
inversion H.
trivial.
Qed.

(* removes a component from a list of components *)
Fixpoint remove (x : Component) (l : list Component) : list Component :=
    match l with
    | nil => nil
    | y::tl => if ((component_index x) == (component_index y)) then tl else y::(remove x tl)
    end.

(* true iff a list of component is empty *)
Definition empty (l : list Component) : bool :=
  match l with
  | nil => true
  | a :: m => false
  end.

End Topology.