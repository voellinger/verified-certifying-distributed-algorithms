Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.
Require Import Coq.Logic.Classical_Prop.
Require Export Coq.Bool.BoolEq.


Section Topology.

Notation "a =/= b" := (beq_nat (Some a) (Some b)) (at level 70).
Notation "a == b" := (beq_nat a b) (at level 70).

(* representation of network *)

Definition Component := Vertex.


Definition component_index (c : Component):nat := match c with
                          | index x => x
                          end.

Definition C_set := U_set Component.

Definition C_list := U_list Component.

Definition C_nil:= V_nil.

Lemma C_eq_dec : forall x y : Component, {x = y} + {x <> y}.
Proof.
        simple destruct x; simple destruct y; intros.
        case (eq_nat_dec n n0); intros.
        left; rewrite e; trivial.
        right; injection; trivial.
Qed.



Fixpoint CA_list (v : V_set) (a : A_set) (c : Connected v a) {struct c} :
 A_list :=
  match c with
  | C_isolated x => A_nil
  | C_leaf v' a' c' x y _ _ => A_ends x y :: A_ends y x :: CA_list v' a' c'
  | C_edge v' a' c' x y _ _ _ _ _ =>
      A_ends x y :: A_ends y x :: CA_list v' a' c'
  | C_eq v' _ a' _ _ _ c' => CA_list v' a' c'
  end.

Fixpoint CV_list (v : V_set) (a : A_set) (c: Connected v a) {struct c} :
 V_list :=
  match c with
  | C_isolated x => x::V_nil
  | C_leaf v' a' c' x y _ _ => y :: CV_list v' a' c'
  | C_edge v' a' c' x y _ _ _ _ _  => CV_list v' a' c'
  | C_eq v' _ a' _ _ _ c' => CV_list v' a' c'
  end.

(* das habe ich als Axiom

Variable Component_prop: forall (c:Component)(v : V_set) (a : A_set)(g : Connected v a),
In c (CV_list v a g). *)

Lemma C_non_directed :forall (v : V_set) (a : A_set) (g : Connected v a) (x y : Vertex),
 a (A_ends x y) -> a (A_ends y x).
Proof.
intros.
apply Connected_Isa_Graph in g.
apply G_non_directed with (v:=v).
apply g.
apply H.
Qed.


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

Definition beq_comp (n m : Component) : bool :=
beq_nat (component_index n) (component_index m). 


(*Variable beq : Component -> Component -> bool.*)
(* Basic properties for beq: maybe these arent used
Variable beq_refl : forall x:Component, true = beq x x.

Variable beq_eq : forall x y:Component, true = beq x y -> x = y.

Variable beq_eq_true : forall x y:Component, x = y -> true = beq x y.

Variable beq_eq_not_false : forall x y:Component, x = y -> false <> beq x y.

Variable beq_false_not_eq : forall x y:Component, false = beq x y -> x <> y.

Variable exists_beq_eq : forall x y:Component, {b : bool | b = beq x y}.

Variable not_eq_false_beq : forall x y:Component, x <> y -> false = beq x y.

Variable eq_dec : forall x y:Component, {x = y} + {x <> y}. *)

Fixpoint In_bool (a: Component) (l:C_list) : bool:=
  match l with
  | nil => false
  | b :: m => beq_comp b a || In_bool a m
  end.

Definition neighbors (v : V_set) (a : A_set)(g : Connected v a) (c: Component) : C_list :=
(A_in_neighborhood c (CA_list v a g)).

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


(* list contains only one kind of component: c *)
Fixpoint forallb_neighbors (l:C_list) (c:Component) : bool :=
      match l with
        | nil => true
        | a::k => beq_comp a c && forallb_neighbors k c
      end.


Lemma forallb_forall_ : forall (l:C_list) (c:Component), 
(forallb_neighbors l c = true) <-> (forall x, In x l ->  x = c).
Proof.
  split; intros.
{ induction l.
  - inversion H0.
  - simpl in H.
    apply andb_prop in H.
    destruct H.
    unfold beq_comp in H.
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
    unfold beq_comp.
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

Lemma  arc_list_set: forall (v: V_set)(a: A_set)(g: Connected v a) (x y : Component),
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

Lemma arc_list_neighbors:
forall (v: V_set)(a: A_set)(g: Connected v a)x y,
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

Lemma neighbourslist_prep:
forall (v: V_set)(a: A_set)(g: Connected v a)(x comp1 comp2: Component),
a (A_ends comp1 x) -> In comp1 (neighbors v a g x).
Proof.
unfold neighbors.
intros.
apply (arc_list_set v a g) in H.
apply arc_list_neighbors in H. 
unfold neighbors in H.
trivial.
Qed.



Lemma neighbourslist2:
forall (v: V_set)(a: A_set)(g: Connected v a)(x comp1 comp2: Component)  (el : E_list) (clist: list Component),
 Path v a comp1 comp2 (x::clist) el -> In comp1  (neighbors v a g x).
Proof.
intros.
apply neighbourslist_prep.
apply x.
inversion H.
trivial.
Qed.



Fixpoint remove (x : Component) (l : list Component) : list Component :=
    match l with
    | nil => nil
    | y::tl => if ((component_index x) == (component_index y)) then tl else y::(remove x tl)
    end.

Definition empty (l : list Component) : bool :=
  match l with
  | nil => true
  | a :: m => false
  end.

End Topology.