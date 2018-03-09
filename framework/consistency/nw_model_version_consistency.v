Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.
Require Import Coq.Logic.Classical_Prop.
Require Export Coq.Bool.BoolEq.

Notation "a =/= b" := (beq_nat (Some a) (Some b)) (at level 70).
Notation "a == b" := (beq_nat a b) (at level 70).

(* representation of network *)

Definition Component := Vertex.


Definition Component_index (c : Component):nat := match c with
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



Variable a:A_set.
Variable v:C_set.
Variable g : Connected v a.
Variable root: Component.
Variable rootprop: v root.


Fixpoint CA_list (v : V_set) (a : A_set) (c : Connected v a) {struct c} :
 A_list :=
  match c with
  | C_isolated x => A_nil
  | C_leaf v' a' c' x y _ _ => CA_list v' a' c'
  | C_edge v' a' c' x y _ _ _ _ _ =>
      A_ends x y :: A_ends y x :: CA_list v' a' c'
  | C_eq v' _ a' _ _ _ c' => CA_list v' a' c'
  end.

Fixpoint CV_list (v : V_set) (a : A_set) (c: Connected v a) {struct c} :
 V_list :=
  match c with
  | C_isolated x => x::V_nil
  | C_leaf v' a' c' x y _ _ => x :: CV_list v' a' c'
  | C_edge v' a' c' x y _ _ _ _ _  => CV_list v' a' c'
  | C_eq v' _ a' _ _ _ c' => CV_list v' a' c'
  end.

Variable Component_prop: forall (c:Component),
In c (CV_list v a g).

Lemma C_non_directed :forall (v : V_set) (a : A_set) (g : Connected v a) (x y : Vertex),
 a (A_ends x y) -> a (A_ends y x).
Proof.
intros.
apply Connected_Isa_Graph in g0.
apply G_non_directed with (v:=v0).
apply g0.
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

Definition beq (n m : Component) : bool :=
beq_nat (Component_index n) (Component_index m). 


(*Variable beq : Component -> Component -> bool.*)

Variable beq_refl : forall x:Component, true = beq x x.

Variable beq_eq : forall x y:Component, true = beq x y -> x = y.

Variable beq_eq_true : forall x y:Component, x = y -> true = beq x y.

Variable beq_eq_not_false : forall x y:Component, x = y -> false <> beq x y.

Variable beq_false_not_eq : forall x y:Component, false = beq x y -> x <> y.

Variable exists_beq_eq : forall x y:Component, {b : bool | b = beq x y}.

Variable not_eq_false_beq : forall x y:Component, x <> y -> false = beq x y.

Variable eq_dec : forall x y:Component, {x = y} + {x <> y}.

Fixpoint In_bool (a: Component) (l:C_list) : bool:=
  match l with
  | nil => false
  | b :: m => beq b a || In_bool a m
  end.

Definition neighbors (g : Connected v a) (c: Component) : C_list :=
(A_in_neighborhood c (CA_list v a g)).


Axiom neighbors_connected_prop :
forall k (g : Connected v a) (c: Component),
In k ( A_out_neighborhood c (CA_list v a g)) <-> In k (A_in_neighborhood c (CA_list v a g)).


Axiom parent_neighbors_: forall (c:Component)(k:Component),
a (A_ends c k) <-> In k (A_in_neighborhood c (CA_list v a g)).



Fixpoint forallb_neigbors (l:C_list) (c:Component) : bool :=
      match l with
        | nil => true
        | a::k => beq a c && forallb_neigbors k c
      end.

Axiom forallb_forall_ : forall (l:C_list) (c:Component) (x:Component), 
(forallb_neigbors l c = true) <-> (In x l ->  x = c).

Axiom  arc_list_set:
forall x y,
a (A_ends x y ) -> In (A_ends x y ) (CA_list v a g).


Lemma arc_list_neighbors:
forall x y,
In (A_ends x y ) (CA_list v a g) -> In x (neighbors g y ).
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
forall (x comp1 comp2: Component),
a (A_ends comp1 x)-> In comp1  (neighbors g x).
Proof.
unfold neighbors.
intros.
apply arc_list_set in H.
apply arc_list_neighbors in H. 
unfold neighbors in H.
trivial.
Qed.



Lemma neighbourslist2:
forall (x comp1 comp2: Component)  (el : E_list) (clist: list Component),
 Path v a comp1 comp2 (x::clist) el -> In comp1  (neighbors g x ).
Proof.
intros.
apply neighbourslist_prep.
apply x.
inversion H.
trivial.
Qed.

