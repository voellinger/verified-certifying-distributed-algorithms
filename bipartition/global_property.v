Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.Even.

Section Test.

Variable v : V_set.
Variable a : A_set.


Lemma s_is_plus_one : forall n:nat, S n = n + 1.
Proof.
  intros.
  rewrite (Nat.add_comm n 1).
  reflexivity.
Qed.

Lemma list_length_geq_0: forall (l : list Type), length l >= 0.
Proof.
  intros.
  induction l.
  unfold length.
  auto.
  unfold length.
  auto.
Qed.


Lemma S_0: forall (n : nat), S(n) > 0.
Proof.
  intros.
  unfold gt.
  induction n.
  unfold lt.
  apply le_n.
  unfold lt.
  apply le_S in IHn.
  apply IHn.
Qed.


Definition OddCycle (x y : Vertex) (vl : V_list) (el : E_list) (p : Path v a x y vl el)
 := Cycle v a x y vl el p /\ odd (length vl).


Lemma oddcycle_geq_1: forall (x y : Vertex) (vl : V_list) (el : E_list) (p : Path v a x y vl el) 
(c: Cycle v a x y vl el p), OddCycle x y vl el p -> length vl > 0.
Proof.
  intros.
  unfold OddCycle in H.
  destruct H.
  destruct vl as [nil|v1].
  inversion H0.
  unfold length.
  apply S_0.
Qed.


Lemma Extra_edge_still_path:
forall (x y a1 a2: Vertex) (v : V_set) (a : A_set) (vl : V_list) (el : E_list), 
Path v a x y vl el ->
{vl0 : V_list & { el0 : E_list & Path v (A_union a (A_single (A_ends a1 a2))) x y vl0 el0}}.
Proof.
  intros.
  (*let vl0 := vl.*)
Admitted. 




Lemma Extra_edge_in_tree_makes_cycle1: 
forall (x y z: Vertex) (t : Tree v a),
v x -> v y -> x <> y -> ~ a (A_ends y x) ->  (* |v| >= 3 *)
(exists (vl: V_list) (el: E_list), Path v (A_union a (A_single (A_ends x y))) z x (y :: vl) (E_ends x y :: el) -> z = x).
Proof.
  intros.
  assert ({vl : V_list &  {el : E_list &  Path v a y x vl el}}).
  apply Tree_isa_connected in t.
  apply (Connected_path v a t y x).
  apply H0.
  apply H.
  
  destruct H3.
  destruct s.
  exists x0.
  exists x1.

  intros.
  destruct H3.
  reflexivity.
  apply e.
  

Lemma Extra_edge_in_tree_makes_cycle2: 
forall (v : V_set) (a : A_set) (t : Tree v a) (x y: Vertex) (vl: V_list) (el: E_list) 
(p : Path v (A_union a (A_single (A_ends x y))) x x (y :: vl) (E_ends x y :: el)),

v x -> v y -> x <> y -> ~ a (A_ends x y) ->  (* |v| >= 3 *)
Cycle v (A_union a (A_single (A_ends x y))) x x (y :: vl) (E_ends x y :: el) p.
Proof.
  intros.
  unfold Cycle.
  reflexivity.
Qed.






(* Variable g : Graph v a.
Lemma Path_degree_zero_nil :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Path v a x y vl el ->
 (exists2 z : Vertex, In z (x :: vl) & degree z v a g = 0) -> vl = V_nil. *)


Lemma Extra_edge_in_tree_makes_cycle: 
forall (v : V_set) (a : A_set) (t : Tree v a) (x y: Vertex) (vl: V_list) (el: E_list),
v x -> v y -> x <> y -> ~ a (A_ends x y) ->  (* |v| >= 3 *) Path v a x y vl el ->

 Cycle v (A_union a (A_single (A_ends x y))) x x (y :: vl) (E_ends x y :: el)
 (Path v (A_union a (A_single (A_ends x y))) x x (y :: vl) (E_ends x y :: el)).
Proof.
  intros.
  (* 1. show that there is a path from x to y
     2. append the new edge to the path from 1 to get a path from x to x
     3. the path of 2 is a cycle
  *)

  (* Show that there is a path p between x and y in the current tree. *)
  assert ({vl : V_list &  {el : E_list &  Path v0 a0 y x vl el}}).
  apply Tree_isa_connected in H3.
  apply (Connected_path v0 a0 c y x).
  apply H0.
  apply H.
  
  destruct H6.
  destruct s.


  (* append edge to path p *)

Qed.



Definition Cycle (x y : Vertex) (vl : V_list) (el : E_list)
  (p : Path x y vl el) := x = y.



Lemma Connected_path :
 forall (v : V_set) (a : A_set) (g : Connected v a) (x y : Vertex),
 v x -> v y -> {vl : V_list &  {el : E_list &  Path v a x y vl el}}.



Lemma Walk_reverse :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Walk v a x y vl el -> Walk v a y x (cdr (rev (x :: vl))) (E_reverse el).






Lemma Walk_to_path :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Walk v a x y vl el ->
 {vl0 : V_list &  {el0 : E_list &  Path v a x y vl0 el0}}.
Proof.
        intros x y vl el w; elim w; intros.
        split with V_nil; split with E_nil. apply P_null;








Inductive Path : Vertex -> Vertex -> V_list -> E_list -> Set :=
  | P_null : forall x : Vertex, v x -> Path x x V_nil E_nil
  | P_step :
      forall (x y z : Vertex) (vl : V_list) (el : E_list),
      Path y z vl el ->
      v x ->
      a (A_ends x y) ->
      x <> y ->
      ~ In y vl ->
      (In x vl -> x = z) ->
      (forall u : Edge, In u el -> ~ E_eq u (E_ends x y)) ->
      Path x z (y :: vl) (E_ends x y :: el).


Definition Cycle (x y : Vertex) (vl : V_list) (el : E_list)
  (p : Path x y vl el) := x = y.



Lemma one_in_list_one_not_unequal:
forall (el : E_list) (e f : Edge),

In e el -> ~ In f el -> ~ E_eq e f.
Proof.
  intros.
  induction el.
  inversion H.
  
  unfold In in H.
  inversion H.








Lemma Extra_edge_in_tree_makes_cycle: 
forall (v : V_set) (a : A_set) (t : Tree v a) (x y: Vertex),

v x -> v y -> x <> y -> ~ a (A_ends x y) ->  (* |v| >= 3 *)
{vl: V_list & {el: E_list & Path v (A_union a (A_single (A_ends x y))) x x (y :: vl) (E_ends x y :: el)}}.




Lemma Extra_edge_in_tree_makes_cycle: 
forall (c : Connected v a) (x y: Vertex) (v : V_set) (a : A_set) (vl : V_list) (el : E_list),

v x -> v y -> ~ a (A_ends x y) -> x <> y -> Tree v a -> ~ In y vl -> (forall u : Edge, In u el -> ~ E_eq u (E_ends x y))
  -> Path v (A_union a (A_single (A_ends x y))) x x (y :: vl) (E_ends x y :: el).
Proof.
  intros.
  (* 1. show that there is a path from x to y
     2. append the new edge to the path from 1 to get a path from x to x
     3. the path of 2 is a cycle
  *)

  (* Show that there is a path p between x and y in the current tree. *)
  assert ({vl : V_list &  {el : E_list &  Path v0 a0 y x vl el}}).
  apply Tree_isa_connected in H3.
  apply (Connected_path v0 a0 c y x).
  apply H0.
  apply H.
  
  destruct H6.
  destruct s.


  (* append edge to path p *)
  apply (P_step v0 (A_union a0 (A_single (A_ends x y))) x y x vl el).
  apply (Extra_edge_still_path y x x y v0 a0 vl el).
  apply p.
  apply H.
  unfold A_union.
  apply In_right.
  apply In_single.
  apply H2.
  apply H4.
  trivial.
  apply H5.
Qed.
