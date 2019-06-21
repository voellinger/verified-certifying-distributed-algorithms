Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.
Require Import Coq.Logic.Classical_Prop.

Load Bipartition_related.
Require Export Coq.Bool.BoolEq.


Section Checker.

Definition nldlist := list (Component * Component * nat).

(*CA_list: all arcs of a Connected-graph*)
Fixpoint CA_list (v : V_set) (a : A_set) (c : Connected v a) {struct c} : A_list :=
  match c with
  | C_isolated x => A_nil
  | C_leaf v' a' c' x y _ _ => A_ends x y :: A_ends y x :: CA_list v' a' c'
  | C_edge v' a' c' x y _ _ _ _ _ => A_ends x y :: A_ends y x :: CA_list v' a' c'
  | C_eq v' _ a' _ _ _ c' => CA_list v' a' c'
  end.

Fixpoint is_not_in (x : Component) (l : nldlist) : Prop :=
  match l with
  | nil => True
  | (y,z,n) :: tl => if V_eq_dec x y then False else is_not_in x tl
  end.

Fixpoint is_in_once (x : Component) (l : nldlist) : Prop :=
  match l with
  | nil => False
  | (y,z,n) :: tl => if V_eq_dec x y then is_not_in x tl else is_in_once x tl
  end.

Fixpoint get_distance_in_list (x : Component) (l : nldlist) : nat :=
  match l with
  | nil => 0
  | (y,z,n) :: tl => if V_eq_dec x y then n else get_distance_in_list x tl
  end.

Fixpoint get_leader_in_list (x : Component) (l : nldlist) : Component :=
  match l with
  | nil => x
  | (y,z,n) :: tl => if V_eq_dec x y then z else get_leader_in_list x tl
  end.

Fixpoint leader_same (x : Component) (l : nldlist) : bool :=
  match l with
  | nil => true
  | (c1, c2, n) :: tl => if (V_eq_dec x c2) then leader_same x tl else false
  end.

Function is_same (x : Component) (other : Component) : bool :=
  if V_eq_dec x other then true else false.

Fixpoint is_in (x : Component) (l : list Component) : bool :=
  match l with
  | nil => false
  | y :: tl => if V_eq_dec x y then true else is_in x tl
  end.

Definition Checker_tree (x : Component) (neigh_list : list Component) (leader parent : Component) (distance : nat) (nld : nldlist) : bool :=
  leader_same leader nld &&
  ((is_same x leader && is_same x parent && (distance =? 0)) ||
   (negb (is_same x leader) && (is_in parent neigh_list) &&
    Nat.eqb distance (get_distance_in_list parent nld + 1))).

Fixpoint Checker_local_bipartition (d : nat) (nld : nldlist) : bool :=
  match nld with
  | nil => true
  | (c1, c2, n) :: tl => if (eqb (Nat.odd d) (Nat.odd n)) then false else Checker_local_bipartition d tl
  end.

Fixpoint is_not_in_b (x : Component) (l : nldlist) : bool :=
  match l with
  | nil => true
  | (y,z,n) :: tl => if V_eq_dec x y then false else is_not_in_b x tl
  end.

Fixpoint is_in_once_b (x : Component) (l : nldlist) : bool :=
  match l with
  | nil => false
  | (y,z,n) :: tl => if V_eq_dec x y then is_not_in_b x tl else is_in_once_b x tl
  end.

Fixpoint NoDup_b (l: nldlist) : bool :=
  match l with
  | nil => true
  | (a, b, c) :: tl => is_in_once_b a l && NoDup_b tl
  end.

Fixpoint each_neighbor_is_in_nld (neigh_list : list Component) (nld : nldlist) : bool :=
  match neigh_list with
  | nil => true
  | a :: tl => is_in_once_b a nld && each_neighbor_is_in_nld tl nld
  end.

Fixpoint each_nld_is_in_neighbor (neigh_list : list Component) (nld : nldlist) : bool :=
  match nld with
  | nil => true
  | (a,b,c) :: tl => is_in a neigh_list && each_nld_is_in_neighbor neigh_list tl
  end.

Definition Checker_local_output_consistent (neigh_list : list Component) (nld : nldlist) : bool :=
  NoDup_b nld &&
  each_neighbor_is_in_nld neigh_list nld &&
  each_nld_is_in_neighbor neigh_list nld.

Definition Local_checker (x : Component) (neigh_list : list Component) (leader parent : Component) (distance : nat) (nld : nldlist) (local_bipartite global_output_consistent: bool): bool :=
  eqb (Checker_local_bipartition distance nld) local_bipartite &&
  Checker_local_output_consistent neigh_list nld &&
  Checker_tree x neigh_list leader parent distance nld &&
  global_output_consistent.

End Checker.




(* Require Extraction. *)
Extraction Language Haskell.
(*Extraction Language Scheme.*)
(*Extraction Language Ocaml.*)
Extraction "Local_checker" Local_checker.