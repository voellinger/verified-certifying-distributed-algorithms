Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.
Require Import Coq.Logic.Classical_Prop.

Load Bipartition_related.
Require Export Coq.Bool.BoolEq.
Require Extraction.
Extraction Language Haskell.

Section Checker.

(******** Network of the algorithm *********)
Variable v : V_set.
Variable a : A_set.
Variable c : Connected v a.
(********/Network of the algorithm *********)

(******** Interface of checker *********)
Variable bipartite_answer : bool.
Variable global_output_consistent : bool.
Variable leader : Component -> Component.
Variable distance : Component -> nat.
Variable parent : Component -> Component.
Variable neighbors_leader_distance : Component -> list (Component * Component * nat).
(********/Interface of checker *********)


Record local_input: Set := mk_local_input {
  i : Component;
  neighbours : list Component;
}.

Record checker_input : Set := mk_checker_input {
  algo_answer : bool;
  global_consistent : bool;
  leader_i : Component;
  distance_i : nat;
  parent_i : Component;
  neighbor_leader_distance : list (Component * Component * nat)
}.

(*CA_list: all arcs of a Connected-graph*)
Fixpoint CA_list (v : V_set) (a : A_set) (c : Connected v a) {struct c} : A_list :=
  match c with
  | C_isolated x => A_nil
  | C_leaf v' a' c' x y _ _ => A_ends x y :: A_ends y x :: CA_list v' a' c'
  | C_edge v' a' c' x y _ _ _ _ _ => A_ends x y :: A_ends y x :: CA_list v' a' c'
  | C_eq v' _ a' _ _ _ c' => CA_list v' a' c'
  end.

Definition neighbors (x: Component) : list Component :=
  (A_in_neighborhood x (CA_list v a c)).

Definition construct_local_input (x: Component) : local_input :=
  mk_local_input 
    x 
    (neighbors x).

Fixpoint manual_construct_checker_input_neighbor_list (l : list Component) : list (Component * Component * nat) :=
  match l with
  | nil => nil
  | hd :: tl => (hd, leader hd, distance hd) :: (manual_construct_checker_input_neighbor_list tl)
  end.

Definition construct_checker_input (x : Component) : checker_input :=
  mk_checker_input 
    bipartite_answer
    global_output_consistent
    (leader x) 
    (distance x) 
    (parent x)
    (neighbors_leader_distance x).





Lemma CA_list_complete : forall (v : V_set) (a : A_set) (c : Connected v a) (x : Arc),
  a x <-> In x (CA_list v a c).
Proof. clear v a c.
  intros v a c x.
  split ; intros.
  - induction c.
    + simpl.
      inversion H.
    + simpl.
      inversion H.
      inversion H0.
      auto. subst.
      inversion H0 ; subst ; auto.
      subst.
      right. right.
      apply (IHc0 ) ; auto.
    + simpl.
      inversion H ; subst ; auto.
      inversion H0 ; subst ; intuition.
    + rewrite <- e in *.
      rewrite <- e0 in *.
      apply (IHc0 ) ; auto.
  - induction c.
    + simpl in H.
      destruct H.
    + simpl in H.
      destruct H ; subst ; intuition.
      apply In_left. apply E_right.
      subst. apply In_left. apply E_left.
      apply In_right.
      auto.
    + simpl in H.
      destruct H ; subst ; intuition.
      apply In_left. apply E_right.
      subst. apply In_left. apply E_left.
      apply In_right.
      auto.
    + rewrite <- e in *.
      rewrite <- e0 in *.
      apply (IHc0 ) ; auto.
Qed.

Lemma local_input_correct: forall (x1 x2: Component),
  In x2 (construct_local_input x1).(neighbours) <-> a (A_ends x1 x2).
Proof.
  intros.
  unfold construct_local_input.
  unfold neighbours.
  unfold neighbors.
  induction c ; split ; intros ; simpl in * ; subst ; intuition.
  - inversion H.
  - destruct (V_eq_dec x1 y) ; destruct (V_eq_dec x1 x) ; subst ; intuition.
    inversion H ; subst ; auto.
    apply In_left. apply E_left.
    intuition. apply In_right. auto.
    inversion H ; subst ; auto.
    apply In_left. apply E_right.
    intuition. apply In_right. auto.
    apply In_right. auto.
  - destruct (V_eq_dec x1 y) ; destruct (V_eq_dec x1 x) ; subst ; intuition.
    inversion H ; subst.
    inversion H4 ; subst ; intuition.
    intuition. inversion H ; subst.
    inversion H4 ; subst ; intuition. intuition.
    inversion H ; subst.
    inversion H4 ; subst ; intuition.
    intuition.
  - destruct (V_eq_dec x1 y) ; destruct (V_eq_dec x1 x) ; subst ; intuition.
    inversion H ; subst ; auto.
    apply In_left. apply E_left.
    intuition. apply In_right. auto.
    inversion H ; subst ; auto.
    apply In_left. apply E_right.
    intuition. apply In_right. auto.
    apply In_right. auto.
  - destruct (V_eq_dec x1 y) ; destruct (V_eq_dec x1 x) ; subst ; intuition.
    inversion H ; subst.
    inversion H4 ; subst ; intuition.
    intuition. inversion H ; subst.
    inversion H4 ; subst ; intuition. intuition.
    inversion H ; subst.
    inversion H4 ; subst ; intuition.
    intuition.
Qed.

Fixpoint is_not_in (x : Component) (l : list (Component * Component * nat)) : Prop :=
  match l with
  | nil => True
  | (y,z,n) :: tl => if V_eq_dec x y then False else is_not_in x tl
  end.

Fixpoint is_in_once (x : Component) (l : list (Component * Component * nat)) : Prop :=
  match l with
  | nil => False
  | (y,z,n) :: tl => if V_eq_dec x y then is_not_in x tl else is_in_once x tl
  end.

Fixpoint get_distance_in_list (x : Component) (l : list (Component * Component * nat)) : nat :=
  match l with
  | nil => 0
  | (y,z,n) :: tl => if V_eq_dec x y then n else get_distance_in_list x tl
  end.

Fixpoint get_root (v : V_set) (a : A_set) (c : Connected v a) : Component :=
  match c with
  | C_isolated x => x
  | C_leaf v' a' c' x y _ _ => get_root v' a' c'
  | C_edge v' a' c' x y _ _ _ _ _ => get_root v' a' c'
  | C_eq v' _ a' _ _ _ c' => get_root v' a' c'
  end.

Fixpoint get_leader_in_list (x : Component) (l : list (Component * Component * nat)) : Component :=
  match l with
  | nil => (get_root v a c)
  | (y,z,n) :: tl => if V_eq_dec x y then z else get_leader_in_list x tl
  end.

Lemma is_in_once_correct : forall x l,
  is_in_once x l -> exists y n, In (x,y,n) l.
Proof.
  intros.
  induction l.
  inversion H.
  simpl in *. destruct a0. destruct p.
  destruct (V_eq_dec x c0) ; subst ; intuition.
  exists c1. exists n. auto.
  destruct H4. destruct H4. exists x0. exists x1. auto.
Qed.

Lemma is_not_in_correct : forall l a b c,
  is_not_in a l -> ~ In (a,b,c) l.
Proof.
  intro l.
  induction l ; simpl in * ; intuition.
  inversion H5. subst. destruct (V_eq_dec a1 a1) ; intuition.
  destruct (V_eq_dec a1 a0) ; intuition.
  specialize (IHl a1 b1 c0) ; intuition.
Qed.

Lemma is_not_in_correct' : forall l x,
(~ In x l) ->  is_not_in x (manual_construct_checker_input_neighbor_list l).
Proof.
  intros.
  induction l ; simpl in * ; intuition.
  destruct (V_eq_dec x a0) ; subst ; intuition.
Qed.

Fixpoint checker_global_output_consistent (x : Component) :=
  (construct_checker_input x).(global_consistent).

Axiom checker_global_output_consistent_nld_correct1 : forall (x1 x2 : Component),
  checker_global_output_consistent x1 = true ->
    get_distance_in_list x2 (neighbors_leader_distance x1) = (construct_checker_input x2).(distance_i) /\
    get_leader_in_list x2 (neighbors_leader_distance x1) = (construct_checker_input x2).(leader_i).

Lemma neighbors_leader_distance_correct2' : forall (x1 x2 : Component),
  checker_global_output_consistent x1 = true -> 
     get_distance_in_list x2 (neighbors_leader_distance x1) = (construct_checker_input x2).(distance_i).
Proof.
  intros.
  apply checker_global_output_consistent_nld_correct1 ; auto.
Qed.

Lemma neighbors_leader_distance_correct2 : forall (x1 x2 : Component),
  checker_global_output_consistent x1 = true ->
     get_distance_in_list x2 (construct_checker_input x1).(neighbor_leader_distance) = (construct_checker_input x2).(distance_i).
Proof.
  intros.
  apply (neighbors_leader_distance_correct2' x1 x2) ; auto.
Qed.

Lemma neighbors_leader_distance_correct5' : forall (x1 x2 : Component),
  checker_global_output_consistent x1 = true ->
     get_leader_in_list x2 (neighbors_leader_distance x1) = (construct_checker_input x2).(leader_i).
Proof.
  intros.
  apply checker_global_output_consistent_nld_correct1 ; auto.
Qed.

Lemma neighbors_leader_distance_correct5 : forall (x1 x2 : Component),
  checker_global_output_consistent x1 = true ->
     get_leader_in_list x2 (construct_checker_input x1).(neighbor_leader_distance) = (construct_checker_input x2).(leader_i).
Proof.
  intros.
  apply (neighbors_leader_distance_correct5' x1 x2) ; auto.
Qed.

Lemma neighbors_leader_distance_correct4' : forall (x y : Component),
  is_in_once y (neighbors_leader_distance x) ->
  (exists (z : Component) (n : nat),
  In (y,z,n) (neighbors_leader_distance x)).
Proof.
  intros x y H.
  induction (neighbors_leader_distance x) ; simpl in *.
  inversion H.
  destruct a0. destruct p. destruct (V_eq_dec y c0).
  subst.
  exists c1. exists n. left. auto.
  apply IHl in H.
  destruct H. destruct H. exists x0. exists x1.
  right. auto.
Qed.

Lemma neighbors_leader_distance_correct4 : forall (x y : Component),
  is_in_once y (construct_checker_input x).(neighbor_leader_distance) ->
  (exists (z : Component) (n : nat),
  In (y,z,n) (construct_checker_input x).(neighbor_leader_distance)).
Proof.
  intros.
  apply (neighbors_leader_distance_correct4' x y) ; auto.
Qed.

Fixpoint leader_same (x : Component) (l : list (Component * Component * nat)) : bool :=
  match l with
  | nil => true
  | (c1, c2, n) :: tl => if (V_eq_dec x c2) then leader_same x tl else false
  end.

Lemma leader_same_correct : forall (x a b: Component) (l : list (Component * Component * nat)) (c : nat),
  leader_same x l = true -> In (a, b, c) l -> b = x.
Proof.
  intros.
  induction l ; simpl in * ; intuition.
  destruct a1. destruct p. inversion H1 ; subst ; intuition.
  destruct (V_eq_dec x b) ; intuition. inversion H.
  destruct a1. destruct p.
  destruct (V_eq_dec x c2) ; intuition.
Qed.

Function is_leader (x : Component) : bool :=
  if V_eq_dec x (construct_checker_input x).(leader_i) then true else false.

Function is_parent (x : Component) : bool :=
  if V_eq_dec x (construct_checker_input x).(parent_i) then true else false.

Fixpoint is_in (x : Component) (l : list Component) : bool :=
  match l with
  | nil => false
  | y :: tl => if V_eq_dec x y then true else is_in x tl
  end.

Lemma is_in_correct : forall (x : Component) (l : list Component),
  is_in x l = true <-> In x l.
Proof.
  split ; intros.
  induction l ; simpl in * ; intuition.
  destruct (V_eq_dec x a0) ; subst ; intuition.
  induction l ; simpl in * ; intuition.
  destruct (V_eq_dec x a0) ; subst ; intuition.
  destruct (V_eq_dec x a0) ; subst ; intuition.
Qed.

Definition checker_tree (x : Component) : bool :=
  leader_same (construct_checker_input x).(leader_i) (construct_checker_input x).(neighbor_leader_distance) &&
  ((is_leader x && is_parent x && ((construct_checker_input x).(distance_i) =? 0)) ||
  (negb (is_leader x) && (is_in (construct_checker_input x).(parent_i) (construct_local_input x).(neighbours)) &&
   Nat.eqb (construct_checker_input x).(distance_i) ((construct_checker_input (construct_checker_input x).(parent_i)).(distance_i) + 1)
  )).

Fixpoint locally_bipartite (d : nat) (neighbor_l : list (Component * Component * nat)) : bool :=
  match neighbor_l with
  | nil => true
  | (c1, c2, n) :: tl => if (eqb (Nat.odd d) (Nat.odd n)) then false else locally_bipartite d tl
  end.

Definition checker_local_bipartition (x : Component) : bool :=
  locally_bipartite (construct_checker_input x).(distance_i) (construct_checker_input x).(neighbor_leader_distance).

Definition get_color (x : Component) : bool :=
  Nat.odd (construct_checker_input x).(distance_i).

Definition get_distance (x : Component) : nat :=
  (construct_checker_input x).(distance_i).

Definition get_parent (x : Component) : Component :=
  (construct_checker_input x).(parent_i).

Definition get_leader (x : Component) : Component :=
  (construct_checker_input x).(leader_i).

Fixpoint is_not_in_b (x : Component) (l : list (Component * Component * nat)) : bool :=
  match l with
  | nil => true
  | (y,z,n) :: tl => if V_eq_dec x y then false else is_not_in_b x tl
  end.

Fixpoint is_in_once_b (x : Component) (l : list (Component * Component * nat)) : bool :=
  match l with
  | nil => false
  | (y,z,n) :: tl => if V_eq_dec x y then is_not_in_b x tl else is_in_once_b x tl
  end.

Fixpoint NoDup_b (l: list (Component * Component * nat)) : bool :=
  match l with
  | nil => true
  | (a, b, c) :: tl => is_in_once_b a l && NoDup_b tl
  end.

Lemma NoDup_b_1: forall (y z : Component) (n : nat) (l : list (Component * Component * nat)),
  NoDup_b ((y, z, n) :: l) = true ->
    is_in_once y ((y, z, n) :: l).
Proof.
  intros.
  simpl in *.
  destruct (V_eq_dec y y) ; intuition.
  apply andb_true_iff in H.
  destruct H.
  unfold is_not_in.
  induction l ; auto.
  destruct a0. destruct p. simpl in *.
  destruct (V_eq_dec c0 c0) ; intuition.
  destruct (V_eq_dec y c0) ; intuition.
  simpl in *.
  apply andb_true_iff in H4.
  destruct H4.
  intuition.
Qed.

Lemma NoDup_b_2 : forall a0 l,
  NoDup_b (a0 :: l) = true
    -> NoDup_b l = true.
Proof.
  intros.
  unfold NoDup_b in *. destruct a0. destruct p. simpl in *.
  destruct (V_eq_dec c0 c0) ; intuition.
  apply andb_true_iff in H.
  destruct H.
  intuition.
Qed.




Fixpoint each_neighbor_is_in_nld (x : Component) (l : list Component) : bool :=
  match l with
  | nil => true
  | a :: tl => is_in_once_b a (construct_checker_input x).(neighbor_leader_distance) && each_neighbor_is_in_nld x tl
  end.

Fixpoint each_nld_is_in_neighbor (x : Component) (l : list (Component * Component * nat)) : bool :=
  match l with
  | nil => true
  | (a,b,c) :: tl => is_in a (construct_local_input x).(neighbours) && each_nld_is_in_neighbor x tl
  end.

Definition checker_local_output_consistent (x : Component) : bool :=
  NoDup_b (neighbors_leader_distance x) &&
  each_neighbor_is_in_nld x (construct_local_input x).(neighbours) &&
  each_nld_is_in_neighbor x (construct_checker_input x).(neighbor_leader_distance).

Lemma neighbors_leader_distance_correct1' : forall (x1 x2 : Component),
  checker_local_output_consistent x1 = true ->
  is_in_once x2 (neighbors_leader_distance x1) ->
  In x2 (construct_local_input x1).(neighbours).
Proof.
  intros.
  simpl.
  unfold checker_local_output_consistent in H.
  apply andb_true_iff in H. destruct H.
  apply andb_true_iff in H. destruct H.
  clear H2.
  simpl in *.
  induction (neighbors_leader_distance x1).
  inversion H0.
  simpl in *.
  destruct a0. destruct p.
  apply andb_true_iff in H1. destruct H1.
  apply andb_true_iff in H. destruct H.
  destruct (V_eq_dec c0 c0).
  destruct (V_eq_dec x2 c0) ; subst.
  apply is_in_correct in H1 ; auto.
  intuition. intuition.
Qed.

Lemma neighbors_leader_distance_correct1 : forall (x1 x2 : Component),
  checker_local_output_consistent x1 = true ->
  In x2 (construct_local_input x1).(neighbours) -> 
    is_in_once x2 (construct_checker_input x1).(neighbor_leader_distance).
Proof.
  intros x1 x2 H H1.
  unfold checker_local_output_consistent in H.
  apply andb_true_iff in H.
  destruct H. clear H0.
  apply andb_true_iff in H.
  destruct H.
  clear H.
  simpl in *.
  induction (neighbors x1).
  inversion H1.
  simpl in *.
  destruct H1 ; subst.
  apply andb_true_iff in H0.
  destruct H0.
  clear H0 IHl.
  induction (neighbors_leader_distance x1).
  simpl in *. inversion H.
  simpl in *.
  destruct a0. destruct p. destruct (V_eq_dec x2 c0) ; subst ; intuition.
  clear IHl0.
  induction l0. simpl. auto.
  simpl in *. destruct a0. destruct p. destruct (V_eq_dec c0 c2) ; subst ; intuition.
  apply andb_true_iff in H0. destruct H0.
  auto.
Qed.

Lemma neighbors_leader_distance_correct0 : forall (x y z : Component) (n : nat),
  checker_local_output_consistent x = true ->
  In (y,z,n) (neighbors_leader_distance x) ->  
    is_in_once y (construct_checker_input x).(neighbor_leader_distance).
Proof.
  simpl in * ; intros.
  unfold checker_local_output_consistent in H.
  apply andb_true_iff in H. destruct H. clear H1. apply andb_true_iff in H. destruct H. clear H1.
  induction (neighbors_leader_distance x). auto.

  assert (NoDup_b l = true).
  apply NoDup_b_2 in H. auto.
  inversion H0. subst.
  apply NoDup_b_1 in H. auto.
  apply IHl in H1 ; auto.
  clear H0 IHl.
  destruct a0. destruct p.
  assert (c0 <> y).
  intuition. subst. 
  induction l. inversion H2. inversion H2. subst. unfold NoDup_b in H.
  simpl in H. destruct (V_eq_dec y y) ; intuition.
  destruct a0. destruct p. simpl in *. destruct (V_eq_dec y y) ; destruct (V_eq_dec c0 c0) ; destruct (V_eq_dec y c0) ; intuition.
  assert (is_not_in_b y l && NoDup_b l = true).
  apply andb_true_iff in H. destruct H.
  apply andb_true_iff in H2. destruct H2.
  apply andb_true_iff. auto. auto.
  assert (is_not_in_b y l && NoDup_b l = true).
  apply andb_true_iff in H. destruct H.
  apply andb_true_iff in H2. destruct H2.
  apply andb_true_iff. auto. auto.
  unfold is_in_once.
  destruct (V_eq_dec y c0) ; intuition.
  symmetry in e. intuition.
Qed.


Lemma neighborhood_correct : forall (v : V_set) a c x y,
  In y (A_in_neighborhood x (CA_list v a c)) ->
  a (A_ends x y).
Proof.
  clear v a c.
  intros v a c.
  induction c ; simpl in * ; intuition.
  + destruct (V_eq_dec x0 y) ; subst ; intuition.
    - destruct (V_eq_dec y x) ; subst ; intuition.
      simpl in *.
      intuition.
      subst. apply In_left. apply E_left.
      apply In_right.
      specialize (H3 y y0) ; auto.
    - destruct (V_eq_dec x0 x) ; subst ; intuition.
      simpl in *. intuition ; subst.
      apply In_left. apply E_right.
      apply In_right. apply (H3 x y0) ; auto.
      apply In_right. apply (H3 x0 y0) ; auto.
  + destruct (V_eq_dec x0 y) ; subst ; intuition.
    - destruct (V_eq_dec y x) ; subst ; intuition.
      simpl in *.
      intuition.
      subst. apply In_left. apply E_left.
      apply In_right.
      specialize (H3 y y0) ; auto.
    - destruct (V_eq_dec x0 x) ; subst ; intuition.
      simpl in *. intuition ; subst.
      apply In_left. apply E_right.
      apply In_right. apply (H3 x y0) ; auto.
      apply In_right. apply (H3 x0 y0) ; auto.
  + subst. intuition.
Qed.

Lemma neighborhood_correct1 : forall (v : V_set) (a : A_set) c x y,
  a (A_ends x y) ->
  In y (A_in_neighborhood x (CA_list v a c)).
Proof.
  clear v a c.
  intros.
  induction c ; simpl in * ; intuition.
  inversion H.
  destruct (V_eq_dec x y0) ; subst ; intuition.
  destruct (V_eq_dec y0 x0) ; subst ; intuition.
  inversion H.
  subst. inversion H5. subst. simpl. left. auto.
  subst. simpl. auto.
  subst. simpl. right. auto.
  destruct (V_eq_dec x x0) ; subst ; intuition.
  inversion H. inversion H5 ; subst ; simpl.
  auto. auto. subst. simpl. auto.
  inversion H ; subst. inversion H5 ; subst ; simpl.
  intuition. intuition.
  auto.
  destruct (V_eq_dec x y0) ; subst ; intuition.
  destruct (V_eq_dec y0 x0) ; subst ; intuition.
  inversion H.
  subst. inversion H5. subst. simpl. left. auto.
  subst. simpl. auto.
  subst. simpl. right. auto.
  destruct (V_eq_dec x x0) ; subst ; intuition.
  inversion H. inversion H5 ; subst ; simpl.
  auto. auto. subst. simpl. auto.
  inversion H ; subst. inversion H5 ; subst ; simpl.
  intuition. intuition.
  auto.
  subst. auto.
Qed.

Lemma checker_bipartite_correct : (forall x : Component,
  v x ->
  (checker_local_bipartition x = true /\
  checker_local_output_consistent x = true /\
  checker_global_output_consistent x = true)) ->
  forall y : Component, gamma_1 v a c y get_color.
Proof.
  unfold gamma_1.
  intros H. intros. destruct H0.
  assert (v y) as vy.
  assert (Connected v a).
  apply c.
  apply Connected_Isa_Graph in H2.
  apply (G_ina_inv1 v a H2) in H1 ; auto.
  assert (H' := H).
  specialize (H y). specialize (H' v2).
  intuition.
  unfold checker_local_bipartition in *.
  unfold get_color in H2. simpl in *.
  clear H H5 H8.
  assert (In y (neighbors v2)).
  unfold neighbors.
  apply neighborhood_correct1.
  apply (G_non_directed v a) ; auto.
  apply (Connected_Isa_Graph v a) ; auto.
  rename H3 into H5. rename H6 into Hglobal.
  assert (H6 := H5).
  unfold checker_local_output_consistent in H5.
  apply andb_true_iff in H5. destruct H5.
  simpl in *.
  clear H3.
  apply (neighbors_leader_distance_correct1 v2 y) in H6 ; simpl in * ; auto.
  apply (neighbors_leader_distance_correct2' v2 y) in Hglobal.
  simpl in *.
  clear H5 H0 H1 vy.
  
  
  induction (neighbors_leader_distance v2).

  inversion H6.
  simpl in *. destruct a0. destruct p.
  destruct (V_eq_dec y c0) ; subst ; intuition.
  rewrite H2 in *.
  assert (eqb (Nat.odd (distance v2)) (Nat.odd (distance v2)) = true).
  destruct (Nat.odd (distance v2)). auto. auto.
  rewrite H5 in H4. inversion H4.

  destruct (eqb (Nat.odd (distance v2)) (Nat.odd n)). inversion H4.
  auto.
Qed.



Lemma checker_tree_correct : forall (x : Component),
  v x -> (checker_tree x) = true -> gamma_2 get_parent get_distance v a (construct_checker_input x).(leader_i) x.
Proof.
  intros.
  unfold checker_tree in H0.
  unfold gamma_2.
  unfold parent_prop.
  unfold distance_prop.
  unfold is_parent in H0.
  unfold is_leader in H0.
  unfold get_parent.
  apply andb_prop in H0.
  destruct H0.
  destruct (V_eq_dec x (leader_i (construct_checker_input x))) ; subst.
  simpl in *. rewrite orb_false_r in H1.
  apply andb_prop in H1.
  destruct H1. subst.
  destruct (V_eq_dec x (parent x)) ; subst ; intuition.
  right. intuition. unfold get_distance. apply beq_nat_true in H2. auto.
  inversion H1.
  inversion H1. simpl in *.
  intuition.
  left.
  assert (a (A_ends x (parent_i (construct_checker_input x)))).
  apply andb_prop in H1.
  destruct H1.
  unfold neighbors in H1.
  apply is_in_correct in H1.
  apply (neighborhood_correct v a c) ; auto.
  assert (Graph v a).
  apply (Connected_Isa_Graph v a c).
  intuition.
  apply (G_ina_inv2 _ _ H3 _ _ H2).
  apply (G_non_directed _ _ H3 _ _ H2).
  left. intuition.
  apply andb_prop in H1. destruct H1.
  apply beq_nat_true in H2.
  unfold get_distance. auto.
Qed.

Lemma all_leader_same : forall x v_random,
  (forall x : Component, v x -> checker_tree x = true /\
  checker_local_output_consistent x = true /\
  checker_global_output_consistent x = true) ->
  v v_random -> v x -> 
  leader_i (construct_checker_input x) = leader_i (construct_checker_input v_random).
Proof. 
  unfold checker_tree.
  unfold neighbours.
  intros.
  assert ({vl : V_list & {el : E_list & Walk v a v_random x vl el}}).
  apply Connected_walk ; auto.
  destruct H2. destruct s.
  induction w.
  + reflexivity.
  + apply W_endx_inv in w.
    intuition.
    rewrite H3.
    assert (H' := H).
    specialize (H x) ; intuition.
    apply andb_true_iff in H.
    destruct H.

    apply orb_true_iff in H4.
    apply local_input_correct in a0.
    rename H5 into Hglobal.
    clear H3 H2.
    assert (a1 := a0).
    apply neighbors_leader_distance_correct1 in a0.
    apply neighbors_leader_distance_correct4 in a0.
    destruct a0. destruct H2.
    apply (neighbors_leader_distance_correct5 x y) in Hglobal ; auto.
    rewrite <- Hglobal. clear Hglobal.
    assert (a0 := H2).
    apply (leader_same_correct (leader_i (construct_checker_input x))) in H2 ; auto.
    rewrite <- H2. clear H2 v0. rename a0 into aneu.

    unfold neighbors in *. 



    simpl in *.
    specialize (H' x). clear H4. intuition.
    clear a1 H3 H2 H5.
    induction (neighbors_leader_distance x).
    inversion aneu.
    simpl in *. destruct a0. destruct p.
    destruct (V_eq_dec y c0) ; destruct (V_eq_dec (leader x) c1) ; subst.
    destruct aneu.
    inversion H2. auto. symmetry.
    apply (leader_same_correct (leader x) c0 x0 l x1) ; auto.
    inversion H. destruct aneu. inversion H2.
    subst. intuition.
    auto.
    inversion H.
    specialize (H' x). intuition.
Qed.

Theorem checker_correct :
 ((forall (x : Component), v x ->
  checker_local_bipartition x = true /\ checker_local_output_consistent x = true /\
  checker_global_output_consistent x = true) -> 
    bipartite a) 

  /\

(((forall (x : Component), v x -> 
  (checker_tree x = true /\ checker_local_output_consistent x = true /\
  checker_global_output_consistent x = true)) /\
  (exists (x : Component), v x /\
  checker_local_bipartition x = false)) -> ~ bipartite a).
Proof.
  split ; intros.
  - apply (Gamma_1_Psi1 (get_root v a c) get_parent get_distance v a c get_color).
    unfold Gamma_1.
    intros.
    apply checker_bipartite_correct ; intros ; auto.
  - assert ((forall x : Component,
     v x -> checker_tree x = true) /\
    (exists x : Component, v x /\ checker_local_bipartition x = false)).
    destruct H ; split ; intros ; auto. apply (H x) ; auto.
    assert (forall x : Component, v x -> checker_local_output_consistent x = true).
    intros. destruct H. apply (H x) ; auto.



    destruct H0.
    assert (forall x : Component, v x -> checker_global_output_consistent x = true).
    destruct H. clear H3.
    intros. specialize (H x). intuition. clear H.
    assert (exists v_random, v v_random) as v_r.
    apply (v_not_empty v a c).
    destruct v_r as [v_random v_r].
    assert (forall (x : Component), v x -> (construct_checker_input x).(leader_i) = (construct_checker_input v_random).(leader_i)).
    intros.
    apply all_leader_same ; auto.
    assert (spanning_tree v a (leader_i (construct_checker_input v_random)) get_parent get_distance c) as G1.
    apply G2'G2. unfold Gamma_2'.
    exists (leader_i (construct_checker_input v_random)). unfold root_prop''.
    split ; intuition.
    specialize (H x). intuition. simpl in *. rewrite <- H5.
    apply checker_tree_correct ; auto.
    simpl in *.





    apply (Gamma_implies_Psi (leader_i (construct_checker_input v_random)) get_parent get_distance v a c) ; auto.
    apply (Gamma_2_Gamma_3_Gamma (leader_i (construct_checker_input v_random)) get_parent get_distance v a c G1).
    unfold Gamma_3.
    unfold gamma_3.
    unfold neighbors_with_same_color.
    clear H G1 v_r v_random.
    rename H0 into H0'. rename H2 into H0.
    unfold checker_local_bipartition in H0.
    assert (forall (x y z : Component) (n : nat),
      v x ->
      In (y,z,n) (construct_checker_input x).(neighbor_leader_distance) ->
      a (A_ends x y)).
    intros.
    apply local_input_correct. simpl in *.
    apply neighbors_leader_distance_correct0 in H2 ; auto. simpl in *.
    apply neighbors_leader_distance_correct1' in H2 ; auto.
    (* specialize (H1 x). *)




    assert (forall (x y z : Component) (n : nat),
      v x ->
      In (y,z,n) (construct_checker_input x).(neighbor_leader_distance) ->
      get_distance_in_list y (construct_checker_input x).(neighbor_leader_distance) = (construct_checker_input y).(distance_i)).
    intros.
    apply neighbors_leader_distance_correct2. apply (H3 x0) ; auto.
    specialize (Hneu x0).
    intuition.
    apply (neighbors_leader_distance_correct0 x0 y z n) ; auto.
    specialize (H2 x).
    unfold get_distance in *.
    assert ({y : Component & {z : Component & In (y, z, distance_i (construct_checker_input y)) (neighbor_leader_distance (construct_checker_input x)) /\
      Nat.odd (distance_i (construct_checker_input x)) = Nat.odd (distance_i (construct_checker_input y))}}).


    assert (forall (y z : Component) (n : nat),
      In (y,z,n) (construct_checker_input x).(neighbor_leader_distance) ->
      is_in_once y (construct_checker_input x).(neighbor_leader_distance)) as new.
    intros.
    specialize (Hneu x). apply Hneu in H.
    apply (neighbors_leader_distance_correct0 x y z n) in H.
    auto. simpl in H3. auto.
    clear H1.
    remember leader as ll. remember parent as pp. remember neighbors_leader_distance as rr.
    induction (neighbor_leader_distance (construct_checker_input x)) ; simpl in * ; intuition.
    inversion H0.
    destruct a0. destruct p.
    assert (H2' := H2).
    specialize (H2 c0 c1 n). intuition. clear H3.
    destruct ((V_eq_dec c0 c0)) ; subst.
    assert ({Nat.odd (distance x) = Nat.odd (distance c0)} + 
            {Nat.odd (distance x) <> Nat.odd (distance c0)}).
    apply bool_dec.
    destruct H1.
    exists c0. exists c1.
    rewrite e0 in *. intuition.
    unfold eqb in H0.
    assert ({y : Component & {z : Component &
      In (y, z, distance y) l /\
      Nat.odd (distance x) = Nat.odd (distance y)}} -> 
      {y : Component & {z : Component &
      ((c0, c1, distance c0) = (y, z, distance y) \/
      In (y, z, distance y) l) /\
      Nat.odd (distance x) = Nat.odd (distance y)}}).
    intros. destruct H1. destruct s. exists x0. exists x1. intuition.
    apply H1. clear H1.
    apply IHl ; auto.
    destruct (Nat.odd (distance x)) ; destruct (Nat.odd (distance c0)) ; intuition.




    intros. specialize (H2' y z n0). specialize (new y z n0).
    destruct (V_eq_dec y c0) ; subst. remember leader as lll. remember parent as ppp.
    remember neighbors_leader_distance as rr. intuition.
    apply (is_not_in_correct l c0 z n0) in H6. intuition.
    intuition.
    clear IHl H2' H0.
    intros.
    specialize (new y z n0).
    destruct (V_eq_dec y c0) ; subst.
    assert (is_not_in c0 l). apply new. auto.
    apply (is_not_in_correct l c0 z n0) in H1. intuition.
    intuition.


    intuition.
    destruct H3. repeat destruct s.
    destruct a0.
    exists x0.
    apply H1 in H3.
    assert (v x0).
    assert (Graph v a).
    apply (Connected_Isa_Graph v a c).
    apply (G_ina_inv2 v a H5 _ _ H3).
    intuition.
    auto.
Qed.

End Checker.



Recursive Extraction checker_local_bipartition.
Recursive Extraction checker_local_output_consistent.
Recursive Extraction checker_tree.