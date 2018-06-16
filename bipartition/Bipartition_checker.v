Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.
Require Import Coq.Logic.Classical_Prop.

Load Bipartition_related.
Require Export Coq.Bool.BoolEq.
Require Extraction.
Extraction Language Haskell.

Section Checker.

Variable dummy : Component.

Record local_input: Set := mk_local_input {
  i : Component;
  neighbours : list Component;
}.

Record checker_input : Set := mk_checker_input {
algo_answer : bool;
leader_i : Component;
distance_i : nat;
parent_i : Component;
neighbor_leader_distance : list (Component * Component * nat)
}.

(*CA_list: all arcs of a Connected-graph*)
Fixpoint CA_list (v : V_set) (a : A_set) (c : Connected v a) {struct c} :
 A_list :=
  match c with
  | C_isolated x => A_nil
  | C_leaf v' a' c' x y _ _ => A_ends x y :: A_ends y x :: CA_list v' a' c'
  | C_edge v' a' c' x y _ _ _ _ _ => A_ends x y :: A_ends y x :: CA_list v' a' c'
  | C_eq v' _ a' _ _ _ c' => CA_list v' a' c'
  end.

Lemma CA_list_complete : forall (v : V_set) (a : A_set) (c : Connected v a) (x : Arc),
  a x <-> In x (CA_list v a c).
Proof.
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
      apply (IHc H0).
    + simpl.
      inversion H ; subst ; auto.
      inversion H0 ; subst ; intuition.
    + rewrite <- e in *.
      rewrite <- e0 in *.
      apply (IHc H).
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
      apply (IHc H).
Qed.

Variable v : V_set.
Variable a : A_set.
Variable c : Connected v a.

Definition neighbors (x: Component) : list Component :=
(A_in_neighborhood x (CA_list v a c)).

Definition construct_local_input (x: Component) : local_input :=
mk_local_input x (neighbors x).

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
    inversion H0 ; subst ; intuition.
    intuition. inversion H ; subst.
    inversion H0 ; subst ; intuition. intuition.
    inversion H ; subst.
    inversion H0 ; subst ; intuition.
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
    inversion H0 ; subst ; intuition.
    intuition. inversion H ; subst.
    inversion H0 ; subst ; intuition. intuition.
    inversion H ; subst.
    inversion H0 ; subst ; intuition.
    intuition.
Qed.

Variable construct_checker_input : Component -> checker_input.

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

Fixpoint get_leader_in_list (x : Component) (l : list (Component * Component * nat)) : Component :=
  match l with
  | nil => dummy
  | (y,z,n) :: tl => if V_eq_dec x y then z else get_leader_in_list x tl
  end.

Axiom checker_input_correct0 : forall (x y z : Component) (n : nat),
  In (y,z,n) (construct_checker_input x).(neighbor_leader_distance) ->
    is_in_once y (construct_checker_input x).(neighbor_leader_distance).

Axiom checker_input_correct1 : forall (x1 x2 : Component),
  In x2 (construct_local_input x1).(neighbours) <-> 
    is_in_once x2 (construct_checker_input x1).(neighbor_leader_distance).

Axiom checker_input_correct2 : forall (x1 x2 : Component),
  In x2 (construct_local_input x1).(neighbours) -> 
     get_distance_in_list x2 (construct_checker_input x1).(neighbor_leader_distance) = (construct_checker_input x2).(distance_i).

Axiom checker_input_correct5 : forall (x1 x2 : Component),
  In x2 (construct_local_input x1).(neighbours) -> 
     get_leader_in_list x2 (construct_checker_input x1).(neighbor_leader_distance) = (construct_checker_input x2).(leader_i).

Lemma checker_input_correct4 : forall (x y : Component),
  is_in_once y (construct_checker_input x).(neighbor_leader_distance) ->
  (exists (z : Component) (n : nat),
  In (y,z,n) (construct_checker_input x).(neighbor_leader_distance)).
Proof.
  intros.
  induction (neighbor_leader_distance (construct_checker_input x)) ; intros ; simpl in * ; intuition.
  destruct a0. destruct p.
  destruct (V_eq_dec y c0) ; intuition.
  subst.
  exists (c1). exists n. auto.
  destruct H1. destruct H1.
  exists x0. exists x1. auto.
Qed.

Lemma checker_input_correct3 : forall (x y z: Component) (n : nat),
  In (y,z,n) (construct_checker_input x).(neighbor_leader_distance) -> 
    (construct_checker_input y).(distance_i) = n.
Proof.
  intros.
  assert (H' := H).
  apply checker_input_correct0 in H'.
  apply checker_input_correct1 in H'.
  apply checker_input_correct2 in H'.
  rewrite <- H'. clear H'.
  assert (H' := H).
  apply checker_input_correct0 in H.
  induction (neighbor_leader_distance (construct_checker_input x)) ; intros ; simpl in * ; intuition.
  - destruct a0. destruct p.
    destruct (V_eq_dec y c0) ; subst ; intuition.
    inversion H0. intuition.
    inversion H0. symmetry in H4. intuition.
  - destruct a0. destruct p.
    destruct (V_eq_dec y c0) ; subst ; intuition.
    exfalso.
    clear IHl H1 n0 c1 x v a c.
    induction l ; simpl in * ; intuition.
    destruct a. destruct p.
    inversion H1 ; subst.
    destruct (V_eq_dec c0 c0) ; intuition.
    destruct a. destruct p.
    destruct (V_eq_dec c0 c) ; intuition.
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


Lemma checker_bipartite_correct : forall x : Component,
  v x ->
  checker_local_bipartition x = true ->
  gamma_1 v a c x get_color.
Proof.
  unfold gamma_1.
  intros.
  destruct H1.
  unfold get_color.
  assert (a (A_ends v2 x)).
  assert (Connected v a).
  apply c.
  apply Connected_Isa_Graph in H3.
  apply (G_non_directed v a H3) in H2 ; auto.
  rename H2 into H2'.
  assert (v x) as vx.
  assert (Connected v a).
  apply c.
  apply Connected_Isa_Graph in H2.
  apply (G_ina_inv2 v a H2) in H3 ; auto.
  apply local_input_correct in H3.
  assert (H2 := H3).
  apply checker_input_correct1 in H3.
  apply checker_input_correct2 in H2.
  intuition.
  rewrite <- H2 in *.
  apply checker_input_correct1 in H3.
  rewrite checker_input_correct2 in * ; auto.
  subst.
  clear H1 H2.
  apply local_input_correct in H2'.
  apply checker_input_correct1 in H2'.
  unfold checker_local_bipartition in H0.
  assert (H2'' := H2').
  apply checker_input_correct4 in H2'.
  destruct H2'. destruct H1.
  apply checker_input_correct0 in H1.
  apply checker_input_correct1 in H1.
  apply checker_input_correct2 in H1.
  rewrite <- H1 in *. clear H1.
  induction (neighbor_leader_distance (construct_checker_input x)) ; simpl in * ; intuition.
  destruct a0. destruct p.
  destruct (V_eq_dec v2 c0) ; subst ; intuition.
  rewrite H4 in *.
  destruct (Nat.odd n) ; intuition.
  destruct (eqb (Nat.odd (distance_i (construct_checker_input x))) (Nat.odd n)) ; subst ; intuition.
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
      specialize (H0 y y0) ; auto.
    - destruct (V_eq_dec x0 x) ; subst ; intuition.
      simpl in *. intuition ; subst.
      apply In_left. apply E_right.
      apply In_right. apply (H0 x y0) ; auto.
      apply In_right. apply (H0 x0 y0) ; auto.
  + destruct (V_eq_dec x0 y) ; subst ; intuition.
    - destruct (V_eq_dec y x) ; subst ; intuition.
      simpl in *.
      intuition.
      subst. apply In_left. apply E_left.
      apply In_right.
      specialize (H0 y y0) ; auto.
    - destruct (V_eq_dec x0 x) ; subst ; intuition.
      simpl in *. intuition ; subst.
      apply In_left. apply E_right.
      apply In_right. apply (H0 x y0) ; auto.
      apply In_right. apply (H0 x0 y0) ; auto.
  + subst. intuition.
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
  destruct (V_eq_dec x (parent_i (construct_checker_input x))) ; subst ; intuition.
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
  (forall x : Component, v x -> checker_tree x = true) ->
  v v_random -> v x -> 
  leader_i (construct_checker_input x) = leader_i (construct_checker_input v_random).
Proof.
  unfold checker_tree.
  unfold neighbours.
  simpl in *. unfold neighbors. intros.
  assert ({vl : V_list & {el : E_list & Walk v a v_random x vl el}}).
  apply Connected_walk ; auto.
  destruct H2. destruct s.
  induction w.
  + reflexivity.
  + apply W_endx_inv in w.
    intuition.
    rewrite H3.
    specialize (H x) ; intuition.
    apply andb_true_iff in H2.
    destruct H2.
    apply orb_true_iff in H2.
    apply local_input_correct in a0.
    clear H3 H2.
    assert (a1 := a0).
    apply checker_input_correct1 in a0.
    apply checker_input_correct4 in a0.
    destruct a0. destruct H2.
    apply checker_input_correct5 in a1.
    rewrite <- a1. clear a1.
    assert (a0 := H2).
    apply (leader_same_correct (leader_i (construct_checker_input x))) in H2 ; auto.
    rewrite <- H2. clear H2.
    induction (neighbor_leader_distance (construct_checker_input x)) ; simpl in * ; intuition.
    destruct a1. destruct p.
    destruct (V_eq_dec y c0) ; subst ; intuition.
    inversion H2. subst. intuition. inversion H2. subst. intuition.
    destruct a1. destruct p.
    destruct (V_eq_dec y c0) ; subst ; intuition.
    destruct (V_eq_dec (leader_i (construct_checker_input x)) c1) ; subst ; intuition.
    apply (leader_same_correct _ c0 x0 l x1) in H ; auto.
    inversion H.
    destruct (V_eq_dec (leader_i (construct_checker_input x)) c1) ; subst ; intuition.
Qed.

Lemma checker_true' : 
  (forall x, v x -> checker_tree x = true) ->
  (forall x, v x -> (({x = leader_i (construct_checker_input x) /\ x = parent_i (construct_checker_input x) /\ distance_i (construct_checker_input x) = 0} +
         {x <> leader_i (construct_checker_input x) /\ a (A_ends x (parent_i (construct_checker_input x))) /\
          (distance_i (construct_checker_input x) = 1 + distance_i (construct_checker_input (parent_i (construct_checker_input x))))}))).
Proof.
  intros. rename x into x0.
  unfold checker_tree in H.
  specialize (H x0) ; intuition.
  apply andb_true_iff in H1. destruct H1.
  apply orb_true_elim in H1. destruct H1.
  left.
  apply andb_true_iff in e. destruct e.
  apply andb_true_iff in H1. destruct H1.
  apply beq_nat_true in H2.
  unfold is_leader in H1. unfold is_parent in H3.
  destruct (V_eq_dec x0 (leader_i (construct_checker_input x0))) ; subst ; intuition.
  destruct (V_eq_dec x0 (parent_i (construct_checker_input x0))) ; subst ; intuition.
  inversion H3. inversion H1. inversion H1.
  right.
  apply andb_true_iff in e. destruct e.
  apply andb_true_iff in H1. destruct H1.
  apply beq_nat_true in H2.
  apply negb_true_iff in H1.
  apply is_in_correct in H3.
  apply neighborhood_correct in H3.
  unfold is_leader in H1.
  destruct (V_eq_dec x0 (leader_i (construct_checker_input x0))) ; subst ; intuition.
Qed.

Lemma parent_i_local : forall x, (forall x,
  v x -> checker_tree x = true) -> v x ->
  v (parent_i (construct_checker_input x)).
Proof.
  intros.
  assert (forall x, v x -> (({x = leader_i (construct_checker_input x) /\ x = parent_i (construct_checker_input x) /\ distance_i (construct_checker_input x) = 0} +
         {x <> leader_i (construct_checker_input x) /\ a (A_ends x (parent_i (construct_checker_input x))) /\
          (distance_i (construct_checker_input x) = 1 + distance_i (construct_checker_input (parent_i (construct_checker_input x))))}))).
  apply checker_true' ; auto.
  clear H.
  specialize (H1 x).
  intuition.
  rewrite <- H2. auto.
  assert (Graph v a). apply Connected_Isa_Graph ; auto.
  apply (G_ina_inv2 v a H1 x); auto.
Qed.

Lemma is_not_in_correct : forall l a b c,
  is_not_in a l -> ~ In (a,b,c) l.
Proof.
  intro l.
  induction l ; simpl in * ; intuition.
  inversion H2. subst. destruct (V_eq_dec a1 a1) ; intuition.
  destruct (V_eq_dec a1 a0) ; intuition.
  specialize (IHl a1 b1 c0) ; intuition.
Qed.

Theorem checker_correct :
 ((forall (x : Component), v x ->
  (checker_local_bipartition x) = true) -> bipartite a) /\

(((forall (x : Component), v x -> 
  (checker_tree x) = true) /\
  (exists (x : Component), v x /\
  (checker_local_bipartition x) = false)) -> ~ bipartite a).
Proof.
  split ; intros.
  - apply (Gamma_1_Psi1 dummy get_parent get_distance v a c get_color).
    unfold Gamma_1.
    intros.
    apply checker_bipartite_correct ; intros ; auto.
  - assert (exists v_random, v v_random) as v_r.
    apply (v_not_empty v a c).
    destruct v_r as [v_random v_r].
    assert (forall (x : Component), v x -> (construct_checker_input x).(leader_i) = (construct_checker_input v_random).(leader_i)).
    destruct H. clear H0.
    intros.
    apply all_leader_same ; auto.
    assert (spanning_tree v a (leader_i (construct_checker_input v_random)) get_parent get_distance c) as G1.
    apply G2'G2. unfold Gamma_2'.
    exists (leader_i (construct_checker_input v_random)). unfold root_prop''.
    split ; intuition.
    specialize (H1 x).
    apply checker_tree_correct in H1 ; auto.
    specialize (H0 x) ; intuition. rewrite <- H3. auto.


    destruct H. clear H H0.
    destruct H1. destruct H.


    apply (Gamma_implies_Psi (leader_i (construct_checker_input v_random)) get_parent get_distance v a c) ; auto.
    apply (Gamma_2_Gamma_3_Gamma (leader_i (construct_checker_input v_random)) get_parent get_distance v a c G1).
    unfold Gamma_3.
    unfold gamma_3.
    unfold neighbors_with_same_color.
    clear G1 v_random v_r.
    exists x.
    unfold checker_local_bipartition in H0.
    assert (forall (x y z : Component) (n : nat),
      In (y,z,n) (construct_checker_input x).(neighbor_leader_distance) ->
      a (A_ends x y)).
    intros.
    apply local_input_correct.
    apply checker_input_correct1. apply checker_input_correct0 in H1 ; auto.
    specialize (H1 x).




    assert (forall (x y z : Component) (n : nat),
      In (y,z,n) (construct_checker_input x).(neighbor_leader_distance) ->
      get_distance_in_list y (construct_checker_input x).(neighbor_leader_distance) = (construct_checker_input y).(distance_i)).
    intros.
    apply checker_input_correct2. apply checker_input_correct1. apply checker_input_correct0 in H2. auto.
    specialize (H2 x).
    unfold get_distance in *.
    assert ({y : Component & {z : Component & In (y, z, distance_i (construct_checker_input y)) (neighbor_leader_distance (construct_checker_input x)) /\
              Nat.odd (distance_i (construct_checker_input x)) = Nat.odd (distance_i (construct_checker_input y))}}).


    assert (forall (y z : Component) (n : nat),
  In (y,z,n) (construct_checker_input x).(neighbor_leader_distance) ->
    is_in_once y (construct_checker_input x).(neighbor_leader_distance)) as new.
    apply checker_input_correct0.
    clear H1.

    induction (neighbor_leader_distance (construct_checker_input x)) ; simpl in * ; intuition.
    inversion H0.
    destruct a0. destruct p.
    assert (H2' := H2).
    specialize (H2 c0 c1 n). intuition. clear H3.
    destruct ((V_eq_dec c0 c0)) ; subst ; intuition.
    assert ({Nat.odd (distance_i (construct_checker_input x)) = Nat.odd (distance_i (construct_checker_input c0))} + 
            {Nat.odd (distance_i (construct_checker_input x)) <> Nat.odd (distance_i (construct_checker_input c0))}).
    apply bool_dec.
    destruct H1.
    exists c0. exists c1.
    rewrite e0 in *. intuition.
    unfold eqb in H0.
    assert ({y : Component &
      {z : Component &
      In (y, z, distance_i (construct_checker_input y)) l /\
      Nat.odd (distance_i (construct_checker_input x)) = Nat.odd (distance_i (construct_checker_input y))}} -> 
            {y : Component &
{z : Component &
((c0, c1, distance_i (construct_checker_input c0)) = (y, z, distance_i (construct_checker_input y)) \/
 In (y, z, distance_i (construct_checker_input y)) l) /\
Nat.odd (distance_i (construct_checker_input x)) = Nat.odd (distance_i (construct_checker_input y))}}).
    intros. destruct H1. destruct s. exists x0. exists x1. intuition.
    apply H1. clear H1.
    apply IHl ; auto.
    destruct (Nat.odd (distance_i (construct_checker_input x))) ; destruct (Nat.odd (distance_i (construct_checker_input c0))) ; intuition.



    intros. specialize (H2' y z n0). specialize (new y z n0). intuition.
    destruct (V_eq_dec y c0) ; subst ; intuition.
    apply (is_not_in_correct l c0 z n0) in H4. intuition.
    clear IHl H2' H0.
    intros.
    specialize (new y z n0).
    destruct (V_eq_dec y c0) ; subst ; intuition.
    apply (is_not_in_correct l c0 z n0) in H3. intuition.



    destruct H3. repeat destruct s.
    destruct a0.
    exists x0.
    apply H1 in H3.
    assert (v x0).
    assert (Graph v a).
    apply (Connected_Isa_Graph v a c).
    apply (G_ina_inv2 v a H5 _ _ H3).
    intuition.
Qed.

End Checker.



Recursive Extraction checker_local_bipartition.
Recursive Extraction checker_tree.
