Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.
Require Import Coq.Logic.Classical_Prop.

Load Bipartition_checker.
Require Export Coq.Bool.BoolEq.


Section Checker_proofs.

(******** Network of the algorithm *********)
Variable v : V_set.
Variable a : A_set.
Variable c : Connected v a.
(********/Network of the algorithm *********)

(******** Interface of checker *********)
Variable bipartite_answer : bool.
Variable leader : Component -> Component.
Variable distance : Component -> nat.
Variable parent : Component -> Component.
Variable neighbors_input : Component -> list Component.
Variable nld : Component -> nldlist.
(********/Interface of checker *********)

(******** Seperate function to implement in the framework *********)
Variable global_output_consistent : bool.
(********/Seperate function to implement in the framework *********)

Definition neighbors (x: Component) : list Component :=
  (A_in_neighborhood x (CA_list v a c)).

Fixpoint manual_construct_checker_input_neighbor_list (l : list Component) (leader : Component -> Component) (distance : Component -> nat) : nldlist :=
  match l with
  | nil => nil
  | hd :: tl => (hd, leader hd, distance hd) :: (manual_construct_checker_input_neighbor_list tl leader distance)
  end.


Axiom checker_global_output_consistent_nld_correct1 : forall (x1 x2 : Component),
  global_output_consistent = true ->
    get_distance_in_list x2 (nld x1) = distance x2 /\
    get_leader_in_list x2 (nld x1) = leader x2.

Axiom neighbor_input_is_correct : forall v0,
  neighbors_input v0 = neighbors v0.

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

Lemma is_in_once_correct : forall x l,
  is_in_once x l -> exists y n, In (x,y,n) l.
Proof.
  intros. clear neighbors_input.
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
  intro l. clear neighbors_input.
  induction l ; simpl in * ; intuition.
  inversion H5. subst. destruct (V_eq_dec a1 a1) ; intuition.
  destruct (V_eq_dec a1 a0) ; intuition.
  specialize (IHl a1 b1 c0) ; intuition.
Qed.

Lemma is_not_in_correct' : forall l le d x,
(~ In x l) ->  is_not_in x (manual_construct_checker_input_neighbor_list l le d).
Proof.
  intros.
  induction l ; simpl in * ; intuition.
  destruct (V_eq_dec x a0) ; subst ; intuition.
Qed.

Lemma local_input_correct: forall (x1 x2: Component),
  In x2 (neighbors_input x1) <-> a (A_ends x1 x2).
Proof.
  intros.
  rewrite neighbor_input_is_correct. clear neighbors_input.
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

Lemma nld_correct2' : forall (x1 x2 : Component),
  global_output_consistent = true ->
     get_distance_in_list x2 (nld x1) = distance x2.
Proof.
  intros.
  apply checker_global_output_consistent_nld_correct1 ; auto.
Qed.

Lemma nld_correct2 : forall (x1 x2 : Component),
  global_output_consistent = true ->
     get_distance_in_list x2 (nld x1) = distance x2.
Proof.
  intros.
  apply (nld_correct2' x1 x2) ; auto.
Qed.

Lemma nld_correct5' : forall (x1 x2 : Component),
  global_output_consistent = true ->
     get_leader_in_list x2 (nld x1) = leader x2.
Proof.
  intros.
  apply checker_global_output_consistent_nld_correct1 ; auto.
Qed.

Lemma nld_correct5 : forall (x1 x2 : Component),
  global_output_consistent = true ->
     get_leader_in_list x2 (nld x1) = leader x2.
Proof.
  intros.
  apply (nld_correct5' x1 x2) ; auto.
Qed.

Lemma nld_correct4' : forall (x y : Component),
  is_in_once y (nld x) ->
  (exists (z : Component) (n : nat),
  In (y,z,n) (nld x)).
Proof.
  intros x y H.
  induction (nld x) ; simpl in *.
  inversion H.
  destruct a0. destruct p. destruct (V_eq_dec y c0).
  subst.
  exists c1. exists n0. left. auto.
  apply IHn in H.
  destruct H. destruct H. exists x0. exists x1.
  right. auto.
Qed.

Lemma nld_correct4 : forall (x y : Component),
  is_in_once y (nld x) ->
  (exists (z : Component) (n : nat),
  In (y,z,n) (nld x)).
Proof.
  intros.
  apply (nld_correct4' x y) ; auto.
Qed.

Lemma leader_same_correct : forall (x a b: Component) (l : nldlist) (c : nat),
  leader_same x l = true -> In (a, b, c) l -> b = x.
Proof.
  intros.
  induction l ; simpl in * ; intuition.
  destruct a1. destruct p. inversion H1 ; subst ; intuition.
  destruct (V_eq_dec x b) ; intuition. inversion H.
  destruct a1. destruct p.
  destruct (V_eq_dec x c2) ; intuition.
Qed.

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

Lemma NoDup_b_1: forall (y z : Component) (n : nat) (l : nldlist),
  NoDup_b ((y, z, n) :: l) = true ->
    is_in_once y ((y, z, n) :: l).
Proof.
  intros. clear neighbors_input.
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

Lemma nld_correct1' : forall (x1 x2 : Component),
  Checker_local_output_consistent (neighbors_input x1) (nld x1) = true ->
  is_in_once x2 (nld x1) ->
  In x2 (neighbors_input x1).
Proof.
  intros.
  simpl.
  unfold Checker_local_output_consistent in H.
  apply andb_true_iff in H. destruct H.
  apply andb_true_iff in H. destruct H.
  clear H2.
  simpl in *.
  induction (nld x1).
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

Lemma nld_correct1 : forall (x1 x2 : Component),
  Checker_local_output_consistent (neighbors_input x1) (nld x1) = true ->
  In x2 (neighbors_input x1) -> 
    is_in_once x2 (nld x1).
Proof.
  intros x1 x2 H H1.
  unfold Checker_local_output_consistent in H.
  apply andb_true_iff in H.
  destruct H. clear H0.
  apply andb_true_iff in H.
  destruct H.
  clear H.
  simpl in *. rewrite neighbor_input_is_correct in *. clear neighbors_input.
  induction (neighbors x1).
  inversion H1.
  simpl in *.
  destruct H1 ; subst.
  apply andb_true_iff in H0.
  destruct H0.
  clear H0 IHl.
  induction (nld x1).
  simpl in *. inversion H.
  simpl in *.
  destruct a0. destruct p. destruct (V_eq_dec x2 c0) ; subst ; intuition.
  induction n. simpl. auto.
  simpl in *. destruct a0. destruct p. destruct (V_eq_dec c0 c2) ; subst ; intuition.
  apply andb_true_iff in H0. destruct H0.
  auto.
Qed.

Lemma nld_correct0 : forall (x y z : Component) (n : nat),
  Checker_local_output_consistent (neighbors_input x) (nld x) = true ->
  In (y,z,n) (nld x) ->  
    is_in_once y (nld x).
Proof.
  simpl in * ; intros.
  unfold Checker_local_output_consistent in H.
  apply andb_true_iff in H. destruct H. clear H1. apply andb_true_iff in H. destruct H. clear H1.
  induction (nld x). auto.

  assert (NoDup_b n0 = true).
  apply NoDup_b_2 in H. auto.
  inversion H0. subst.
  apply NoDup_b_1 in H. auto.
  apply IHn0 in H1 ; auto.
  clear H0 IHn0.
  destruct a0. destruct p.
  assert (c0 <> y).
  intuition. subst.
  induction n0. inversion H2. inversion H2. subst. unfold NoDup_b in H.
  simpl in H. destruct (V_eq_dec y y) ; intuition.
  destruct a0. destruct p. simpl in *. destruct (V_eq_dec y y) ; destruct (V_eq_dec c0 c0) ; destruct (V_eq_dec y c0) ; intuition.
  assert (is_not_in_b y n0 && NoDup_b n0 = true).
  apply andb_true_iff in H. destruct H.
  apply andb_true_iff in H2. destruct H2.
  apply andb_true_iff. auto. auto.
  assert (is_not_in_b y n0 && NoDup_b n0 = true).
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
  intros v a c. clear neighbors_input.
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
  intros. clear neighbors_input.
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

Definition get_color (x : Component) : bool :=
  Nat.odd (distance x).

Lemma checker_bipartite_correct : (forall x : Component,
  v x ->
  (Checker_local_bipartition (distance x) (nld x) = true /\
  Checker_local_output_consistent (neighbors_input x) (nld x) = true /\
  global_output_consistent = true)) ->
  forall y : Component, gamma_1 v a c y get_color.
Proof.
  unfold gamma_1.
  intros H y v2 H0. destruct H0 as [H0 H1].
  assert (v y) as vy.
  assert (Connected v a).
  apply c.
  apply Connected_Isa_Graph in H2.
  apply (G_ina_inv1 v a H2) in H1 ; auto.
  assert (H' := H).
  specialize (H y). specialize (H' v2).
  apply H' in H0. apply H in vy. clear H' H.
  unfold get_color.
  assert (In y (neighbors v2)) as H.
  unfold neighbors.
  apply neighborhood_correct1.
  apply (G_non_directed v a) ; auto.
  apply (Connected_Isa_Graph v a) ; auto.
  clear H1.
  destruct H0 as [H0 H00]. destruct H00 as [H00 H000].
  destruct vy as [H1 H11]. destruct H11 as [H11 H111].
  apply (nld_correct1 v2 y) in H00 ; simpl in * ; auto.
  apply (nld_correct2' v2 y) in H000. clear H1 H11 H111 H.
  intuition.
  induction (nld v2).

  inversion H00.
  simpl in *. destruct a0. destruct p.
  destruct (V_eq_dec y c0) ; subst ; intuition.
  assert (eqb (Nat.odd (distance v2)) (Nat.odd (distance v2)) = true) as obvious.
  destruct (Nat.odd (distance v2)). auto. auto.
  rewrite H in *.
  rewrite obvious in *. inversion H0.

  destruct (eqb (Nat.odd (distance v2)) (Nat.odd n0)). inversion H0.
  auto.
  rewrite neighbor_input_is_correct. auto.
Qed.

Lemma Checker_tree_correct : forall (x : Component),
  v x -> (Checker_tree x (neighbors_input x) (leader x) (parent x) (distance x) (nld x)) = true -> global_output_consistent = true -> gamma_2 parent distance v a (leader x) x.
Proof.
  intros x H H0 Hglobal.
  unfold Checker_tree in H0.
  unfold gamma_2.
  unfold parent_prop.
  unfold distance_prop.
  unfold is_same in H0.
  apply andb_prop in H0.
  destruct H0 as [H0 H1].
  rewrite nld_correct2 in * ; auto.

  destruct (V_eq_dec x (leader x)) ; subst.
  simpl in *. rewrite orb_false_r in H1.
  apply andb_prop in H1.
  destruct H1. subst.
  destruct (V_eq_dec x (parent x)) ; subst ; intuition.
  right. intuition. apply beq_nat_true in H2. auto.
  inversion H1.
  inversion H1. simpl in *.
  intuition.
  left.
  assert (a (A_ends x (parent x))).
  apply andb_prop in H1.
  destruct H1.
  unfold neighbors in H1.
  apply is_in_correct in H1.
  apply (neighborhood_correct v a c) ; auto.
  assert (Graph v a).
  apply (Connected_Isa_Graph v a c).
  rewrite neighbor_input_is_correct in *. intuition.
  simpl in *. 
  assert (Graph v a).
  apply (Connected_Isa_Graph v a c).
  intuition.
  apply (G_ina_inv2 _ _ H3 _ _ H2).
  apply (G_non_directed _ _ H3 _ _ H2).
  left. intuition.
  apply andb_prop in H1. destruct H1.
  apply beq_nat_true in H2.
  auto.
Qed.

Lemma all_leader_same : forall x v_random,
  (forall x : Component, v x -> (Checker_tree x (neighbors_input x) (leader x) (parent x) (distance x) (nld x)) = true /\
  Checker_local_output_consistent (neighbors_input x) (nld x) = true /\
  global_output_consistent = true) ->
  v v_random -> v x -> 
  leader x = leader v_random.
Proof. 
  unfold Checker_tree.
  intros x v_random H H0 H1.
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
    apply nld_correct1 in a0.
    apply nld_correct4 in a0.
    destruct a0. destruct H2.
    apply (nld_correct5 x y) in Hglobal ; auto.
    rewrite <- Hglobal. clear Hglobal.
    assert (a0 := H2).
    apply (leader_same_correct (leader x)) in H2 ; auto.
    rewrite <- H2. clear H2 v0. rename a0 into aneu.

    unfold neighbors in *. 



    simpl in *.
    specialize (H' x). clear H4. intuition.
    clear a1 H3 H2 H5.
    induction (nld x).
    inversion aneu.
    simpl in *. destruct a0. destruct p.
    destruct (V_eq_dec y c0) ; destruct (V_eq_dec (leader x) c1) ; subst.
    destruct aneu.
    inversion H2. auto. symmetry.
    apply (leader_same_correct (leader x) c0 x0 n x1) ; auto.
    inversion H. destruct aneu. inversion H2.
    subst. intuition.
    auto.
    inversion H.
    specialize (H' x). intuition.
Qed.  


Fixpoint get_root (v : V_set) (a : A_set) (c : Connected v a) : Component :=
  match c with
  | C_isolated x => x
  | C_leaf v' a' c' x y _ _ => get_root v' a' c'
  | C_edge v' a' c' x y _ _ _ _ _ => get_root v' a' c'
  | C_eq v' _ a' _ _ _ c' => get_root v' a' c'
  end.

Theorem checker_correct :
 ((forall (x : Component), v x ->
  Checker_local_bipartition (distance x) (nld x) = true /\ Checker_local_output_consistent (neighbors_input x) (nld x) = true /\
  global_output_consistent = true) -> 
    bipartite a) 

  /\

(((forall (x : Component), v x -> 
  (Checker_tree x (neighbors_input x) (leader x) (parent x) (distance x) (nld x) = true /\ Checker_local_output_consistent (neighbors_input x) (nld x) = true /\
  global_output_consistent = true)) /\
  (exists (x : Component), v x /\
  Checker_local_bipartition (distance x) (nld x) = false)) -> ~ bipartite a).
Proof.
  split ; intros.
  - apply (Gamma_1_Psi1 (get_root v a c) parent distance v a c get_color).
    unfold Gamma_1.
    intros.
    apply checker_bipartite_correct ; intros ; auto.
  - assert ((forall x : Component,
     v x -> Checker_tree x (neighbors_input x) (leader x) (parent x) (distance x) (nld x) = true) /\
    (exists x : Component, v x /\ Checker_local_bipartition (distance x) (nld x) = false)).
    destruct H ; split ; intros ; auto. apply (H x) ; auto.
    assert (forall x : Component, v x -> Checker_local_output_consistent (neighbors_input x) (nld x) = true).
    intros. destruct H. apply (H x) ; auto.



    destruct H0.
    assert (forall x : Component, v x -> global_output_consistent = true).
    destruct H. clear H3.
    intros. specialize (H x). intuition. clear H.
    assert (exists v_random, v v_random) as v_r.
    apply (v_not_empty v a c).
    destruct v_r as [v_random v_r].
    assert (forall (x : Component), v x -> leader x = leader v_random).
    intros.
    apply all_leader_same ; auto. intros. intuition. apply (H3 x0) ; auto.
    assert (spanning_tree v a (leader v_random) parent distance c) as G1.
    apply G2'G2. unfold Gamma_2'.
    exists (leader v_random). unfold root_prop''.
    split ; intuition.
    specialize (H x). intuition. simpl in *. rewrite <- H5.
    apply Checker_tree_correct ; auto. apply (H3 x) ; auto.
    simpl in *.

    destruct H2. destruct H2.



    apply (Gamma_implies_Psi (leader v_random) parent distance v a c) ; auto.
    apply (Gamma_2_Gamma_3_Gamma (leader v_random) parent distance v a c G1).
    unfold Gamma_3.
    unfold gamma_3.
    unfold neighbors_with_same_color.
    clear H G1 v_r v_random.
    rename H0 into H0'. rename H2 into H0.
    unfold Checker_local_bipartition in H0.
    assert (forall (x y z : Component) (n : nat),
      v x ->
      In (y,z,n) (nld x) ->
      a (A_ends x y)).
    intros.
    apply local_input_correct. simpl in *.
    apply nld_correct0 in H2 ; auto. simpl in *.
    apply nld_correct1' in H2 ; auto.
    exists x.
    specialize (H x).




    assert (forall (x y z : Component) (n : nat),
      v x ->
      In (y,z,n) (nld x) ->
      get_distance_in_list y (nld x) = (distance y)).
    intros.
    apply nld_correct2. apply (H3 x0) ; auto.
    specialize (H2 x).
    assert ({y : Component & {z : Component & In (y, z, distance y) (nld x) /\
      Nat.odd (distance x) = Nat.odd (distance y)}}).


    assert (forall (y z : Component) (n : nat),
      In (y,z,n) (nld x) ->
      is_in_once y (nld x)) as new.
    intros.
    (* specialize (Hneu x). apply Hneu in H. *)
    apply (nld_correct0 x y z n) in H5.
    auto. simpl in H3. auto.
    clear H.
    remember leader as ll. remember parent as pp. remember nld as rr.
    unfold Checker_local_bipartition in H4.
    simpl in *.
    induction (rr x) ; simpl in * ; intuition.
    
    inversion H4.
    destruct a0. destruct p.
    assert (H2' := H2).
    specialize (H2 c0 c1 n0). intuition. clear H5.
    destruct ((V_eq_dec c0 c0)) ; subst.
    assert ({Nat.odd (distance x) = Nat.odd (distance c0)} + 
            {Nat.odd (distance x) <> Nat.odd (distance c0)}).
    apply bool_dec.
    destruct H.
    exists c0. exists c1.
    rewrite e0 in *. intuition.
    unfold eqb in H4.
    assert ({y : Component & {z : Component &
      In (y, z, distance y) n /\
      Nat.odd (distance x) = Nat.odd (distance y)}} -> 
      {y : Component & {z : Component &
      ((c0, c1, distance c0) = (y, z, distance y) \/
      In (y, z, distance y) n) /\
      Nat.odd (distance x) = Nat.odd (distance y)}}).
    intros. destruct H. destruct s. exists x0. exists x1. intuition.
    apply H. clear H.
    apply IHn ; auto.
    destruct (Nat.odd (distance x)) ; destruct (Nat.odd (distance c0)) ; intuition.




    intros. specialize (H2' y z n1). specialize (new y z n1).
    destruct (V_eq_dec y c0) ; subst. remember leader as lll. remember parent as ppp.
    remember nld as rr. intuition.
    apply (is_not_in_correct n c0 z n1) in H8. intuition.
    intuition.
    clear IHn H2' H4.
    intros.
    specialize (new y z n1).
    destruct (V_eq_dec y c0) ; subst.
    assert (is_not_in c0 n). apply new. auto.
    apply (is_not_in_correct n c0 z n1) in H2. intuition.
    intuition.


    intuition.
    destruct H5. repeat destruct s.
    destruct a0.
    exists x0.
    apply H in H5 ; auto.
    assert (v x0).
    assert (Graph v a).
    apply (Connected_Isa_Graph v a c).
    apply (G_ina_inv2 v a H7 _ _ H5).
    intuition.
Qed.

End Checker_proofs.