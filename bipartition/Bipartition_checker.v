Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.
Require Import Coq.Logic.Classical_Prop.

Load Bipartition_related.
Require Export Coq.Bool.BoolEq.
Require Extraction.
Extraction Language Haskell.

Section Checker.

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

Axiom checker_input_correct0 : forall (x y z : Component) (n : nat),
  In (y,z,n) (construct_checker_input x).(neighbor_leader_distance) ->
    is_in_once y (construct_checker_input x).(neighbor_leader_distance).

Axiom checker_input_correct1 : forall (x1 x2 : Component),
  In x2 (construct_local_input x1).(neighbours) <-> 
    is_in_once x2 (construct_checker_input x1).(neighbor_leader_distance).

Axiom checker_input_correct2 : forall (x1 x2 : Component),
  In x2 (construct_local_input x1).(neighbours) <-> 
     get_distance_in_list x2 (construct_checker_input x1).(neighbor_leader_distance) = (construct_checker_input x2).(distance_i).

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
  is_in x l = true -> In x l.
Proof.
  intros.
  induction l ; simpl in * ; intuition.
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


Lemma checker_bipartite_correct : (forall x : Component,
  v x ->
  checker_local_bipartition x = true) ->
  (forall x : Component,
  gamma_1 v a c x get_color).
Proof.
  unfold gamma_1.
  intros.
  destruct H0.
  unfold get_color.
  assert (a (A_ends v2 x)).
  assert (Connected v a).
  apply c.
  apply Connected_Isa_Graph in H2.
  apply (G_non_directed v a H2) in H1 ; auto.
  rename H1 into H1'.
  assert (v x) as vx.
  assert (Connected v a).
  apply c.
  apply Connected_Isa_Graph in H1.
  apply (G_ina_inv2 v a H1) in H2 ; auto.
  apply local_input_correct in H2.
  assert (H1 := H2).
  apply checker_input_correct1 in H2.
  apply checker_input_correct2 in H1.
  intuition.
  rewrite <- H1 in *.
  apply checker_input_correct1 in H2.
  rewrite checker_input_correct2 in * ; auto.
  rewrite H2 in *.
  clear H2.
  subst.
  clear H0 H1.
  specialize (H x) ; intuition.
  apply local_input_correct in H1'.
  apply checker_input_correct1 in H1'.
  unfold checker_local_bipartition in H0.
  assert (H1'' := H1').
  apply checker_input_correct4 in H1'.
  destruct H1'. destruct H.
  apply checker_input_correct0 in H.
  apply checker_input_correct1 in H.
  apply checker_input_correct2 in H.
  rewrite <- H in *. clear H.
  induction (neighbor_leader_distance (construct_checker_input x)) ; simpl in * ; intuition.
  destruct a0. destruct p.
  destruct (V_eq_dec v2 c0) ; subst ; intuition.
  rewrite H3 in *.
  destruct (Nat.odd n) ; intuition.
  destruct (eqb (Nat.odd (distance_i (construct_checker_input x))) (Nat.odd n)) ; subst ; intuition.
Qed.


Lemma checker_bipartite_correct : forall x : Component,
  v x ->
  checker_local_bipartition x = true ->
  gamma_1 v a c x get_color.
Proof.
  unfold gamma_1.
  unfold checker_local_bipartition. 
  intros.
  destruct H1.
  unfold get_color.
  assert (a (A_ends v2 x)).
  assert (Connected v a).
  apply c.
  apply Connected_Isa_Graph in H3.
  apply (G_non_directed v a H3) in H2 ; auto.
  clear H1. clear H.
  apply local_input_correct in H2.
  assert (H1 := H2).
  apply checker_input_correct1 in H2.
  apply checker_input_correct2 in H1.
  apply local_input_correct in H3.
  assert (H4 := H3).
  apply checker_input_correct2 in H3.
  apply checker_input_correct1 in H4.
  rewrite <- H1 in *. rewrite <- H3 in *. clear H3 H1 H4.
(*   clear H1 H4 H3. *)
  induction (neighbor_leader_distance (construct_checker_input x)) ; simpl in * ; intuition.
  destruct a0. destruct p.
  destruct (eqb
         (Nat.odd
            (get_distance_in_list x
               (neighbor_leader_distance (construct_checker_input c0))))
         (Nat.odd n)) ; subst ; intuition.
  destruct (V_eq_dec v2 c0) ; subst ; intuition ; simpl in *.
  destruct (eqb (Nat.odd (distance_i (construct_checker_input x))) (Nat.odd (distance_i (construct_checker_input c0)))) ; subst ; intuition.
  


  clear IHl H4.
  induction (neighbor_leader_distance (construct_checker_input c0)) ; simpl in * ; intuition.
  destruct a0. destruct p.
  destruct (V_eq_dec v2 c2) ; subst ; intuition.
  destruct (eqb (Nat.odd n) (Nat.odd n0)) ; intuition.
  
(*   rewrite <- Nat.negb_even.
  rewrite <- Nat.negb_even.
  assert (forall b1 b2, b1 <> b2 -> negb b1 <> negb b2).
  intros. destruct b1 ; destruct b2 ; intuition.
  apply H.
  
  intuition. *)
  
  apply locally_bipartite' ; auto.
Qed.

Variable dummy : Component.

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

  


Theorem checker_correct :
 ((forall (x : Component), v x ->
  (checker_local_bipartition x) = true) -> bipartite a) /\

(((forall (x : Component), v x -> 
  (checker_tree x) = true) /\
  (exists (x : Component), v x /\
  (checker_local_bipartition x) = false)) -> ~ bipartite a).
Proof.
  unfold checker_local_bipartition.
  unfold checker_tree.
  split ; intros.
  - apply (Gamma_1_Psi1 dummy get_parent get_distance v a c get_color).
    unfold Gamma_1.
    intros.
    apply all_locally_bipartite.
    intuition.
  - assert (exists (root : Component), forall (x : Component), v x -> (construct_checker_input x).(leader_i) = root).
    destruct H. clear dummy H0.
    assert (exists (x : Component), v x).
    clear H construct_checker_input.
    induction c.
    + exists x. apply In_single.
    + exists x. apply In_right. auto.
    + exists x. auto.
    + subst. intuition.
    + destruct H0 as [some_component v_sc]. exists (construct_checker_input some_component).(leader_i). intros.
      specialize (H x). intuition.
      admit.
(*       leader_same (leader_i (construct_checker_input x))
       (neighbor_leader_distance (construct_checker_input x)) &&
      weil x und some_component mit einem weg verbunden sind
 *)
    + destruct H0 as [root leader_prop].
      assert (spanning_tree v a root get_parent get_distance c) as G1.
      admit.
      destruct H.
      destruct H0.
      destruct H0.

      assert (forall (v2 : Component), is_in_once v2 (neighbor_leader_distance (construct_checker_input x)) -> a (A_ends x v2)).
      intros.
      apply local_input_correct.
      apply <- checker_input_correct1 in H2.
      auto.
      assert (exists (v2 : Component), is_in_once v2 (neighbor_leader_distance (construct_checker_input x)) /\
                                        Nat.odd (get_distance x) = Nat.odd (get_distance v2)).
      clear H dummy G1 leader_prop root H2.
      assert (forall (x y z: Component) (n : nat),
          In (y,z,n) (construct_checker_input x).(neighbor_leader_distance) -> 
          (construct_checker_input y).(distance_i) = n).
      apply checker_input_correct3.
      specialize (H x).
      assert (forall (x y z: Component) (n : nat),
          In (y,z,n) (construct_checker_input x).(neighbor_leader_distance) -> 
          is_in_once y (construct_checker_input x).(neighbor_leader_distance)).
      apply checker_input_correct4.
      specialize (H2 x).


  (* rewrite: checker_input_correct1 *)

  (*     induction (neighbor_leader_distance (construct_checker_input x)).
      + inversion H1.
      + destruct a0. destruct p.
        simpl in *.
        destruct (eqb (Nat.odd (distance_i (construct_checker_input x))) (Nat.odd n)) ; subst ; intuition.
        specialize (H c0 c1 n).
        specialize (H2 c0 c1 n).
        assert (In (c0, c1, n) ((c0, c1, n) :: l)). intuition. intuition. clear H3.
        exists c0.
        simpl in *.
        split. auto. *)
    
        
        
        
        
      admit.
      destruct H3 as [v2 H3].
      specialize (H2 v2).
      intuition.

      apply (Gamma_implies_Psi root get_parent get_distance v a c) ; auto.
      apply (Gamma_2_Gamma_3_Gamma root get_parent get_distance v a c G1).
      unfold Gamma_3.
      unfold gamma_3.
      unfold neighbors_with_same_color.
      clear leader_prop G1 root.
      exists x. exists v2. intuition.
      assert (Graph v a).
      apply (Connected_Isa_Graph v a c).
      apply (G_ina_inv2 v a H2 _ _ H3).
Admitted.   

End Checker.