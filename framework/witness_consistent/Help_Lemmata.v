Require Import GraphBasics.Graphs.
Require Import Coq.Logic.Classical_Prop.
Require Import Verdi.Verdi.
Require Export StructTact.Fin.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Require Import Verdi.ExtrOcamlBasicExt.
Require Import Verdi.ExtrOcamlList.

Require Import FunInd.


Load CDAInterface.
Section Help_Lemmata.




Lemma list_not_equals : forall (T : Type) (x y : T) (l1 l2 : list T) ,
  (x <> y \/ l1 <> l2) -> (x :: l1 <> y :: l2).
Proof.
  intros T x y l1 l2.
  induction l1 ; unfold not.
  + intros.
    destruct H.
    - destruct l2.
      inversion H0.
      intuition.
      inversion H0.
    - destruct l2.
      intuition.
      inversion H0.
  + intros.
    destruct H.
    - induction l2.
      inversion H0.
      inversion H0.
      intuition.
    - inversion H0.
      intuition.
Qed.

Lemma silly_lemma : forall (T: Type) y (p : T) xs ys, 
  In p (xs ++ ys) -> In p (xs ++ y :: ys).
Proof.
  intros T y p xs ys H.
  apply in_app_or in H.
  apply in_or_app.
  simpl.
  destruct H ; auto.
Qed.


Lemma name_comp_name : forall n1 n2,
  name_component n1 = name_component n2 -> n1 = n2.
Proof.
  intros n1 n2 H.
  unfold name_component in *.
  break_match.
  break_match.
  subst.
  auto.
Qed.

Lemma checker_name : forall p,
  Checker (name_component p) = p.
Proof.
  intros p.
  unfold name_component.
  break_match.
  auto.
Qed.

Notation "a =/= b" := (beq_nat (Some a) (Some b)) (at level 70).
Notation "a == b" := (beq_nat a b) (at level 70).

Lemma beq_false_nat : forall n m : nat, 
  n <> m -> (n == m) = false.
Proof.
  induction n; induction m; intros.
  intuition.
  intuition.
  intuition.
  simpl.
  intuition.
Qed.


Fixpoint remove_src (src : Name) (child_list : list Name) : list Name :=
  match child_list with
  | [] => []
  | hd :: tl => if (component_index (name_component src) == component_index (name_component hd)) then tl else (remove_src src tl)
  end.

Fixpoint is_always (test_case : Assignment) (vl : list Assignment) : bool :=
  let (var, val) := test_case in
  match vl with
  | nil => true
  | hd :: tl => let (vl_var, vl_val) := hd in
      if (var_beq var vl_var) then (val_beq val vl_val) && is_always test_case tl else is_always test_case tl
  end.

Fixpoint check_ass_list (vl : list Assignment) : bool :=
  match vl with
  | nil => true
  | hd :: tl => (is_always hd tl) && check_ass_list tl
  end.

Lemma remove_src_before : forall d pSrc l1,
  In d (remove_src pSrc l1) ->
  In d l1.
Proof.
  intros.
  induction l1.
  - simpl in H.
    inversion H.
  - simpl in *.
    break_match ; auto.
Qed.

Lemma is_consistent_one_lesss : forall a0 cert,
  is_consistent (a0 :: cert) ->
  is_consistent cert.
Proof.
  intros a0 cert H.
  unfold is_consistent in *.
  intros.
  destruct assign1.
  destruct assign2.
  intros.
  specialize (H (assign_cons v0 v1)).
  specialize (H (assign_cons v2 v3)).
  simpl in H.
  apply H ; auto.
Qed.

Lemma not_consistent_one_less : forall cert va0 va1,
  ~ is_consistent (assign_cons va0 va1 :: cert) ->
  (~ is_consistent cert \/ (exists v3, In (assign_cons va0 v3) cert /\ va1 <> v3)).
Proof.
  intros cert va0 va1 H.
  assert (is_consistent cert \/ ~is_consistent cert) as new.
  apply classic.
  destruct new as [new|neww].
  right.
  induction cert.
  + assert (is_consistent [assign_cons va0 va1]).
    unfold is_consistent.
    destruct assign1.
    destruct assign2.
    intros.
    inversion H0.
    inversion H1.
    apply <- Assignment_eq_dec3 in H3.
    apply <- Assignment_eq_dec3 in H4.
    destruct H3. destruct H4.
    rewrite <- H5. rewrite H6. auto.
    inversion H4.
    inversion H3.
    intuition.
  + assert (new' := new).
    apply is_consistent_one_lesss in new'.
    destruct a0.
    assert ((va0 = v0 /\ va1 <> v1) \/ ~ is_consistent (assign_cons va0 va1 :: cert)).
      clear new' IHcert.
      assert ((va0 = v0 /\ va1 <> v1) \/ ~(va0 = v0 /\ va1 <> v1)).
      apply classic.
      destruct H0.
      destruct H0.
      left. auto.
      assert (va0 <> v0 \/ va1 = v1).
      assert (va0 = v0 \/ va0 <> v0).
      apply classic.
      destruct H1.
      assert (va1 = v1 \/ va1 <> v1).
      apply classic.
      destruct H2.
      right. auto.
      rewrite H1 in H0. intuition.
      left. auto.
      right. clear H0.
      destruct H1.
        intuition.
        apply H.
        unfold is_consistent.
        destruct assign1. destruct assign2.
        intros. subst.
        simpl in *.
        destruct H2.
          apply <- Assignment_eq_dec3 in H2. destruct H2. subst.
          destruct H3.
            apply <- Assignment_eq_dec3 in H2. destruct H2. auto.
            destruct H2.
              apply <- Assignment_eq_dec3 in H2. destruct H2. subst.
              intuition.
              unfold is_consistent in H1.
              apply (H1 (assign_cons v4 v3) (assign_cons v4 v5)) ; auto.
              simpl. left. auto.
              simpl. right. auto.
          destruct H2.
            apply <- Assignment_eq_dec3 in H2. destruct H2. subst.
            destruct H3.
              apply <- Assignment_eq_dec3 in H2. destruct H2. subst.
              intuition.
              destruct H2.
                apply <- Assignment_eq_dec3 in H2. destruct H2. auto.
                unfold is_consistent in new.
                apply (new (assign_cons v4 v3) (assign_cons v4 v5)) ; auto.
                simpl. left. auto.
                simpl. right. auto.
            destruct H3.
            apply <- Assignment_eq_dec3 in H3. destruct H3. subst.
            apply (H1 (assign_cons v4 v3) (assign_cons v4 v5)) ; auto.
            simpl. right. auto.
            simpl. left. auto.
            destruct H3.
            apply <- Assignment_eq_dec3 in H3. destruct H3. subst.
            apply (new (assign_cons v4 v3) (assign_cons v4 v5)) ; auto.
            simpl. right. auto.
            simpl. left. auto.
            apply (is_consistent_one_lesss) in new.
          unfold is_consistent in new.
          apply (new (assign_cons v4 v3) (assign_cons v4 v5)) ; auto.

        intuition.
        apply H.
        unfold is_consistent.
        intros.
        destruct assign1. destruct assign2.
        intros.
        subst.
        inversion H2.
          apply <- Assignment_eq_dec3 in H0.
          destruct H0.
          subst.
          inversion H3.
            apply <- Assignment_eq_dec3 in H0.
            destruct H0.
            subst.
            auto.
            inversion H0.
              apply <- Assignment_eq_dec3 in H4.
              destruct H4. subst. auto.
              unfold is_consistent in H1.
              apply (H1 (assign_cons v4 v3) (assign_cons v4 v5)) ; auto.
              simpl. left. auto.
            simpl. right. auto.
          inversion H0.
            apply <- Assignment_eq_dec3 in H4.
            destruct H4.
            subst.
            inversion H3.
              apply <- Assignment_eq_dec3 in H4.
              destruct H4.
              auto.
              inversion H4.
              apply <- Assignment_eq_dec3 in H5.
              destruct H5. auto.
            unfold is_consistent in new.
            apply (new (assign_cons v4 v3) (assign_cons v4 v5)) ; auto.
          inversion H3.
          apply <- Assignment_eq_dec3 in H5. destruct H5. subst.
          unfold is_consistent in H1.
          apply (H1 (assign_cons v4 v3) (assign_cons v4 v5)) ; auto.
          simpl. right. auto.
          simpl. left. auto.
          inversion H5.
          apply <- Assignment_eq_dec3 in H6. destruct H6. subst.
          unfold is_consistent in new.
          apply (new (assign_cons v4 v3) (assign_cons v4 v5)) ; auto.
          apply (is_consistent_one_lesss) in new.
          unfold is_consistent in new.
          apply (new (assign_cons v4 v3) (assign_cons v4 v5)) ; auto.
    destruct H0.
    exists v1.
    destruct H0.
    rewrite H0.
    split.
    simpl. left. auto.
    auto.
    apply IHcert in H0 ; auto.
    destruct H0.
    destruct H0.
    exists x.
    split.
    simpl. right. auto.
    auto.
  + left. auto.
Qed.

Lemma is_consistent_in_parts : forall c1 c2,
  is_consistent (c1 ++ c2) -> is_consistent c1 /\ is_consistent c2.
Proof.
  intros c1 c2 H.
  + induction c1.
    - simpl in *.
      split.
      unfold is_consistent.
      intros. destruct assign1. destruct assign2. intros. inversion H0.
      auto.
    - simpl in *.
      assert (H' := H).
      apply is_consistent_one_lesss in H'.
      apply IHc1 in H'.
      destruct H'.
      split.
      unfold is_consistent. unfold is_consistent in H.
      intros.
      specialize (H assign1 assign2).
      destruct assign1. destruct assign2.
      intros. apply H ; auto ; simpl.
      inversion H2 ; auto. right. apply in_or_app. left. auto.
      inversion H3 ; auto. right. apply in_or_app. left. auto.
      auto.
Qed.


Lemma not_consistent : forall cert,
 ~ is_consistent cert <-> 
  (exists v0 v1 v3, In (assign_cons v0 v1) cert /\ In (assign_cons v0 v3) cert /\ v1 <> v3).
Proof.
  intros cert.
  split ; intros.
  + induction cert.
    - assert (is_consistent []).
      unfold is_consistent.
      intros.
      destruct assign1. destruct assign2.
      intros.
      inversion H0.
      intuition.
    - destruct a0 as [va0 va1].
      assert (~ is_consistent cert \/ (exists v3, In (assign_cons va0 v3) cert /\ va1 <> v3)).
      apply not_consistent_one_less ; auto.
      destruct H0.
      apply IHcert in H0.
      destruct H0.
      destruct H0.
      destruct H0.
      destruct H0.
      destruct H1.
      exists x. exists x0. exists x1.
      split.
      simpl. right. auto.
      split.
      simpl. right. auto.
      auto.
      destruct H0.
      destruct H0.
      exists va0. exists va1. exists x.
      split.
      simpl. left. auto.
      split.
      simpl. right. auto.
      auto.
  + repeat destruct H.
    destruct H0.
    unfold is_consistent.
    intuition.
    specialize (H2 (assign_cons x x0) (assign_cons x x1)).
    simpl in H2.
    apply H1.
    apply H2 ; auto.
Qed.

Lemma is_consistent_one_less : forall a0 a1 cert,
  is_consistent (a0 :: a1 :: cert) ->
  is_consistent (a0 :: cert).
Proof.
  intros a0 a1 cert H.
  unfold is_consistent in *.
  intros.
  destruct assign1.
  destruct assign2.
  intros.
  specialize (H (assign_cons v0 v1)).
  specialize (H (assign_cons v2 v3)).
  simpl in H.
  apply H ; auto.
  inversion H0.
  left. auto.
  right. right. auto.
  inversion H1.
  left. auto.
  right. right. auto.
Qed.

Lemma is_alwayss: forall a0 cert,
  is_consistent (a0 :: cert) -> is_always a0 cert = true.
Proof.
  intros.
  destruct a0.
  induction cert.
  + auto.
  + simpl.
    assert (H' := H).
    apply is_consistent_one_less in H.
    apply IHcert in H.
    rewrite H in *.
    destruct a0.
    assert ({v0 = v2} + {v0 <> v2}).
    apply var_eq_dec.
    destruct H0.
      rewrite e in *.
      unfold var_beq.
      destruct (var_eq_dec v2 v2).
      unfold is_consistent in H'.
      assert (v1 = v3).
      specialize (H' (assign_cons v2 v1)).
      specialize (H' (assign_cons v2 v3)).
      simpl in H'.
      apply H' ; auto.
      rewrite H0.
      unfold val_beq.
      destruct (val_eq_dec v3 v3).
      auto.
      intuition.
      intuition.
    
      unfold var_beq.
      destruct (var_eq_dec v0 v2).
      intuition.
      reflexivity.
Qed.

Lemma is_alwayssss : forall v2 v1 a0 cert,
  is_always (assign_cons v2 v1) (a0 :: cert) = true ->
  is_always (assign_cons v2 v1) cert = true.
Proof.
  intros v2 v1 a0 cert H.
  simpl in H.
  destruct a0.
  unfold var_beq in H.
  unfold val_beq in H.
  destruct (var_eq_dec v2 v0) in H.
  destruct (val_eq_dec v1 v3) in H.
  apply andb_true_iff in H.
  destruct H ; auto.
  apply andb_true_iff in H.
  destruct H. inversion H.
  auto.
Qed.

Lemma is_alwaysss : forall v2 v1 v3 cert,
  is_always (assign_cons v2 v1) cert = true ->
  In (assign_cons v2 v3) cert ->
  v1 = v3.
Proof.
  intros v2 v1 v3 cert H H0.
  induction cert.
  + inversion H0.
  + assert (H' := H).
    assert (is_always (assign_cons v2 v1) cert = true).
    apply is_alwayssss in H ; auto.
    inversion H0.
    - rewrite H2 in *.
      simpl in H.
      unfold var_beq in H.
      destruct (var_eq_dec v2 v2).
      apply andb_true_iff in H.
        destruct H.
        unfold val_beq in H.
        destruct (val_eq_dec v1 v3).
        auto.
        inversion H.
        intuition.
    - apply IHcert in H1 ; auto.
Qed.

Lemma check_ass_list_works : forall (cert : Certificate),
  (check_ass_list cert) = true <-> is_consistent cert.
Proof.
  intros cert.
  induction cert.
  + unfold is_consistent.
    simpl.
    intuition.
    destruct assign1.
    destruct assign2.
    intuition.
  + split ; intros.
    - assert (check_ass_list cert = true).
      simpl in H.
      apply andb_true_iff in H.
      destruct H.
      auto.
      apply IHcert in H0.
      unfold is_consistent.
      destruct assign1.
      destruct assign2.
      intros.
      inversion H1.
        inversion H2.
          rewrite H5 in H4.
          apply <- Assignment_eq_dec3 in H4.
          destruct H4 ; auto.
          unfold check_ass_list in H.
          apply andb_true_iff in H.
          destruct H.
          rewrite H4 in *.
          rewrite H3 in *.
          apply (is_alwaysss v2 v1 v3 cert) ; auto.
        inversion H2.
          unfold check_ass_list in H.
          apply andb_true_iff in H.
          destruct H.
          rewrite H3 in *.
          rewrite H5 in *.
          symmetry.
          apply (is_alwaysss v2 v3 v1 cert) ; auto.
          unfold is_consistent in H0.
          rewrite H3 in *.
          specialize (H0 (assign_cons v2 v1) (assign_cons v2 v3)).
          simpl in H0.
          apply H0 ; auto.
    - assert (check_ass_list cert = true).
      apply IHcert.
      unfold is_consistent in *.
      intros.
      specialize (H assign1 assign2).
      destruct assign1.
      destruct assign2.
      intros.
      apply H ; auto.
      simpl ; right ; auto.
      simpl ; right ; auto.
      simpl.
      rewrite H0.
      assert (is_always a0 cert = true).
      apply is_alwayss.
      auto.
      rewrite H1.
      auto.
Qed.




End Help_Lemmata.