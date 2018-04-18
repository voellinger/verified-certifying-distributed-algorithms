
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
(* Load Spanning_Tree_related. *)

Section ConnectedChecker.


(* All components are already indexed by natural numbers via GraphBasics. *)
Definition Component_Index := nat.
(* A distance for how long a message has traveled to the recipient. *)
Definition Distance := nat.


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

(* This is the content of a message. It consists of a list of:
  - variables
  - assignment of the variable

  The same variable/assignment pair could be in there multiple times, as could be variables assigned to different values.
*)
Definition Msg := Certificate.

Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
Proof.
  intro x.
  induction x ; intros.
  - induction y.
    + left ; auto.
    + right.
      unfold not ; intros.
      inversion H.
  - induction y.
    + right.
      unfold not ; intros.
      inversion H.
    + specialize (IHx y).
      assert ({a0 = a1} + {a0 <> a1}).
      apply Assignment_eq_dec.
      destruct IHx.
        rewrite e.
        destruct H.
          rewrite e0.
          left ; auto.
          right.
          apply list_not_equals ; auto.
        right.
        apply list_not_equals ; auto.
Qed.


Variable parent : Name -> Name.
Variable children : Name -> list Name.
Variable root : Name.

Axiom root_prop : v (name_component root).

Axiom root_own_parent : parent root = root.

Axiom parent_children : forall (p c : Name),
  In c (children p) -> parent c = p.

Axiom children_parent : forall (c : Name),
  {In c (children (parent c))} + {c = root}.

Axiom c_arcs : forall (p c : Name),
  In c (children p) -> a (A_ends (name_component p) (name_component c)).

Axiom p_arcs : forall (c : Name),
  {a (A_ends (name_component c) (name_component (parent c)))} + {c = root}.

Definition parent_walk (x y : Component) (vl : V_list) (el : E_list) (w : Walk v a x y vl el) :=
  forall (c1 c2 : Name), In (E_ends (name_component c1) (name_component c2)) el -> parent c1 = c2.

Axiom parent_walk_to_root : forall (c : Name),
  {vl : V_list & {el : E_list & {w : Walk v a (name_component c) (name_component root) vl el & parent_walk (name_component c) (name_component root) vl el w}}}.

Definition descendand (des ancestor : Name) : Set :=
  {vl : V_list & {el : E_list & {w : Walk v a (name_component des) (name_component ancestor) vl el & parent_walk (name_component des) (name_component ancestor) vl el w}}}.

(* 

Fixpoint descendands (ancestor : Name) (child_list : list Name) : list Name :=
  match child_list with
  | [] => [ancestor]
  | hd :: tl => (descendands hd (children hd)) ++ (descendands ancestor tl)
  end. 

kann man auch \u00fcber parent_walk definieren

*)

Record Data := mkData{
  checkerknowledge: Checkerknowledge; 
  checkerinput : Checkerinput;
  ass_list : Certificate;
  terminated : bool;
  consistent : bool;
  child_list : list Name
}.

(* initialization of the network *)
Definition init_Data (me: Name) := 
  mkData (init_Checkerknowledge me)
         (init_Checkerinput me)
         (certificate (init_Checkerinput me))
         false
         true
         (children me).


(* This input starts a checker *)
Inductive Input := alg_terminated : Input.

(* kann weggelassen werden? *)
Definition Output := bool.



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
        destruct H4.
          apply <- Assignment_eq_dec3 in H4. destruct H4. subst.
          destruct H5.
            apply <- Assignment_eq_dec3 in H4. destruct H4. auto.
            destruct H4.
              apply <- Assignment_eq_dec3 in H4. destruct H4. subst.
              intuition.
              unfold is_consistent in H1.
              apply (H1 (assign_cons v4 v3) (assign_cons v4 v5)) ; auto.
              simpl. left. auto.
              simpl. right. auto.
          destruct H4.
            apply <- Assignment_eq_dec3 in H4. destruct H4. subst.
            destruct H5.
              apply <- Assignment_eq_dec3 in H4. destruct H4. subst.
              intuition.
              destruct H4.
                apply <- Assignment_eq_dec3 in H4. destruct H4. auto.
                unfold is_consistent in new.
                apply (new (assign_cons v4 v3) (assign_cons v4 v5)) ; auto.
                simpl. left. auto.
                simpl. right. auto.
            destruct H5.
            apply <- Assignment_eq_dec3 in H5. destruct H5. subst.
            apply (H1 (assign_cons v4 v3) (assign_cons v4 v5)) ; auto.
            simpl. right. auto.
            simpl. left. auto.
            destruct H5.
            apply <- Assignment_eq_dec3 in H5. destruct H5. subst.
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
        inversion H4.
          apply <- Assignment_eq_dec3 in H0.
          destruct H0.
          subst.
          inversion H5.
            apply <- Assignment_eq_dec3 in H0.
            destruct H0.
            subst.
            auto.
            inversion H0.
              apply <- Assignment_eq_dec3 in H6.
              destruct H6. subst. auto.
              unfold is_consistent in H1.
              apply (H1 (assign_cons v4 v3) (assign_cons v4 v5)) ; auto.
              simpl. left. auto.
            simpl. right. auto.
          inversion H0.
            apply <- Assignment_eq_dec3 in H6.
            destruct H6.
            subst.
            inversion H5.
              apply <- Assignment_eq_dec3 in H6.
              destruct H6.
              auto.
              inversion H6.
              apply <- Assignment_eq_dec3 in H7.
              destruct H7. auto.
            unfold is_consistent in new.
            apply (new (assign_cons v4 v3) (assign_cons v4 v5)) ; auto.
          inversion H5.
          apply <- Assignment_eq_dec3 in H7. destruct H7. subst.
          unfold is_consistent in H1.
          apply (H1 (assign_cons v4 v3) (assign_cons v4 v5)) ; auto.
          simpl. right. auto.
          simpl. left. auto.
          inversion H7.
          apply <- Assignment_eq_dec3 in H8. destruct H8. subst.
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


(* Sendet zu Beginn hoch, falls *me* ein Blatt ist *)
Definition InputHandler (me : Name) (c : Input) (state: Data) :
            (list Output) * Data * list (Name * Msg) :=
  if (eqb (terminated state) true) then
  ([] , (mkData
            (checkerknowledge state)
            (checkerinput state)
            (ass_list state)
            (terminated state)
            (consistent state)
            (child_list state)),
      [])
  else
	match (child_list state) with
  | [] => 
    ([true] , (mkData
            (checkerknowledge state)
            (checkerinput state)
            (ass_list state)
            (true)
            (check_ass_list (ass_list state))
            (child_list state)),
      [(parent me, (ass_list state))])
  | _ =>
    ([] , (mkData
            (checkerknowledge state)
            (checkerinput state)
            (ass_list state)
            (terminated state)
            (consistent state)
            (child_list state)),
      [])
  end.


Definition NetHandler (me : Name) (src: Name) (child_cert : Msg) (state: Data) :
    (list Output) * Data * list (Name * Msg) :=
  if (eqb (terminated state) true) then
  ([] , (mkData
            (checkerknowledge state)
            (checkerinput state)
            (ass_list state)
            (terminated state)
            (consistent state)
            (child_list state)),
      [])
  else
  match (child_list state) with
  | [] =>
    ([] , (mkData
            (checkerknowledge state)
            (checkerinput state)
            (ass_list state)
            (terminated state)
            (consistent state)
            (child_list state)),
      [])
  | [c] =>
    ([check_ass_list ((ass_list state) ++ child_cert)] , (mkData
            (checkerknowledge state)
            (checkerinput state)
            ((ass_list state) ++ child_cert)
            (true)
            (check_ass_list ((ass_list state) ++ child_cert))
            ([])),
      [(parent me, (ass_list state))])
  | _ =>
    ([] , (mkData
            (checkerknowledge state)
            (checkerinput state)
            ((ass_list state) ++ child_cert)
            (terminated state)
            (consistent state)
            (remove_src src (child_list state))),
      [])
  end.


Lemma W_endx_inv :
 forall (v : V_set) (a : A_set) (x y : Vertex) (vl : V_list) (el : E_list), Walk v a x y vl el -> v x.
Proof.
        intros v a x y vl el w; elim w; auto.
Qed.

Lemma W_endy_inv :
 forall (v : V_set) (a : A_set) (x y : Vertex) (vl : V_list) (el : E_list), Walk v a x y vl el -> v y.
Proof.
        intros v a x y vl el w; elim w; auto.
Qed.

Lemma W_invl_inv :
 forall (v : V_set) (a : A_set) (x y : Vertex) (vl : V_list) (el : E_list),
 Walk v a x y vl el -> forall z : Vertex, In z vl -> v z.
Proof.
        intros v a x y vl el w; elim w; intros.
        inversion H.

        inversion H0.
        rewrite <- H1; apply (W_endx_inv _ _ _ _ _ _ w0).

        auto.
Qed.

Lemma W_iny_vl :
 forall (v : V_set) (a : A_set) (x y : Vertex) (vl : V_list) (el : E_list),
 Walk v a x y vl el -> vl <> V_nil -> In y vl.
Proof.
        intros v a x y vl el w; elim w; intros.
        absurd (V_nil = V_nil); auto.

        inversion w0.
        simpl; auto.

        rewrite H6; simpl; right.
        apply H; rewrite <- H6; discriminate.
Qed.

Fixpoint varList_has_varb (vl : list Var) (v : Var) : bool :=
  match vl with
  | nil => false
  | hd :: tl => var_beq hd v && varList_has_varb tl v
  end.

Definition varList_has_var (vl : list Var) (v : Var) : Prop :=
  varList_has_varb vl v = true.

Definition isa_aVarComponent (aVar : Var) (c : Name) : Prop :=
  varList_has_var (init_var_l c) aVar.

Variable null_Value : Value.

Fixpoint valueOfa (aVar : Var) (cert : list Assignment) : Value :=
  match cert with
  | [] => null_Value
  | hd :: tl => let (var, val) := hd in if var_beq var aVar then val else valueOfa aVar tl
  end.

Definition valueOf (aVar : Var) (c : Name) : Value :=
  valueOfa aVar (init_certificate c).

Definition Witness_consistent : Prop :=
  forall (c1 c2 : Name) (a : Var), v (name_component c1) -> v (name_component c2) -> isa_aVarComponent a c1 -> isa_aVarComponent a c2 -> valueOf a c1 = valueOf a c2.

Definition descendand_r (d : Name) : Set :=
  {vl : V_list & {el : E_list & {w : Walk v a (name_component d) (name_component root) vl el & parent_walk (name_component d) (name_component root) vl el w}}}.

Definition root_subtree_consistent :=
  forall a d1 d2, descendand_r d1 -> descendand_r d2 -> isa_aVarComponent a d1 -> isa_aVarComponent a d2 -> valueOf a d1 = valueOf a d2.

Lemma Witness_consistent_root_subtree_consistent :
  Witness_consistent <-> root_subtree_consistent.
Proof.
  unfold Witness_consistent. unfold root_subtree_consistent.
  split ; intros.
  + unfold descendand in *.
    destruct H0.
    destruct s. destruct s.
    destruct H1.
    destruct s. destruct s.
    assert (x1' := x1).
    apply W_endx_inv in x1'.
    assert (x4' := x4).
    apply W_endx_inv in x4'.
    apply (H d1 d2 a0) ; auto.
  + apply (H a0 c1 c2) ; auto ; unfold descendand.
    apply (parent_walk_to_root c1) ; auto.
    apply (parent_walk_to_root c2) ; auto.
Qed.

Lemma root_descendand : 
  descendand_r root.
Proof.
  unfold descendand.
  exists V_nil.
  exists E_nil.
  assert (Walk v a (name_component root) (name_component root) V_nil E_nil).
  apply W_null ; auto.
  apply root_prop.
  exists H.
  unfold parent_walk.
  intros.
  inversion H0.
Qed.


Instance Checker_BaseParams : BaseParams :=
  {
    data := Data;
    input := Input;
    output := Output
  }.

Instance Checker_MultiParams : MultiParams Checker_BaseParams :=
  {
    name := Name;
    name_eq_dec := Name_eq_dec;
    msg := Msg;
    msg_eq_dec := Msg_eq_dec;
    nodes := Nodes a v g;
    all_names_nodes := all_Names_Nodes a v g;
    no_dup_nodes := NoDup_Nodes a v g;
    init_handlers := init_Data; 
    input_handlers := InputHandler ;
    net_handlers := NetHandler
    }.


Lemma terminated_means_no_change: forall net net2 tr c,
  (nwState net (Checker c)).(terminated) = true ->
  step_async_star (params := Checker_MultiParams) net net2 tr ->
  nwState net2 (Checker c) = nwState net (Checker c).
Proof.
  intros net net2 tr c H0 H1.
  induction H1 using refl_trans_1n_trace_n1_ind.
  - auto.
  - assert (nwState x' (Checker c) = nwState x (Checker c)) ; auto.
    invc H.
    + simpl in *.
      unfold NetHandler in H3.
      destruct (Name_eq_dec (Checker c) (pDst p)).
      rewrite <- e in *.
      rewrite H1 in *.
      rewrite H0 in *.
      simpl in *.
      inversion H3.
      rewrite <- H0.
      destruct (nwState x (Checker c)). 
      auto.
      auto.
    + simpl in *.
      unfold InputHandler in H2.
      destruct (Name_eq_dec (Checker c) h).
      rewrite <- e in *.
      rewrite H1 in *.
      rewrite H0 in *.
      simpl in *.
      inversion H2.
      rewrite <- H0.
      destruct (nwState x (Checker c)). 
      auto.
      auto.
Qed.

Lemma terminated_means_no_change_global: forall net net2 tr c,
  (forall (c : Component), (nwState net (Checker c)).(terminated) = true) ->
  step_async_star (params := Checker_MultiParams) net net2 tr ->
  nwState net2 (Checker c) = nwState net (Checker c).
Proof.
  intros net net2 tr c H0 H1.
  apply (terminated_means_no_change net net2 tr c) ; auto.
Qed.

Lemma Drei_zwei' : forall c,
  is_consistent (nwState step_async_init (Checker c)).(ass_list).
Proof.
  intros c.
  simpl.
  apply init_certificate_is_consistent.
Qed.

Lemma Drei_zwei'' : forall net tr c,
  step_async_star (params := Checker_MultiParams) step_async_init net tr ->
  (is_consistent (nwState net (Checker c)).(ass_list)) ->
  (nwState net (Checker c)).(consistent) = true.
Proof.
  intros net tr c H H0.
  remember step_async_init as y in *.
  assert (is_consistent (nwState step_async_init (Checker c)).(ass_list)) as new.
  apply Drei_zwei'.
  induction H using refl_trans_1n_trace_n1_ind.
  + subst.
    simpl in *.
    reflexivity.
  + subst.
    simpl in *.
    assert (is_consistent (ass_list (nwState x' (Checker c)))).
    assert (exists xyz: Certificate, ass_list (nwState x'' (Checker c)) = ass_list (nwState x' (Checker c)) ++ xyz).
    {invc H1.
    - simpl in *.
      unfold NetHandler in H4.
      repeat break_match.
      rewrite e in *. exists []. inversion H4. simpl. rewrite app_nil_r. auto.
      rewrite e in *. exists []. inversion H4. simpl. rewrite app_nil_r. auto.
      rewrite e in *. exists (pBody p). inversion H4. simpl. auto.
      rewrite e in *. exists (pBody p). inversion H4. simpl. auto.
      exists []. rewrite app_nil_r. auto.
      exists []. rewrite app_nil_r. auto.
      exists []. rewrite app_nil_r. auto.
      exists []. rewrite app_nil_r. auto.
    - simpl in *.
      unfold InputHandler in H3.
      repeat break_match.
      rewrite e in *. inversion H3. simpl. exists []. rewrite app_nil_r. auto.
      rewrite e in *. inversion H3. simpl. exists []. rewrite app_nil_r. auto.
      rewrite e in *. inversion H3. simpl. exists []. rewrite app_nil_r. auto.
      exists []. rewrite app_nil_r. auto.
      exists []. rewrite app_nil_r. auto.
      exists []. rewrite app_nil_r. auto. }

    destruct H3.
    rewrite H3 in H0.
    apply is_consistent_in_parts in H0.
    destruct H0.
    auto.
    assert (consistent (nwState x' (Checker c)) = true).
    apply IHrefl_trans_1n_trace1 ; auto.

    invc H1.
    - simpl in *.
      unfold NetHandler in H6.
      repeat break_match.
        rewrite <- e in *. inversion H6. rewrite H4 in *. reflexivity.
        rewrite <- e in *. inversion H6. rewrite H4 in *. reflexivity.
        rewrite <- e in *. inversion H6. simpl. 
          assert (ass_list d = ass_list (nwState x' (Checker c)) ++ pBody p). rewrite <- H8. auto.
          rewrite H1 in H0. apply <- check_ass_list_works in H0. auto.
        rewrite <- e in *. inversion H6. rewrite H4 in *. reflexivity.
        auto.
        auto.
        auto.
        auto.
    - simpl in *.
      unfold InputHandler in H5.
      repeat break_match.
        inversion H5. rewrite <- e in *. auto.
        apply <- check_ass_list_works in H0. rewrite <- e in *. inversion H5. simpl in *.
          assert (ass_list d = ass_list (nwState x' (Checker c))). rewrite <- H7. auto.
          rewrite <- H1. auto.
        inversion H5. rewrite <- e in *. auto.
        auto.
        auto.
        auto.
Qed.

Lemma Drei_zwei : forall net tr c,
  (nwState net (Checker c)).(terminated) = true ->
  step_async_star (params := Checker_MultiParams) step_async_init net tr ->
  ((nwState net (Checker c)).(consistent) = true ->
  is_consistent (nwState net (Checker c)).(ass_list)).
Proof.
  intros net tr c H H1.

  {
  unfold is_consistent.
  destruct assign1. destruct assign2.
  intros.
  remember step_async_init as y in *.
  assert (is_consistent (ass_list (nwState step_async_init (Checker c)))) as H19.
  simpl.
  apply init_certificate_is_consistent.
  induction H1 using refl_trans_1n_trace_n1_ind.
  + subst.
    simpl in H.
    inversion H.
  + subst.
    invc H1.
    - simpl in *.
      unfold NetHandler in H5.
      assert ({Checker c = pDst p} + {Checker c <> pDst p}).
      apply Name_eq_dec.
      destruct H1.
        rewrite <- e in *.
        destruct (Name_eq_dec (Checker c) (Checker c)).
        destruct ((terminated (nwState x' (Checker c)))).
        simpl in H5.
        inversion H5.
        rewrite <- H8 in *.
        rewrite <- H6 in *.
        simpl in *.
        assert (ass_list d = ass_list (nwState x' (Checker c))).
        rewrite <- H7.
        destruct ((nwState x' (Checker c))) ; auto.
        assert (consistent (nwState x' (Checker c)) = true).
        destruct d.
        simpl in H0.
        rewrite H0 in H7.
        inversion H7.
        auto.
        apply IHrefl_trans_1n_trace1 ; auto.
        rewrite H1 in *.
        auto.
        rewrite H1 in *.
        auto.
        simpl in H5.
        break_match.
        inversion H5.
        destruct d.
        simpl in H.
        inversion H7.
        rewrite H in H12.
        inversion H12.
        break_match.
          inversion H5.
          destruct d.
          inversion H7.
          simpl in *.
          rewrite H0 in *.
          rewrite H in *.
          apply check_ass_list_works in H13.
          rewrite H11 in *.
          unfold is_consistent in H13.
          apply (H13 (assign_cons v2 v1) (assign_cons v2 v3)) ; auto.

          destruct d.
          simpl in H.
          inversion H5.
          rewrite H in H10.
          inversion H10.
          intuition.

        destruct (Name_eq_dec (Checker c) (pDst p)).
        intuition.
        apply IHrefl_trans_1n_trace1 ; auto.
    - simpl in *.
      unfold InputHandler in H4.
      assert ({Checker c = h} + {Checker c <> h}).
      apply Name_eq_dec.
      destruct H1.
        rewrite <- e in *.
        destruct (Name_eq_dec (Checker c) (Checker c)).
        destruct (terminated (nwState x' (Checker c))).
        simpl in H4.
        inversion H4.
        destruct d.
        inversion H6.
        simpl in H0.
        rewrite H0 in *.
        simpl in H.
        rewrite H in *.
        simpl in H2.
        rewrite H10 in *.
        apply IHrefl_trans_1n_trace1 ; auto.
        simpl in H4.
        break_match.
          inversion H4.
          destruct d.
          inversion H6.
          simpl in H0.
          rewrite H0 in *.
          simpl in H.
          rewrite H in *.
          simpl in H3.
          simpl in H2.
          rewrite H8 in *.
          rewrite H9 in *.
          rewrite H10 in *.
          rewrite <- H13 in *.
          simpl in *.
          apply check_ass_list_works in H12.
          unfold is_consistent in H12.
          apply (H12 (assign_cons v2 v1) (assign_cons v2 v3)) ; auto.

          inversion H4.
          destruct d.
          inversion H6.
          simpl in H.
          rewrite H in H11.
          inversion H11.
        intuition.
        destruct (Name_eq_dec (Checker c) h).
        intuition.
        apply IHrefl_trans_1n_trace1 ; auto.
  }
Qed.



Lemma Drei_zwei''' : forall net tr c,
  (nwState net (Checker c)).(consistent) = false ->
  step_async_star (params := Checker_MultiParams) step_async_init net tr ->
  ~ is_consistent (nwState net (Checker c)).(ass_list).
Proof.
  intros net tr c H H0.
  remember step_async_init as y in *.
  induction H0 using refl_trans_1n_trace_n1_ind.
  + subst.
    intuition.
  + subst. simpl in *.
    assert (exists xyz: Certificate, ass_list (nwState x'' (Checker c)) = ass_list (nwState x' (Checker c)) ++ xyz).
    {invc H0.
    - simpl in *.
      unfold NetHandler in H2.
      repeat break_match.
      rewrite e in *. exists []. inversion H2. simpl. rewrite app_nil_r. auto.
      rewrite e in *. exists []. inversion H2. simpl. rewrite app_nil_r. auto.
      rewrite e in *. exists (pBody p). inversion H2. simpl. auto.
      rewrite e in *. exists (pBody p). inversion H2. simpl. auto.
      exists []. rewrite app_nil_r. auto.
      exists []. rewrite app_nil_r. auto.
      exists []. rewrite app_nil_r. auto.
      exists []. rewrite app_nil_r. auto.
    - simpl in *.
      unfold InputHandler in H1.
      repeat break_match.
      rewrite e in *. inversion H1. simpl. exists []. rewrite app_nil_r. auto.
      rewrite e in *. inversion H1. simpl. exists []. rewrite app_nil_r. auto.
      rewrite e in *. inversion H1. simpl. exists []. rewrite app_nil_r. auto.
      exists []. rewrite app_nil_r. auto.
      exists []. rewrite app_nil_r. auto.
      exists []. rewrite app_nil_r. auto. }
    destruct H1.
    rewrite H1 in *.
    intuition.
    assert (H2' := H2).
    apply is_consistent_in_parts in H2.
    destruct H2.
    apply (Drei_zwei'' x' tr1) in H2 ; auto.
    invc H0.
    - simpl in *.
      unfold NetHandler in H5.
      repeat break_match.
        rewrite <- e in *. inversion H5. rewrite <- H7 in H. simpl in *. apply (eq_true_false_abs (consistent (nwState x' (Checker c))) H2 H).
        apply (eq_true_false_abs (consistent (nwState x' (Checker c))) H2 H).
        rewrite <- e in *. inversion H5. rewrite <- H7 in H. simpl in *. apply (eq_true_false_abs (consistent (nwState x' (Checker c))) H2 H).
        apply (eq_true_false_abs (consistent (nwState x' (Checker c))) H2 H).
        rewrite <- e in *. inversion H5. rewrite <- H7 in H. rewrite <- H7 in H1. simpl in *. 
        apply app_inv_head in H1. rewrite H1 in *. apply check_ass_list_works in H2'.
        apply (eq_true_false_abs (check_ass_list (ass_list (nwState x' (Checker c)) ++ x)) H2' H).
        apply (eq_true_false_abs (consistent (nwState x' (Checker c))) H2 H).
        rewrite <- e in*. inversion H5. rewrite <- H7 in H. simpl in *. 
        apply (eq_true_false_abs (consistent (nwState x' (Checker c))) H2 H).
        apply (eq_true_false_abs (consistent (nwState x' (Checker c))) H2 H).
    - simpl in *.
      unfold InputHandler in H4.
      repeat break_match.
        rewrite <- e in *. inversion H4. rewrite <- H6 in H. simpl in *.
        apply (eq_true_false_abs (consistent (nwState x' (Checker c))) H2 H).
        apply (eq_true_false_abs (consistent (nwState x' (Checker c))) H2 H).
        rewrite <- e in *. inversion H4. rewrite <- H6 in H. simpl in *.
        apply is_consistent_in_parts in H2'. destruct H2'.
        apply <- check_ass_list_works in H0.
        apply (eq_true_false_abs (check_ass_list (ass_list (nwState x' (Checker c)))) H0 H).
        apply (eq_true_false_abs (consistent (nwState x' (Checker c))) H2 H).
        rewrite <- e in *. inversion H4. rewrite <- H6 in H. simpl in *.
        apply (eq_true_false_abs (consistent (nwState x' (Checker c))) H2 H).
        apply (eq_true_false_abs (consistent (nwState x' (Checker c))) H2 H).
Qed.

Lemma all_subtree_in_ass_list: forall net tr c,
  (nwState net (Checker c)).(terminated) = true ->
  step_async_star (params := Checker_MultiParams) step_async_init net tr ->
  (forall d, descendand (component_name d) (component_name c) -> 
    (forall e, In e (nwState net (Checker d)).(ass_list) -> In e (nwState net (Checker c)).(ass_list))).
Proof.
  intros.
Admitted.

Lemma has_var_exists_val : forall var d,
  isa_aVarComponent var d -> exists val : Value, In (assign_cons var val) (init_certificate d).
Proof.
  intros var d H.
  unfold isa_aVarComponent in H.
  assert (In var (init_var_l d)).
  - unfold varList_has_var in H.
    unfold varList_has_varb in H.
    induction (init_var_l d).
    + inversion H.
    + simpl in *.
      repeat break_match.
      apply andb_prop in H.
      destruct H.
      unfold var_beq in H.
      repeat break_match.
      left. auto.
      inversion H.
  - apply init_var_l_init_certificate in H0.
    apply H0.
Qed.

Lemma is_in_cons_cert_then_take_it : forall var val d,
  In (assign_cons var val) (init_certificate d) -> valueOf var d = val.
Proof.
  intros var val d H.
  assert (is_consistent (init_certificate d)).
  apply init_certificate_is_consistent.
  unfold valueOf.
  induction (init_certificate d).
  + inversion H.
  + simpl in *.
    destruct H.
    - rewrite H in *.
      unfold var_beq.
      repeat break_match ; auto.
      inversion Heqb.
      intuition.
    - destruct a0.
      assert (H0' := H0).
      apply is_consistent_one_lesss in H0.
      assert (valueOfa var l = val).
      apply IHl ; auto.
      repeat break_match ; auto.
      unfold var_beq in Heqb.
      break_match.
      rewrite e in *.
      unfold is_consistent in H0'.
      apply (H0' (assign_cons var v1) (assign_cons var val)) ; auto.
      simpl. left. auto.
      simpl. right. auto.
      inversion Heqb.
Qed.


Lemma cert_stays_in_ass_list : forall net tr c a,
  step_async_star step_async_init net tr ->
  In a (init_certificate c) ->
  In a (ass_list (nwState net (Checker (name_component c)))).
Proof.
  intros net tr c a reachable genesis.
Admitted.

Theorem root_ends_true_witness_consistent: forall net tr,
  (nwState net (Checker (name_component root))).(consistent) = true ->
  (nwState net (Checker (name_component root))).(terminated) = true ->
  step_async_star (params := Checker_MultiParams) step_async_init net tr ->
  Witness_consistent.
Proof.
  intros net tr cons term reachable.
  apply Witness_consistent_root_subtree_consistent.
  unfold root_subtree_consistent.
  intros.
  assert (forall d, descendand (component_name d) (root) -> 
    (forall e, In e (nwState net (Checker d)).(ass_list) -> In e (nwState net (Checker (name_component root))).(ass_list))).
  apply (all_subtree_in_ass_list net tr) ; auto.
  rename H3 into Hd.
  assert (forall e : Assignment,
     In e (ass_list (nwState net (Checker (name_component d1)))) ->
     In e (ass_list (nwState net (Checker (name_component root))))).
  apply (Hd (name_component d1)) ; auto.
  assert (forall e : Assignment,
     In e (ass_list (nwState net (Checker (name_component d2)))) ->
     In e (ass_list (nwState net (Checker (name_component root))))).
  apply (Hd (name_component d2)) ; auto.
  assert (is_consistent (nwState net (Checker (name_component root))).(ass_list)).
  apply (Drei_zwei net tr) ; auto.
  unfold is_consistent in H5.
  clear Hd.

  apply has_var_exists_val in H1.
  apply has_var_exists_val in H2.
  destruct H1 as [val1 H1].
  destruct H2 as [val2 H2].
  assert (Hd1 := H1).
  assert (Hd2 := H2).
  apply (is_in_cons_cert_then_take_it a0 val1) in H1.
  apply (is_in_cons_cert_then_take_it a0 val2) in H2.
  rewrite H1.
  rewrite H2.
  apply (H5 (assign_cons a0 val1) (assign_cons a0 val2)) ; auto.
  apply H3 ; auto.
  apply (cert_stays_in_ass_list net tr) ; auto.
  apply H4 ; auto.
  apply (cert_stays_in_ass_list net tr) ; auto.
Qed.


Axiom everything_ends : forall c net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr ->
  {net2 : network & {tr2 : list (Name * (Input + list Output)) & step_async_star (params := Checker_MultiParams) step_async_init net tr /\
  (nwState net2 (Checker c)).(terminated) = true}}.

Axiom every_step_is_towards_an_end : forall c net tr,
 .

x1. wenn Zustand terminated erreicht (true), dann bleibt er immer true (vllt NetHandler anpassen daf\u00fcr, indem am Anfang abgefragt wird, ob schon terminated)
x2. wenn terminated, dann \u00e4ndert sich consistent nicht mehr            (vllt NetHandler anpassen daf\u00fcr, indem am Anfang abgefragt wird, ob schon terminated)
3. wenn terminated, dann 
  i. sind alle Belegungen der Variablen des Teilbaums in der ass_list
  xii. wenn consistent, dann sind alle Variablen der ass_list sind gleichbelegt
  -> der gesamte Teilbaum hat eine konsistente Belegung
  xiii. wenn nicht consistent, dann existiert eine Variable in der ass_list, die zwei verschiedene Belegungen hat
  -> es existieren zwei Komponenten im Teilbaum, die f\u00fcr eine Variable verschiedene Belegungen haben
x5. wenn alle Variablen im Teilbaum von root gleichbelegt sind, dann ist der Zeuge konsistent
  (weil alle knoten des graphen im teilbaum von root sind)
6. wenn nicht alle Variablen im Teilbaum gleichbelegt sind, dann ist der Zeuge nicht konsistent


M\u00f6gliche Verbesserungen:
  1. bei Doppelbelegungen nur "false" nach oben reichen
  2. ansonsten nur eine Belegung je Variable nach oben reichen
  3. die erste if-abfrage im Nethandler streichen
  4. root braucht an niemanden senden, dann kann auch das erste Pattern weg
  5. entweder einen terminated state und consistent state, oder nur outputs

End ConnectedChecker.