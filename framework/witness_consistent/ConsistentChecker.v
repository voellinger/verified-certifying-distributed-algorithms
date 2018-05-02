
Require Import GraphBasics.Graphs.
Require Import Coq.Logic.Classical_Prop.
Require Import Verdi.Verdi.

Require Export StructTact.Fin.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Require Import Verdi.ExtrOcamlBasicExt.
Require Import Verdi.ExtrOcamlList.

Require Import FunInd.



(* Load Spanning_Tree_related. *)

Load New_Spanning_Tree_related.



Section Consistency_Checker.



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





Record Data := mkData{
  checkerknowledge: Checkerknowledge; 
  checkerinput : Checkerinput;
  ass_list : Certificate;
  terminated : bool;
  consistent : bool;
  child_list : list Name;
  children_d : list Name
}.

(* initialization of the network *)
Definition init_Data (me: Name) := 
  mkData (init_Checkerknowledge me)
         (init_Checkerinput me)
         (certificate (init_Checkerinput me))
         false
         true
         (children me)
         [].


(* This input starts a checker *)
Inductive Input := alg_terminated : Input.

(* kann weggelassen werden? *)
Definition Output := bool.





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
            (child_list state)
            (children_d state)),
      [])
  else
	match (children me) with
  | [] => 
    ([true] , (mkData
            (checkerknowledge state)
            (checkerinput state)
            (ass_list state)
            (true)
            (check_ass_list (ass_list state))
            (child_list state)
            (children_d state)),
      [(parent me, (ass_list state))])
  | _ =>
    ([] , (mkData
            (checkerknowledge state)
            (checkerinput state)
            (ass_list state)
            (terminated state)
            (consistent state)
            (child_list state)
            (children_d state)),
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
            (child_list state)
            (children_d state)),
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
            (child_list state)
            (children_d state)),
      [])
  | [c] =>
    ([check_ass_list ((ass_list state) ++ child_cert)] , (mkData
            (checkerknowledge state)
            (checkerinput state)
            ((ass_list state) ++ child_cert)
            (true)
            (check_ass_list ((ass_list state) ++ child_cert))
            ([])
            (src :: (children_d state))),
      [(parent me, (ass_list state ++ child_cert))])
  | _ =>
    ([] , (mkData
            (checkerknowledge state)
            (checkerinput state)
            ((ass_list state) ++ child_cert)
            (terminated state)
            (consistent state)
            (remove_src src (child_list state))
            (src :: (children_d state))),
      [])
  end.

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





Fixpoint varList_has_varb (vl : list Var) (v : Var) : bool :=
  match vl with
  | nil => false
  | hd :: tl => var_beq hd v || varList_has_varb tl v
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
      apply orb_prop in H.
      destruct H.
      unfold var_beq in H.
      repeat break_match.
      left. auto.
      inversion H.
      right.
      apply IHl ; auto.
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










Definition Witness_consistent : Prop :=
  forall (c1 c2 : Name) (a : Var), v (name_component c1) -> v (name_component c2) -> isa_aVarComponent a c1 -> isa_aVarComponent a c2 -> valueOf a c1 = valueOf a c2.

Definition descendand_r (d : Name) : Set :=
  exists (vl : V_list) (el : E_list) (w : Walk v a (name_component d) (name_component root) vl el), parent_walk (name_component d) (name_component root) vl el w.

Definition root_subtree_consistent :=
  forall a d1 d2, descendand_r d1 -> descendand_r d2 -> isa_aVarComponent a d1 -> isa_aVarComponent a d2 -> valueOf a d1 = valueOf a d2.

Lemma Witness_consistent_root_subtree_consistent :
  Witness_consistent <-> root_subtree_consistent.
Proof.
  unfold Witness_consistent. unfold root_subtree_consistent.
  split ; intros.
  + unfold descendand in *.
    repeat destruct H0.
    repeat destruct H1.
    assert (x1' := x1).
    apply W_endx_inv in x1'.
    assert (x4' := x4).
    apply W_endx_inv in x4'.
    apply (H d1 d2 a0) ; auto.
  + apply (H a0 c1 c2) ; auto ; unfold descendand_r.
    
    apply (parent_walk_to_root v a g c1) ; auto.
    apply (parent_walk_to_root v a g c2) ; auto.
Qed.

Lemma root_descendand : 
  descendand_r root.
Proof.
  unfold descendand.
  exists V_nil.
  exists E_nil.
  assert (Walk v a (name_component root) (name_component root) V_nil E_nil).
  apply W_null ; auto.
  apply root_prop_holds.
  exists H.
  unfold parent_walk.
  unfold parent_walk'.
  intros.
  inversion H0.
Qed.





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


Lemma cert_stays_in_ass_list : forall net tr c a,
  step_async_star step_async_init net tr ->
  In a (init_certificate c) ->
  In a (ass_list (nwState net (Checker (name_component c)))).
Proof.
  intros net tr c a reachable genesis.
  remember step_async_init as y in *.
  induction reachable using refl_trans_1n_trace_n1_ind.
  + subst.
    simpl.
    unfold name_component.
    break_match.
    auto.
  + subst.
    invc H ; simpl in *.
    - unfold NetHandler in H1.
      repeat break_match.
      inversion H1. rewrite <- e in *. simpl in *. apply IHreachable1 ; auto.
      rewrite <- e in *. inversion H1. simpl in *. apply IHreachable1 ; auto.
      rewrite <- e in *. inversion H1. simpl in *. apply in_or_app. left. apply IHreachable1 ; auto.
      rewrite <- e in *. inversion H1. simpl in *. apply in_or_app. left. apply IHreachable1 ; auto.
      apply IHreachable1 ; auto.
      apply IHreachable1 ; auto.
      apply IHreachable1 ; auto.
      apply IHreachable1 ; auto.
    - unfold InputHandler in H0.
      repeat break_match.
      rewrite <- e in *. inversion H0. simpl in *. apply IHreachable1 ; auto.
      rewrite <- e in *. inversion H0. simpl in *. apply IHreachable1 ; auto.
      rewrite <- e in *. inversion H0. simpl in *. apply IHreachable1 ; auto.
      apply IHreachable1 ; auto.
      apply IHreachable1 ; auto.
      apply IHreachable1 ; auto.
Qed.


Lemma Nethandler_nil_one: forall x' pDst pSrc pBody out d  l,
  NetHandler pDst pSrc pBody (nwState x' pDst) = (out, d, l) ->
  (l = [] \/ exists p, l = [p]).
Proof.
  intros.
  unfold NetHandler in H.
  repeat (break_match ; subst ; simpl in * ; inversion H ; auto).
  subst.
  right. exists (parent pDst, ass_list (nwState x' pDst) ++ pBody).
  auto.
Qed.

Lemma Nethandler_correct: forall x' p out d nextDst msg,
  NetHandler (pDst p) (pSrc p) (pBody p) (nwState x' (pDst p)) = (out, d, [(nextDst, msg)]) ->
  (parent (pDst p) = nextDst) /\ (msg = (ass_list (nwState x' (pDst p))) ++ pBody p).
Proof.
  intros.
  destruct p.
  unfold NetHandler in H.
  repeat (break_match ; subst ; simpl in * ; inversion H ; subst).
  auto.
Qed.

Lemma Inputhandler_nil_one : forall inp0 x' h out d l,
  InputHandler h inp0 (nwState x' h) = (out, d, l) ->
  (l = [] \/ exists p, l = [p]).
Proof.
  intros.
  unfold InputHandler in H.
  repeat (break_match ; subst ; simpl in * ; inversion H).
  auto.
  right.
  exists ((parent h, ass_list (nwState x' h))). auto.
  left. auto.
Qed.

Lemma Inputhandler_correct: forall inp0 x' h out d nextDst msg,
  InputHandler h inp0 (nwState x' h) = (out, d, [(nextDst, msg)]) ->
  (parent h = nextDst) /\ (msg = (ass_list (nwState x' h))).
Proof.
  intros.
  unfold InputHandler in H.
  repeat (break_match ; subst ; simpl in * ; inversion H).
  auto.
Qed.

Lemma only_child_in_ass_list: forall net tr c a,
  step_async_star (params := Checker_MultiParams) step_async_init net tr ->
  In a (ass_list (nwState net (Checker c))) -> exists d : Name, In d ((component_name c) :: (children (component_name c))) /\ In a (ass_list (nwState net d)).
Proof.
  intros.
 remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind.
  + subst.
    simpl in *.
    exists (component_name c).
    split ; auto.
  + subst.
    simpl in *.
    invc H1.
    - simpl in *.
      assert (H4' := H4).
      apply Nethandler_nil_one in H4'.
      destruct H4'.
      { subst.
        unfold NetHandler in H4.
        repeat (break_match ; subst ; simpl in * ; auto ; inversion H4 ; intuition ; subst ; intuition ; simpl in *).
        rewrite e in *. apply H1 in H0. destruct H0. exists x. destruct H0. split ; auto. break_match ; subst ; simpl ; auto.
        destruct H5. destruct H1. exists x. split ; auto. break_match ; subst ; simpl ; auto.
        rewrite e in *. apply H1 in H0. destruct H0. exists x. destruct H0. split ; auto. break_match ; subst ; simpl ; auto.
        destruct H6. destruct H1. exists x. split ; auto. break_match ; subst ; simpl ; auto.
        apply in_app_or in H0. destruct H0.
          exists (pDst p). split. left. unfold component_name. auto. break_match ; subst ; simpl ; auto. apply in_or_app. auto.
          exists (pDst p). split. left. unfold component_name. auto. break_match ; subst ; simpl ; auto. apply in_or_app. auto. intuition.
        destruct H6. destruct H1. exists x. split ; auto. break_match ; subst ; simpl ; auto. apply in_or_app. auto.
        apply in_app_or in H0. destruct H0.
          exists (pDst p). split. left. unfold component_name. auto. break_match ; subst ; simpl ; auto. apply in_or_app. auto.
          exists (pDst p). split. left. unfold component_name. auto. break_match ; subst ; simpl ; auto. apply in_or_app. auto. intuition.
        destruct H6. destruct H1. exists x. split ; auto. break_match ; subst ; simpl ; auto. apply in_or_app. auto.
        apply in_app_or in H0. destruct H0.
          exists (pDst p). split. left. unfold component_name. auto. break_match ; subst ; simpl ; auto. apply in_or_app. auto.
          exists (pDst p). split. left. unfold component_name. auto. break_match ; subst ; simpl ; auto. apply in_or_app. auto. intuition.
        destruct H6. destruct H1. exists x. split ; auto. break_match ; subst ; simpl ; auto. apply in_or_app. auto.
      }
      { destruct H1.
        subst.
        unfold NetHandler in H4.
        repeat (break_match ; subst ; simpl in * ; auto ; inversion H4 ; intuition).
        simpl in *.
        subst. apply in_app_or in H0.
        destruct H0.
        exists (pDst p). split. left. rewrite <- e. simpl. unfold component_name. auto.
        break_match. simpl. apply in_or_app. auto.
        auto.
        exists (pDst p). split. left. rewrite <- e. simpl. unfold component_name. auto.
        break_match. simpl. apply in_or_app. auto.
        intuition.

        simpl in *. subst.
        destruct H6.
        exists x.
        destruct H1.
        split ; auto.
        break_match ; simpl.
        subst. apply in_or_app. auto.
        auto.
      }
    - simpl in *.
      assert (H3' := H3).
      apply Inputhandler_nil_one in H3'.
      destruct H3'.
      { subst.
        unfold InputHandler in H3.
        repeat (break_match ; subst ; simpl in * ; auto ; inversion H3 ; intuition).
        destruct H4. destruct H1. exists x. split ; auto. break_match ; simpl.
          subst. auto. auto.
        destruct H4. destruct H1. exists x. split ; auto. break_match ; simpl.
          subst. auto. auto.
        destruct H5. destruct H1. exists x. split ; auto. break_match ; simpl.
          subst. auto. auto.
        destruct H5. destruct H1. exists x. split ; auto. break_match ; simpl.
          subst. auto. auto.
      }
      { destruct H1.
        subst.
        assert (H3' := H3).
        destruct x.
        apply Inputhandler_correct in H3'.
        destruct H3'.
        subst.
        unfold InputHandler in H3.
        repeat (break_match ; subst ; simpl in * ; auto ; inversion H3 ; intuition).
        destruct H5. destruct H1. exists x. split ; auto. break_match ; simpl.
          subst. auto. auto.
      destruct H5. destruct H1. exists x. split ; auto. break_match ; simpl.
          subst. auto. auto.
      }
Qed.



Lemma packets_work' : forall x tr,
  refl_trans_1n_trace step_async step_async_init x tr -> forall p,
  In p (nwPackets x) -> let (pSrc, pDst, pBody) := p in
  terminated (nwState x pSrc) = true.
Proof.
  intros x tr H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind ; intros ; subst ; simpl in *.
  + inversion H.
  + destruct p.
    intuition. specialize (H3 {| pSrc := pSrc; pDst := pDst; pBody := pBody |}).
    invc H0 ; simpl in *.
    - unfold NetHandler in H5.
      rewrite H4 in *.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H5 ; subst ; simpl in * ; intuition.
        apply eqb_prop in Heqb. auto.
        apply (silly_lemma packet p) in H2. intuition.
        apply (silly_lemma packet p) in H2. intuition.
        apply (silly_lemma packet p) in H2. intuition.
        apply (silly_lemma packet p) in H2. intuition.
        inversion H0. subst. intuition.
        apply (silly_lemma packet p) in H0. intuition.
        apply (silly_lemma packet p) in H2. intuition.
    - unfold InputHandler in H4.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H4 ; subst ; simpl in * ; intuition.
      inversion H0. subst. intuition.
Qed.

Lemma packets_work'wrap : forall x tr,
  refl_trans_1n_trace step_async step_async_init x tr -> forall (pSrc pDst : Name) pBody,
  In {| pSrc := pSrc; pDst := pDst; pBody := pBody |} (nwPackets x) -> 
  terminated (nwState x pSrc) = true.
Proof.
  intros.
  assert (forall x tr,
  refl_trans_1n_trace step_async step_async_init x tr -> forall p,
  In p (nwPackets x) -> let (pSrc, pDst, pBody) := p in
  terminated (nwState x pSrc) = true).
  apply (packets_work').
  specialize (H1 x tr H).
  specialize (H1 {| pSrc := pSrc; pDst := pDst; pBody := pBody |}).
  auto.
Qed.

Lemma silly_lemma2 : forall pSrc pDst pBody (p : packet) xs ys, 
  In p (xs ++ ys) -> In p (xs ++ {| pSrc := pSrc; pDst := pDst; pBody := pBody |} :: ys).
Proof.
  intros src dst bod p xs ys H.
  apply in_app_or in H.
  apply in_or_app.
  simpl.
  destruct H ; auto.
Qed.

Lemma packets_work'' : forall x tr,
  refl_trans_1n_trace step_async step_async_init x tr -> forall p,
  In p (nwPackets x) -> let (pSrc, pDst, pBody) := p in
  pDst = parent pSrc.
Proof.
  intros x tr H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind ; intros ; subst ; simpl in *.
  + inversion H.
  + assert (H2' := H2).
    apply (packets_work' x'' (tr1 ++ tr2)) in H2' ; auto.
    simpl in *.
    destruct p.
    simpl in *.
    invc H0 ; simpl in *.
    - rewrite H3 in *. intuition.
      assert (H0' := H0).
      specialize (H0 p).
      assert (let (pSrc, pDst, _) := p in pDst = parent pSrc).
      apply H0.
      apply in_or_app. right. simpl. auto.
      clear H0.
      specialize (H0' {| pSrc := pSrc; pDst := pDst; pBody := pBody |}).
      destruct p. simpl in *.
      unfold NetHandler in H4.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H4 ; subst ; simpl in * ; intuition.
      apply (silly_lemma2 pSrc0 (parent pSrc0) pBody0) in H2. intuition.
      apply (silly_lemma2 pSrc0 (parent pSrc0) pBody0) in H2. intuition.
      apply (silly_lemma2 pSrc0 (parent pSrc0) pBody0) in H2. intuition.
      apply (silly_lemma2 pSrc0 (parent pSrc0) pBody0) in H2. intuition.
      inversion H0. auto.
      apply (silly_lemma2 pSrc0 (parent pSrc0) pBody0) in H0. intuition.
      inversion H0. auto.
      apply (silly_lemma2 pSrc0 (parent pSrc0) pBody0) in H0. intuition.
      apply (silly_lemma2 pSrc0 (parent pSrc0) pBody0) in H2. intuition.
      apply (silly_lemma2 pSrc0 (parent pSrc0) pBody0) in H2. intuition.
    - intuition.
      unfold InputHandler in H3.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H3 ; subst ; simpl in * ; intuition.
      specialize (H0 {| pSrc := h; pDst := pDst; pBody := pBody |}). intuition.
      specialize (H0 {| pSrc := pSrc; pDst := pDst; pBody := pBody |}). intuition.
      inversion H4. auto.
      specialize (H0 {| pSrc := h; pDst := pDst; pBody := pBody |}). intuition.
      inversion H4. auto.
      specialize (H0 {| pSrc := pSrc; pDst := pDst; pBody := pBody |}). intuition.
      specialize (H0 {| pSrc := h; pDst := pDst; pBody := pBody |}). intuition.
      specialize (H0 {| pSrc := pSrc; pDst := pDst; pBody := pBody |}). intuition.
Qed.

Lemma packets_work'''' : forall x (tr : list (Name * (Input + list Output))),
  refl_trans_1n_trace step_async step_async_init x tr -> forall (pSrc pDst: Name) (pBody : Msg),
  In {| pSrc := pSrc; pDst := pDst; pBody := pBody |} (nwPackets x) -> 
  pDst = parent pSrc.
Proof.
  intros.
  assert (forall x tr,
  refl_trans_1n_trace step_async step_async_init x tr -> forall p,
  In p (nwPackets x) -> let (pSrc, pDst, pBody) := p in
  pDst = parent pSrc).
  apply packets_work''.
  specialize (H1 x tr H {| pSrc := pSrc; pDst := pDst; pBody := pBody |} H0).
  simpl in *.
  auto.
Qed.


Lemma all_subtree_terminated: forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr -> forall c,
  (nwState net (Checker c)).(terminated) = true ->
  (forall (d : Name), descendand d (component_name c) -> 
    (nwState net (d)).(terminated) = true).
Proof.
  intros net tr H.
  unfold step_async_star in H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind.
  + intros ; subst ; simpl in *. auto.  
  + subst. intros.
    remember step_async_init as y in *.
    induction H using refl_trans_1n_trace_n1_ind ; intros ; subst ; simpl in *.
    { intuition.
      invc H0 ; simpl in *.
      + unfold NetHandler in H5.
        repeat break_match ; simpl in * ; subst ; simpl in * ; intuition; simpl in * ; inversion H5 ; subst ; intuition ; simpl in *.
        

(* 

    assert (H0' := H0). remember x' as y'. remember x'' as y''.
    invc H0 ; simpl in *.
    - unfold NetHandler in H6.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition; simpl in * ; inversion H6 ; subst ; intuition ; simpl in *. 
      apply eqb_prop in Heqb ; auto.
      apply (H4 c H2 (pDst p)) ; auto.
      apply (H4 c H2 (pDst p)) ; auto.
      rewrite <- e in *. apply (H4 c H2 d) ; auto.
      apply (H4 c H2 d) ; auto.
      rewrite <- e in *. apply (H4 c H2 d) ; auto.
      apply (H4 c H2 d) ; auto.
      
      destruct (pDst p). inversion e. subst. simpl in *.
      clear e H2 H6. apply refl_trans_1n_n1_trace in H1.
      assert (H1' := H1).
      invc H1. invc H8 ; simpl in *.
      { unfold NetHandler in H6.
        repeat break_match ; simpl in * ; subst ; simpl in * ; intuition; simpl in * ; inversion H6 ; subst ; intuition ; simpl in * ; clear H6.
        apply app_inj_tail in H0. destruct H0. subst.
        assert (pDst p0 = Checker c0).
        inversion H6. destruct (pDst p0). inversion H0. subst. simpl in *.
        apply eqb_prop in Heqb0 ; auto.
        apply (H4 c0) ; auto. 
      }
      
      apply (H4 c H2 d) ; auto.
      rewrite <- e in *. apply (H4 c H2 d) ; auto.
      apply (H4 c H2 d) ; auto.       *)
Admitted.

Lemma terminated_child_list_null_null: forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr -> (forall c,
  children (Checker c) = [] -> 
  child_list (nwState net (Checker c)) = []).
Proof.
  intros net tr H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind ; intros ; simpl in *.
  + subst.
    simpl in *.
    auto.
  + subst. simpl in *.
    intuition.
    invc H0 ; simpl in *.
    - unfold NetHandler in H5.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H5 ; subst ; simpl in * ; intuition.
      rewrite <- e in * ; auto.
      rewrite <- e in *. apply H3 in H2. subst.
      rewrite H2 in Heql0.
      inversion Heql0.
    - unfold InputHandler in H4.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H4 ; subst ; simpl in * ; intuition.
Qed.

Lemma terminated_child_list_null: forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr -> (forall c,
  (nwState net (Checker c)).(terminated) = true ->
  child_list (nwState net (Checker c)) = []).
Proof.
  intros net tr H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind ; intros ; simpl in *.
  + subst.
    simpl in *.
    inversion H.
  + subst. simpl in *.
    intuition.
    invc H0 ; simpl in *.
    - unfold NetHandler in H5.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H5 ; subst ; simpl in * ; intuition.
      rewrite <- e in *.
      apply (H3 c) ; auto.
      apply eqb_false_iff in Heqb.
      intuition.
    - unfold InputHandler in H4.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H4 ; subst ; simpl in * ; intuition.
      apply (terminated_child_list_null_null x' tr1) ; auto.
Qed.

(* Lemma descendand_but_no_child
H : descendand (component_name d) (component_name c)
H0 : ~ In (component_name d) (children (Checker c))
 *)

(* Lemma nearly_all_subtree_in_ass_list: forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr -> (forall c d,
  In d (children c) -> (~ In d (child_list (nwState net c))) ->
    forall dd : Name, descendand dd d ->
    (forall e, In e (nwState net dd).(ass_list) -> In e (nwState net d).(ass_list))).
Admitted. *)

(* Lemma children_d_different: forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr -> (forall c d,
    (In d (children_d (nwState net c))) ->
     c <> d).
Proof.
  intros net tr H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind ; intros ; simpl in *.
  + subst.
    simpl in *.
    intuition.
  + subst. simpl in *.
    intuition.
    invc H0 ; simpl in *.
    - unfold NetHandler in H6.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H6 ; subst ; simpl in * ; intuition.
      apply (H4 (pDst p) (pDst p)) ; auto.
      apply (H4 d d) ; auto.
      apply (H4 (pDst p) (pDst p)) ; auto.
      apply (H4 d d) ; auto.
      destruct p. simpl in *. subst.  *)

Lemma nearly_all_subtree_terminated': forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr -> (forall c d,
    (In d (children_d (nwState net c))) ->
    (nwState net d).(terminated) = true).
Proof.
  intros net tr H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind ; intros ; simpl in *.
  + subst.
    simpl in *.
    intuition.
  + subst. simpl in *.
    intuition.
    invc H0 ; simpl in *.
    - unfold NetHandler in H5.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H5 ; subst ; simpl in * ; intuition.
      apply eqb_prop in Heqb ; auto.
      apply eqb_prop in Heqb ; auto.
      apply (H3 (pDst p) (pDst p) ) ; auto.
      apply (H3 c (pDst p)) ; auto.
      assert (terminated (nwState x' (pSrc p)) = true).
      destruct p. simpl in *.
        apply (packets_work'wrap x' tr1 H pSrc pDst pBody) ; auto.
        rewrite H4. apply in_or_app. simpl. auto. 
        destruct p. simpl in *. subst. apply eqb_false_iff in Heqb. intuition.
      apply (H3 (pDst p) (pDst p) ) ; auto.
      apply (H3 c (pDst p)) ; auto.
      apply (H3 (pDst p) d) ; auto.
      apply (H3 c d) ; auto.
      apply (H3 (pDst p) d) ; auto.
      apply (H3 c d) ; auto.
      destruct p. simpl in *. rewrite <- H0 in *.
        apply (packets_work'wrap x' tr1 H pSrc pDst pBody) ; auto.
        rewrite H4. apply in_or_app. simpl. auto.
      apply (H3 (pDst p) d) ; auto.
      apply (H3 c d ) ; auto.
      destruct p. simpl in *. rewrite <- H0 in *.
        apply (packets_work'wrap x' tr1 H pSrc pDst pBody) ; auto.
        rewrite H4. apply in_or_app. simpl. auto.
      apply (H3 (pDst p) d) ; auto.
      apply (H3 c d ) ; auto.
    - specialize (H3 c d).
      unfold InputHandler in H4.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H4 ; subst ; simpl in * ; intuition.
Qed.

(* Lemma nearly_all_subtree_in_ass_list: forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr -> (forall c d,
  In d (children c) -> (~ In d (child_list (nwState net c))) ->
    (forall e, In e (nwState net d).(ass_list) -> In e (nwState net c).(ass_list))).
Proof.
  intros net tr H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind ; intros ; simpl in *.
  + subst.
    simpl in *.
    intuition.
  + subst. simpl in *.
    intuition.
    invc H0 ; simpl in *.
    - unfold NetHandler in H5.
Admitted. *)



Lemma all_subtree_in_ass_list: forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr -> (forall c,
  (nwState net (Checker c)).(terminated) = true ->
  (forall d, descendand (component_name d) (component_name c) -> 
    (forall e, In e (nwState net (Checker d)).(ass_list) -> In e (nwState net (Checker c)).(ass_list)))).
Proof.
  intros net tr H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind ; intros ; simpl in *.
  + subst.
    simpl in *.
    inversion H.
  + subst. simpl in *.
    assert (H2' := H2).
    apply (terminated_child_list_null x'' (tr1 ++ tr2)) in H2 ; auto.
(*     assert ((forall c d,
  In d (children c) -> (~ In d (child_list (nwState x'' c))) ->
    (forall e, In e (nwState x'' d).(ass_list) -> In e (nwState x'' c).(ass_list)))) as new.
    apply (nearly_all_subtree_in_ass_list x'' (tr1 ++ tr2)) ; auto.
   *)  
    (* assert (forall c,
  (forall (d : Name), descendand d c -> d <> c -> 
    (~ In d (child_list (nwState x'' c))) ->
    (nwState x'' d).(terminated) = true)) as newnew.
    apply (nearly_all_subtree_terminated' x'' (tr1 ++ tr2)) ; auto.
     *)unfold component_name in *.
    assert (~ In (Checker d) (child_list (nwState x'' (Checker c)))).
    intuition.
    rewrite H2 in *. inversion H5.

    invc H0 ; simpl in *.
    - assert (forall n m , l = [(n, m)] -> (parent (pDst p) = n) /\ (m = (ass_list (nwState x' (pDst p))) ++ pBody p)).
      intros. subst.
      apply (Nethandler_correct x' p out d0) ; auto.

      destruct p. simpl in *.
      assert (pDst = parent pSrc).
      apply (packets_work'''' x' tr1 H pSrc pDst pBody) ; auto.
      rewrite H6. apply in_or_app. simpl. auto.
      subst.
      assert (l = [] \/ exists p, l = [p]).
      apply (Nethandler_nil_one x' (parent pSrc) pSrc pBody out d0) ; auto.
      destruct H8.
      subst.
      intuition. specialize (H8 c).
      unfold NetHandler in H7.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H7 ; subst ; simpl in * ; intuition.
        rewrite <- e0 in *. intuition. apply (H9 d ) ; auto.
        rewrite <- e0 in *. intuition. apply (H9 d ) ; auto.
        apply eqb_false_iff in Heqb. intuition.
        rewrite <- e0 in *. intuition. apply (H9 d ) ; auto.
        rewrite <- e0 in *. intuition. apply (H9 d ) ; auto.
        rewrite <- e0 in *. intuition. subst.
        assert ((nwState x' (Checker c)).(terminated) = true ->
  (forall (d : Name), descendand d (component_name c) -> 
    (nwState x' (d)).(terminated) = true)).
        apply (all_subtree_terminated x' tr1) ; auto.
        intuition. specialize (H10 (Checker d)) ; intuition.
        apply eqb_false_iff in Heqb. intuition.
        intuition. apply (H9 d ) ; auto.
        intuition. apply (H9 d ) ; auto.
        intuition. apply (H9 d ) ; auto.
        destruct H8. destruct x.
        specialize (H0 n m). intuition.
        assert (pBody = ass_list (nwState x' pSrc)).
        admit.
        subst.
      unfold NetHandler in H7.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H7 ; subst ; simpl in * ; intuition.
      rewrite <- e0 in *.
      assert (d = c \/ d <> c).
      apply classic.
      destruct H0.
      subst. apply in_or_app. auto.
      assert (In pSrc (child_list (nwState x' (Checker c)))).
      admit.
      rewrite Heql in *. inversion H8. subst.
      assert (forall c,
  (forall (d : Name), descendand d c -> d <> c -> 
    (~ In d (child_list (nwState x' c))) ->
    (nwState x' d).(terminated) = true)).
      apply (nearly_all_subtree_terminated' x' tr1) ; auto.
      specialize (H8 (Checker c) (Checker d)) ; intuition.
      


      rewrite <- e0 in *.
        apply eqb_false_iff in Heqb.
        assert ((nwState x' (Checker c)).(terminated) = true ->
  (forall (d : Name), descendand d (component_name c) -> 
    (nwState x' (d)).(terminated) = true)).
        apply (all_subtree_terminated x' tr1) ; auto.
        intuition. specialize (H8 (Checker d)). intuition.
      apply (H9 c H2' d) ; auto.
Admitted.

Lemma only_children_in_child_list : forall x tr,
  step_async_star (params := Checker_MultiParams) step_async_init x tr -> (forall (c : Component) (d : Name),
  In d (child_list (nwState x (Checker c))) ->
  (Checker c) = parent d).
Proof.
  intros x tr H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind ; intros ; simpl in *.
  + subst.
    simpl in *.
    unfold children in H.
    apply (parent_children_holds) in H.
    unfold parent.
    auto.
  + subst. simpl in *.
    intuition.
    invc H0 ; simpl in *.
    - unfold NetHandler in H5.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H5 ; subst ; simpl in * ; intuition.
      rewrite <- e in *.
      apply (H3 c d) ; auto.
      rewrite <- e in *.
      apply (H3 c d) ; auto.
      destruct p. subst. simpl in *. intuition.
      rewrite Heql0.
      repeat break_match.
      simpl in H2.
      simpl. auto.
      simpl. auto.
      simpl. apply remove_src_before in H2. auto.
    - unfold InputHandler in H4.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H4 ; subst ; simpl in * ; intuition.
Qed.




Lemma packets_work''' : forall x tr a0,
  refl_trans_1n_trace step_async step_async_init x tr -> 
  (((forall p, In p (nwPackets x) -> ((let (pSrc, pDst, pBody) := p in
  (In a0 pBody -> exists d : Name, descendand d pSrc /\ In a0 (init_certificate d))))) /\
  forall c, In a0 (ass_list (nwState x (Checker c))) -> exists d : Name, descendand d (component_name c) /\ In a0 (init_certificate d))).
Proof.
  intros x tr a0 H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind ; intros ; subst ; simpl in *.
  + split ; intros.
    inversion H.
    exists (component_name c).
    split ; auto.
    unfold descendand.
    exists nil. exists nil.
    assert (Walk v a (name_component (component_name c)) (name_component (component_name c)) [] []).
    apply W_null ; auto.
    apply (Component_prop_1) ; auto.
    exists H0.
    unfold parent_walk.
    unfold parent_walk'.
    intros.
    inversion H1.
  + intuition.
    assert (H2' := H2).
    apply (packets_work' x'' (tr1 ++ tr2)) in H2' ; auto.
    assert (H2'' := H2).
    apply (packets_work'' x'' (tr1 ++ tr2)) in H2'' ; auto.
    intuition.
    invc H0 ; simpl in *.
    - rewrite H5 in *. intuition.
      
      unfold NetHandler in H6.
      destruct p. destruct p0.

      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H6 ; subst ; simpl in * ; intuition.
      apply (silly_lemma2 pSrc0 pDst0 pBody0) in H2. specialize (H3 {| pSrc := pDst0; pDst := parent pDst0; pBody := pBody |} ). intuition.
      specialize (H3 {| pSrc := pSrc; pDst := parent pSrc; pBody := pBody |}).
        assert (In {| pSrc := pSrc; pDst := parent pSrc; pBody := pBody |} (xs ++ {| pSrc := pSrc0; pDst := pDst0; pBody := pBody0 |} :: ys)).
        apply in_app_or in H2. destruct H2. apply in_or_app. left. auto. apply in_or_app. right. simpl. auto.
        intuition.
      specialize (H3 {| pSrc := pDst0; pDst := parent pDst0; pBody := pBody |}).
        assert (In {| pSrc := pDst0; pDst := parent pDst0; pBody := pBody |}(xs ++ {| pSrc := pSrc0; pDst := pDst0; pBody := pBody0 |} :: ys)).
        apply in_app_or in H2. destruct H2. apply in_or_app. left. auto. apply in_or_app. right. simpl. auto.
        intuition.
      specialize (H3 {| pSrc := pSrc; pDst := parent pSrc; pBody := pBody |}).
        assert (In {| pSrc := pSrc; pDst := parent pSrc; pBody := pBody |} (xs ++ {| pSrc := pSrc0; pDst := pDst0; pBody := pBody0 |} :: ys)).
        apply in_app_or in H2. destruct H2. apply in_or_app. left. auto. apply in_or_app. right. simpl. auto.
        intuition.
      inversion H7. subst. apply in_app_or in H0. destruct H0.
        specialize (H4 (name_component pDst0)). rewrite checker_name in H4.
        intuition.
        specialize (H3 {| pSrc := pSrc0; pDst := pDst0; pBody := pBody0 |}).
        assert (In {| pSrc := pSrc0; pDst := pDst0; pBody := pBody0 |} (xs ++ {| pSrc := pSrc0; pDst := pDst0; pBody := pBody0 |} :: ys)).
        apply in_or_app. right. simpl. auto. intuition. apply H8 in H0.
        destruct H0. exists x. destruct H0. split ; auto.
        apply (descendandp1 pDst0 pSrc0 x) ; auto.
        apply (packets_work'''' x' tr1 H pSrc0 pDst0 pBody0) ; auto.
        rewrite H5. apply in_or_app. right. simpl. auto.
      apply (silly_lemma2 pSrc0 pDst0 pBody0) in H7. specialize (H3 {| pSrc := pDst0; pDst := parent pDst0; pBody := pBody |} ). intuition.
      inversion H7. subst. apply eqb_false_iff in Heqb. intuition.
      apply (silly_lemma2 pSrc0 pDst0 pBody0) in H7. specialize (H3 {| pSrc := pSrc; pDst := parent pSrc; pBody := pBody |} ). intuition.
      apply eqb_false_iff in Heqb. intuition.
      apply (silly_lemma2 pSrc0 pDst0 pBody0) in H2. specialize (H3 {| pSrc := pSrc; pDst := parent pSrc; pBody := pBody |} ). intuition.
    - destruct p. intros. simpl in *. intuition.
      unfold InputHandler in H5.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H5 ; subst ; simpl in * ; intuition.
      specialize (H3 {| pSrc := h; pDst := parent h; pBody := pBody |}). intuition.
      specialize (H3 {| pSrc := pSrc; pDst := parent pSrc; pBody := pBody |}). intuition.
      inversion H6. subst. specialize (H4 (name_component h)).
        apply H4. rewrite checker_name. auto.
      specialize (H3 {| pSrc := h; pDst := parent h; pBody := pBody |}). intuition.
      inversion H6. subst. intuition.
      specialize (H3 {| pSrc := pSrc; pDst := parent pSrc; pBody := pBody |}). intuition.
      specialize (H3 {| pSrc := h; pDst := parent h; pBody := pBody |}). intuition.
      specialize (H3 {| pSrc := pSrc; pDst := parent pSrc; pBody := pBody |}). intuition.
    - invc H0.
      simpl in *.
      break_match.
      assert (In p (nwPackets x')).
      rewrite H5.
      apply in_or_app.
      right. simpl. auto.
      assert (H0' := H0).
      apply (packets_work' x' tr1) in H0 ; auto. subst. intuition.
      assert (let (pSrc, pDst, pBody) := p in
  In a0 pBody -> 
    exists d : Name, descendand d (component_name (name_component pSrc)) /\ In a0 (init_certificate d)) as new.
      specialize (H3 p). intuition.
      destruct p ; simpl in *.
      subst. intuition.
      unfold NetHandler in H6.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H6 ; subst ; simpl in * ; intuition.
      apply in_app_or in H2. destruct H2. intuition.
        specialize (H4 (name_component pSrc)).
        rewrite checker_name in H4.
        intuition. rewrite cnnc in *. destruct H7. destruct H7.
        exists x. split ; auto.
        apply (descendandp1 (component_name c) pSrc) ; auto.
        apply (packets_work'' x' tr1) in H0' ; auto.

      apply in_app_or in H2. destruct H2. intuition.
        specialize (H4 (name_component pSrc)).
        rewrite checker_name in H4. intuition. destruct H7. destruct H7.
        exists x. split ; auto. rewrite cnnc in *.
        apply (descendandp1 (component_name c) pSrc) ; auto.
        apply (packets_work'' x' tr1) in H0' ; auto.
      intuition.
      simpl in *.
      break_match.
      rewrite <- e in *.
      unfold InputHandler in H5.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H5 ; subst ; simpl in * ; intuition.
      intuition.
Qed.


Lemma only_desc_in_ass_list: forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr -> (forall a c,
  In a (ass_list (nwState net (Checker c))) -> exists d : Name, descendand d (component_name c) /\ In a (init_certificate d)).
Proof.
  intros.
  assert (forall x tr a0,
  refl_trans_1n_trace step_async step_async_init x tr -> 
  (((forall p, In p (nwPackets x) -> ((let (pSrc, pDst, pBody) := p in
  (In a0 pBody -> exists d : Name, descendand d pSrc /\ In a0 (init_certificate d))))) /\
  forall c, In a0 (ass_list (nwState x (Checker c))) -> exists d : Name, descendand d (component_name c) /\ In a0 (init_certificate d)))).
  apply packets_work'''.
  specialize (H1 net tr a0). apply H1 ; auto.
Qed.

Lemma is_in_isa : forall v2 v1 n,
  In (assign_cons v2 v1) (init_certificate n) -> isa_aVarComponent v2 n.
Proof.
  intros v2 v1 n H.
  unfold isa_aVarComponent.
  apply init_certificate_init_var_l in H.
  induction (init_var_l n).
  + induction H. 
  + simpl in *.
    destruct H.
    - subst.
      unfold varList_has_var.
      unfold varList_has_varb.
      unfold var_beq.
      break_match.
      simpl. auto.
      intuition.
    - apply IHl in H.
      unfold varList_has_var in *.
      unfold varList_has_varb in *.
      apply orb_true_intro.
      right.
      auto.
Qed.


Theorem root_ends_true_witness_consistent: forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr ->
  (nwState net (Checker (name_component root))).(terminated) = true ->
  (nwState net (Checker (name_component root))).(consistent) = true ->
  Witness_consistent. (*terminated<->wc*)
Proof.
  intros net tr reachable term cons.
  apply Witness_consistent_root_subtree_consistent.
  unfold root_subtree_consistent.
  intros.
  assert (forall d, descendand (component_name d) (root) -> 
    (forall e, In e (nwState net (Checker d)).(ass_list) -> In e (nwState net (Checker (name_component root))).(ass_list))).
  apply (all_subtree_in_ass_list net tr) ; auto.
  rename H3 into Hd.
  assert (forall (c : Name), exists vl el w, parent_walk (name_component c) (name_component root) vl el w) as pwtr.
  unfold parent_walk.
  unfold root.
  intros.
  apply parent_walk_to_root.
  apply Component_prop_1 ; auto.
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

Theorem root_ends_false_witness_inconsistent: forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr ->
  (nwState net (Checker (name_component root))).(terminated) = true ->
  (nwState net (Checker (name_component root))).(consistent) = false ->
  ~ Witness_consistent.
Proof.
  intros net tr reachable terminated inconsistent.
  unfold root in *.
  intuition.
  apply Witness_consistent_root_subtree_consistent in H.
  unfold root_subtree_consistent in H.
  apply (Drei_zwei''' net tr) in inconsistent ; auto.
  intuition.
  apply inconsistent.
  unfold is_consistent.
  intros.
  destruct assign1. destruct assign2.
  intros.
  subst.
  apply (only_desc_in_ass_list net tr reachable) in H0 ; auto.
  apply (only_desc_in_ass_list net tr reachable) in H1 ; auto.
  destruct H0.
  destruct H0.
  destruct H1.
  destruct H1.
  assert (H3' := H3). assert (H2' := H2).
  apply is_in_cons_cert_then_take_it in H3.
  apply is_in_cons_cert_then_take_it in H2.
  apply is_in_isa in H3'.
  apply is_in_isa in H2'.
  specialize (H v2 x x0).
  subst.
  unfold descendand_r in *.
  unfold descendand in *.

  apply H ; auto.
Qed.



Axiom everything_ends : forall c net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr ->
  {net2 : network & {tr2 : list (Name * (Input + list Output)) & 
    step_async_star (params := Checker_MultiParams) net net2 tr2 /\
    (nwState net2 (Checker c)).(terminated) = true}}.

Axiom every_step_is_towards_an_end : forall c net tr net2 tr2,
  step_async_star (params := Checker_MultiParams) step_async_init net tr ->
  step_async net net2 tr2 ->
  {net3 : network & {tr3 : list (Name * (Input + list Output)) & 
    step_async_star (params := Checker_MultiParams) net net3 (tr2 ++ tr3) /\
    (nwState net3 (Checker c)).(terminated) = true}}.

(* x1. wenn Zustand terminated erreicht (true), dann bleibt er immer true (vllt NetHandler anpassen daf\u00fcr, indem am Anfang abgefragt wird, ob schon terminated)
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
  5. child_list, terminated und consistent ghost-variable, nur noch outputs *)

End Consistency_Checker.