
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
  child_todo : list Name;
  child_done : list Name
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
            (child_todo state)
            (child_done state)),
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
            (child_todo state)
            (child_done state)),
      [(parent me, (ass_list state))])
  | _ =>
    ([] , (mkData
            (checkerknowledge state)
            (checkerinput state)
            (ass_list state)
            (terminated state)
            (consistent state)
            (child_todo state)
            (child_done state)),
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
            (child_todo state)
            (child_done state)),
      [])
  else
  match (child_todo state) with
  | [] =>
    ([] , (mkData
            (checkerknowledge state)
            (checkerinput state)
            (ass_list state)
            (terminated state)
            (consistent state)
            (child_todo state)
            (child_done state)),
      [])
  | [c] =>
    ([check_ass_list ((ass_list state) ++ child_cert)] , (mkData
            (checkerknowledge state)
            (checkerinput state)
            ((ass_list state) ++ child_cert)
            (true)
            (check_ass_list ((ass_list state) ++ child_cert))
            ([])
            (src :: (child_done state))),
      [(parent me, (ass_list state ++ child_cert))])
  | _ =>
    ([] , (mkData
            (checkerknowledge state)
            (checkerinput state)
            ((ass_list state) ++ child_cert)
            (terminated state)
            (consistent state)
            (remove_src src (child_todo state))
            (src :: (child_done state))),
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

Lemma terminated_child_todo_null_null: forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr -> (forall c,
  children (Checker c) = [] -> 
  child_todo (nwState net (Checker c)) = []).
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

Lemma terminated_child_todo_null: forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr -> (forall c,
  (nwState net (Checker c)).(terminated) = true ->
  child_todo (nwState net (Checker c)) = []).
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
      apply (terminated_child_todo_null_null x' tr1) ; auto.
Qed.

(* Lemma descendand_but_no_child
H : descendand (component_name d) (component_name c)
H0 : ~ In (component_name d) (children (Checker c))
 *)

(* Lemma nearly_all_subtree_in_ass_list: forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr -> (forall c d,
  In d (children c) -> (~ In d (child_todo (nwState net c))) ->
    forall dd : Name, descendand dd d ->
    (forall e, In e (nwState net dd).(ass_list) -> In e (nwState net d).(ass_list))).
Admitted. *)

Lemma child_done_terminated: forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr -> (forall c d,
    (In d (child_done (nwState net c))) ->
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

Lemma only_children_in_child_todo : forall x tr,
  step_async_star (params := Checker_MultiParams) step_async_init x tr -> (forall (c : Component) (d : Name),
  In d (child_todo (nwState x (Checker c))) ->
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
      simpl. simpl in H2. destruct H2 ; auto.
      simpl. simpl in H2. destruct H2 ; auto. destruct H0 ; auto.
      right. right. apply (remove_src_before _ pSrc) ; auto.
    - unfold InputHandler in H4.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H4 ; subst ; simpl in * ; intuition.
Qed.

Lemma not_parent_in_packets : forall x' tr,
  step_async_star (params := Checker_MultiParams) step_async_init x' tr ->
  (
  forall pSrc pDst pBody pDst2 pBody2,
  In {| pSrc := pSrc; pDst := pDst; pBody := pBody |} (nwPackets x') ->
  ~ In {| pSrc := pSrc; pDst := pDst2; pBody := pBody2 |} (nwPackets x')).
Proof.
Admitted.

Lemma pbody_is_asslist : forall x' tr,
  step_async_star (params := Checker_MultiParams) step_async_init x' tr ->
  (
  forall pSrc pDst pBody,
  In {| pSrc := pSrc; pDst := pDst; pBody := pBody |} (nwPackets x') ->
  pBody = (nwState x' pSrc).(ass_list)).
Proof.
  intros x' tr H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind ; intros ; simpl in *.
  + subst.
    simpl in *.
    inversion H.
  + subst. simpl in *.
    intuition.
    invc H0 ; simpl in *. 
    - destruct p. simpl in *.

      assert ((nwState x' pSrc0).(terminated) = true).
      apply (packets_work'wrap x' tr1 H pSrc0 pDst0 pBody0) ; auto.
      rewrite H4. apply in_or_app. simpl. auto.
      assert (pDst0 = parent pSrc0).
      apply (packets_work'''' x' tr1 H pSrc0 pDst0 pBody0) ; auto.
      rewrite H4. apply in_or_app. simpl. auto.

      subst.
      unfold NetHandler in H5.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H5 ; subst ; simpl in * ; intuition ; rewrite H4 in *.
      apply (H3 (parent pSrc0) pDst pBody) ; auto. apply in_or_app. simpl. apply in_app_or in H2. destruct H2 ; auto.
      apply (H3 (parent pSrc0) pDst pBody) ; auto. apply in_or_app. simpl. apply in_app_or in H2. destruct H2 ; auto.
      inversion H6. subst. auto.
      assert (In {| pSrc := pSrc0; pDst := parent pSrc0; pBody := pBody0 |} (nwPackets x')).
      rewrite H4. apply in_or_app. simpl. auto.
      apply (not_parent_in_packets x' tr1 H _ _ _ pDst pBody) in H2.
      assert (In {| pSrc := pSrc0; pDst := pDst; pBody := pBody |} (nwPackets x')).
      rewrite H4.
      apply in_or_app. simpl. 
      assert (pDst = parent pSrc0). admit. subst.
      assert (pBody = pBody0). admit. subst.
      auto. intuition.
      assert (In {| pSrc := pSrc0; pDst := parent pSrc0; pBody := pBody0 |} (nwPackets x')).
      rewrite H4. apply in_or_app. simpl. auto.
      apply (not_parent_in_packets x' tr1 H _ _ _ pDst pBody) in H6.
      assert (In {| pSrc := pSrc0; pDst := pDst; pBody := pBody |} (nwPackets x')).
      rewrite H4.
      apply in_or_app. simpl. 
      assert (pDst = parent pSrc0). admit. subst.
      assert (pBody = pBody0). admit. subst.
      auto. intuition.
      apply (H3 pSrc pDst pBody) ; auto. apply in_or_app. simpl. apply in_app_or in H2. destruct H2 ; auto.
      apply (H3 pSrc pDst pBody) ; auto. apply in_or_app. simpl. apply in_app_or in H2. destruct H2 ; auto.
      inversion H6. subst. intuition.
      apply (H3 pSrc pDst pBody) ; auto. apply in_or_app. simpl. apply in_app_or in H6. destruct H6 ; auto.
      apply (H3 pSrc pDst pBody) ; auto. apply in_or_app. simpl. apply in_app_or in H2. destruct H2 ; auto.
    - 
      specialize (H3 pSrc pDst pBody).
      unfold InputHandler in H4.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H4 ; subst ; simpl in * ; intuition.
      inversion H0. subst. intuition.
      inversion H0. subst. intuition.
Qed.

Lemma pSrc_in_child_todo : forall x' tr,
  step_async_star (params := Checker_MultiParams) step_async_init x' tr ->
  (
  forall pSrc pDst pBody,
  In {| pSrc := pSrc; pDst := pDst; pBody := pBody |} (nwPackets x') ->
  pSrc <> pDst ->
  In pSrc (nwState x' (parent pSrc)).(child_todo)).
Proof.
  intros net tr H pSrc pDst pBody H2 psrcpdst.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind ; intros ; simpl in *.
  + subst.
    simpl in *.
    intuition.
  + subst. simpl in *.
    intuition.
    invc H0 ; simpl in * ; intuition.
    - (* unfold NetHandler in H5.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H5 ; subst ; simpl in * ; intuition. admit. admit.
      inversion H0. subst. *)
      assert (forall n m , l = [(n, m)] -> (parent (Net.pDst p) = n) /\ (m = (ass_list (nwState x' (Net.pDst p))) ++ Net.pBody p)) as new.
      intros. subst.
      apply (Nethandler_correct x' p out d) ; auto.

      destruct p. simpl in *.

      assert (pBody0 = (nwState x' pSrc0).(ass_list)) as newnewnew.
      apply (pbody_is_asslist x' tr1 H pSrc0 pDst0 pBody0) ; auto.
      rewrite H4. apply in_or_app. simpl. auto.
      assert ((nwState x' pSrc0).(terminated) = true).
      apply (packets_work'wrap x' tr1 H pSrc0 pDst0 pBody0) ; auto.
      rewrite H4. apply in_or_app. simpl. auto.
      assert (pDst0 = parent pSrc0).
      apply (packets_work'''' x' tr1 H pSrc0 pDst0 pBody0) ; auto.
      rewrite H4. apply in_or_app. simpl. auto.

      subst.
      unfold NetHandler in H5.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H5 ; subst ; simpl in * ; intuition.
      rewrite H4 in *. rewrite <- e. apply H3.
      apply in_app_or in H2. destruct H2 ; apply in_or_app ; simpl ; auto.
      rewrite e in *. rewrite Heql0 in *. rewrite H4 in *.
      assert (In pSrc []). apply H3.
      apply in_app_or in H2. destruct H2 ; apply in_or_app ; simpl ; auto. inversion H6.
      inversion H6. (* subst. intuition. *)
      rewrite e in *. rewrite Heql0 in *.
      assert (pSrc = pSrc0). admit. subst. intuition.
Admitted.

Lemma child_done_in_ass_list: forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr -> (forall c d,
    (In d (child_done (nwState net c))) ->
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


    assert (H2' := H2).
    apply (child_done_terminated x'' (tr1 ++ tr2)) in H2' ; auto.
    invc H0 ; simpl in *.
    - assert (forall n m , l = [(n, m)] -> (parent (pDst p) = n) /\ (m = (ass_list (nwState x' (pDst p))) ++ pBody p)) as new.
      intros. subst.
      apply (Nethandler_correct x' p out d0) ; auto.

      destruct p. simpl in *.
      assert (pBody = (nwState x' pSrc).(ass_list)) as newnewnew.
      apply (pbody_is_asslist x' tr1 H pSrc pDst pBody) ; auto.
      rewrite H5. apply in_or_app. simpl. auto.


      assert ((nwState x' pSrc).(terminated) = true).
      apply (packets_work'wrap x' tr1 H pSrc pDst pBody) ; auto.
      rewrite H5. apply in_or_app. simpl. auto.
      assert (pDst = parent pSrc).
      apply (packets_work'''' x' tr1 H pSrc pDst pBody) ; auto.
      rewrite H5. apply in_or_app. simpl. auto.
      assert (l = [] \/ exists p, l = [p]).
      apply (Nethandler_nil_one x' pDst pSrc pBody out d0 l) ; auto.


      destruct H8.
      subst.
      
      unfold NetHandler in H6.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H6 ; subst ; simpl in * ; intuition.
      apply (H4 (parent pSrc) d) ; auto.
      apply (H4 (parent pSrc) d) ; auto.
      subst. apply in_or_app. auto.
      apply in_or_app. left. apply (H4 (parent pSrc) d) ; auto.
      apply (H4 c (parent pSrc)) ; auto.
      apply (H4 c (parent pSrc)) ; auto.
      assert ((terminated (nwState x' (parent pSrc))) = true).
      apply (child_done_terminated x' tr1 H c (parent pSrc)) ; auto.
      apply eqb_false_iff in Heqb. intuition.
      apply (H4 c d) ; auto.
      apply (H4 c d) ; auto.
      apply (H4 c d) ; auto.
      destruct H8. destruct x. subst.
      specialize (new n m). intuition.
      subst.
      unfold NetHandler in H6.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H6 ; subst ; simpl in * ; intuition.
      subst. apply in_or_app. auto.
      apply in_or_app. left.
      apply (H4 (parent pSrc) d) ; auto.
      apply in_app_or in H3. destruct H3.
      apply (H4 c (parent pSrc)) ; auto.
      assert ((terminated (nwState x' (parent pSrc))) = true).
      apply (child_done_terminated x' tr1 H c (parent pSrc)) ; auto.
      apply eqb_false_iff in Heqb. intuition.
      apply (H4 c d) ; auto.
    - specialize (H4 c d).
      intuition.
      unfold InputHandler in H5.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H5 ; subst ; simpl in * ; intuition.
Qed.

Lemma comp_index_name : forall pSrc n,
  component_index (name_component pSrc) =? component_index (name_component n) = true <->
  pSrc = n.
Proof.
  intros pSrc n.
  split ; intros.
  assert (pSrc = n \/ pSrc <> n).
  apply classic.
  destruct H0.
  auto.
  unfold name_component in *. repeat break_match.
  subst. unfold component_index in *. repeat break_match.
  subst.
  apply Nat.eqb_eq in H. subst. intuition.
  apply <- Nat.eqb_eq ; auto.
  subst. auto.
Qed.

Lemma remove_removes_one : forall p l,
 In p l -> NoDup l -> Permutation (p :: remove_src p l) l.
Proof.
  intros p l H H0.
  induction l.
  inversion H.
  simpl in H. destruct H.
  subst.
  simpl.
  break_match. auto. 
  assert ((component_index (name_component p) =? component_index (name_component p)) = true).
  apply Nat.eqb_refl.
  rewrite H in Heqb. inversion Heqb.
  intuition.
  assert (H0' := H0).
  apply NoDup_cons_iff in H0'.
  destruct H0'.
  intuition.
  simpl in *.
  assert (p = a0 \/ p <> a0).
  apply classic.
  destruct H1.
  subst. intuition.
  break_match.
  apply comp_index_name in Heqb.
  intuition.
  apply (perm_skip a0) in H4.
  apply Permutation_sym in H4. apply Permutation_sym.
  apply (Permutation_trans H4) ; auto.
  apply perm_swap.
Qed.

Lemma no_v_no_children : forall v0 a0 c y x,
  ~ v0 y ->
  ~ In (component_name y) (children' v0 a0 c (component_name x)).
Proof.
  intros.
  induction c ; intros ; simpl in *.
  + intuition.
  + assert (~ v0 y).
    intuition.
    apply H.
    apply In_right. auto. apply IHc in H0.
    assert (y <> y0).
    intuition. apply H.
    apply In_left. auto. subst. apply In_single.
    unfold not. intros.
    break_match.
      - simpl in H2.
        destruct H2. inversion e. inversion H2. subst. intuition.
        intuition.
      - intuition.
  + intuition.
  + rewrite <- e in *.
    intuition.
Qed.

Lemma NoDup_children: forall name,
  NoDup (children name).
Proof.
  intros.
  unfold children.
  induction g ; intros ; simpl in * ; intuition.
  + break_match ; subst.
    - assert (~ In (component_name y) (children' v0 a0 c (component_name x))).
      apply no_v_no_children ; auto.
      apply NoDup_cons ; auto.
    - auto.
Qed.

Lemma remove_src_before': forall (d pSrc : Name) (l1 : list Name),
  ~ In d l1 ->
  ~ In d (remove_src pSrc l1).
Proof.
  intros.
  induction l1 ; intros ; simpl in * ; intuition ; break_match ; intuition.
  inversion H0.
  subst.
  intuition.
  intuition.
Qed.

Lemma NoDup_remove_src : forall pSrc l1,
  NoDup l1 ->
  NoDup (remove_src pSrc l1).
Proof.
  intros.
  induction l1 ; intros ; simpl in * ; intuition ; break_match ; intuition.
  + apply NoDup_cons_iff in H. destruct H ; auto.
  + apply NoDup_cons_iff in H. destruct H ; intuition.
    apply NoDup_cons_iff. split ; auto.
    apply remove_src_before' ; auto.
Qed.

Lemma Nodup_child_todo: forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr -> (forall c,
  NoDup (child_todo (nwState net c))).
Proof.
  intros net tr H.
remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind ; intros ; simpl in *.
  + subst.
    simpl in *.
    intuition.
    apply NoDup_children.
  + subst. simpl in *.
    intuition.
    invc H0 ; simpl in *.
    - destruct p. simpl in *.

      assert (pBody = (nwState x' pSrc).(ass_list)) as newnewnew.
      apply (pbody_is_asslist x' tr1 H pSrc pDst pBody) ; auto.
      rewrite H3. apply in_or_app. simpl. auto.


      assert ((nwState x' pSrc).(terminated) = true).
      apply (packets_work'wrap x' tr1 H pSrc pDst pBody) ; auto.
      rewrite H3. apply in_or_app. simpl. auto.
      assert (pDst = parent pSrc).
      apply (packets_work'''' x' tr1 H pSrc pDst pBody) ; auto.
      rewrite H3. apply in_or_app. simpl. auto.

      subst.
      unfold NetHandler in H4.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H4 ; subst ; simpl in * ; intuition.
      specialize (H2 (parent pSrc)). rewrite Heql0 in *.
      assert (H2' := H2).
      apply NoDup_cons_iff in H2'.
      destruct H2'.
      assert (H2'' := H6).
      apply NoDup_cons_iff in H2''.
      destruct H2''.
      repeat break_match ; auto.
      assert (~ In n l1).
      intuition.
      apply NoDup_cons_iff ; auto.
      assert (NoDup (remove_src pSrc l1)).
      apply NoDup_remove_src ; auto.
      apply NoDup_cons_iff ; split ; auto.
      intuition. apply H5. simpl in H10. destruct H10 ; simpl ; auto.
      right. apply (remove_src_before n pSrc) ; auto.
      apply NoDup_cons_iff ; split ; auto.
      intuition. apply H7.
      apply (remove_src_before n0 pSrc) ; auto.
    - unfold InputHandler in H3.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H3 ; subst ; simpl in * ; intuition.
Qed.

Lemma child_done_children_list_children: forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr -> (forall c,
  Permutation ((nwState net c).(child_done) ++ (nwState net c).(child_todo)) (children c)).
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
    - assert (forall n m , l = [(n, m)] -> (parent (pDst p) = n) /\ (m = (ass_list (nwState x' (pDst p))) ++ pBody p)) as new.
      intros. subst.
      apply (Nethandler_correct x' p out d) ; auto.

      destruct p. simpl in *.

      assert (pBody = (nwState x' pSrc).(ass_list)) as newnewnew.
      apply (pbody_is_asslist x' tr1 H pSrc pDst pBody) ; auto.
      rewrite H3. apply in_or_app. simpl. auto.


      assert ((nwState x' pSrc).(terminated) = true).
      apply (packets_work'wrap x' tr1 H pSrc pDst pBody) ; auto.
      rewrite H3. apply in_or_app. simpl. auto.
      assert (pDst = parent pSrc).
      apply (packets_work'''' x' tr1 H pSrc pDst pBody) ; auto.
      rewrite H3. apply in_or_app. simpl. auto.

      subst.
      unfold NetHandler in H4.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H4 ; subst ; simpl in * ; intuition.
      specialize (H2 (parent pSrc)). rewrite Heql0 in H2. auto.
      assert (pSrc = (parent pSrc) \/ pSrc <> (parent pSrc)) as psrcpdst.
      apply classic.
      destruct psrcpdst as [psrc|pdst].
      subst. rewrite <- psrc in *. rewrite <- psrc in *.
      apply eqb_false_iff in Heqb. intuition.
      assert (n = pSrc).
      assert (In pSrc (nwState x' (parent pSrc)).(child_todo)) as newnew.
      apply (pSrc_in_child_todo x' tr1 H pSrc (parent pSrc) (nwState x' pSrc).(ass_list)) ; auto.
      rewrite H3. apply in_or_app. simpl. right. auto.
      rewrite Heql0 in newnew. simpl in newnew. destruct newnew. auto. intuition.
      specialize (H2 (parent pSrc)). rewrite Heql0 in H2. subst.
      rewrite app_nil_r. 
      assert (Permutation (pSrc :: child_done (nwState x' (parent pSrc))) (child_done (nwState x' (parent pSrc)) ++ [pSrc])).
      apply Permutation_cons_append.
      apply Permutation_sym. apply Permutation_sym in H2. apply Permutation_sym in H5.
      apply (Permutation_trans H2 H5) ; auto.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H4 ; subst ; simpl in * ; intuition.
      apply comp_index_name in Heqb0. subst.
      specialize (H2 (parent n)). rewrite Heql0 in H2. auto.
      assert (Permutation (n :: child_done (nwState x' (parent n)) ++ n0 :: l1) (child_done (nwState x' (parent n)) ++ n :: n0 :: l1)).
      apply (Permutation_cons_app (child_done (nwState x' (parent n))) ) ; auto.
      apply Permutation_sym. apply Permutation_sym in H2. apply Permutation_sym in H5.
      apply (Permutation_trans H2 H5) ; auto.
      apply comp_index_name in Heqb1. subst.
      specialize (H2 (parent n0)). rewrite Heql0 in *.
      apply Permutation_sym. apply Permutation_sym in H2.
      apply (Permutation_trans H2) ; auto.
      apply Permutation_sym.
      assert (Permutation (n0 :: child_done (nwState x' (parent n0)) ++ n :: l1) (child_done (nwState x' (parent n0)) ++ n0 :: n :: l1)).
      apply (Permutation_middle).
      apply (Permutation_trans H5) ; auto.
      apply Permutation_app_head. apply perm_swap.
      specialize (H2 (parent pSrc)). rewrite Heql0 in *.
      apply Permutation_sym. apply Permutation_sym in H2.
      apply (Permutation_trans H2) ; auto.
      apply Permutation_sym.
      assert (Permutation (pSrc :: child_done (nwState x' (parent pSrc)) ++ n :: n0 :: remove_src pSrc l1) (child_done (nwState x' (parent pSrc)) ++ pSrc :: n :: n0 :: remove_src pSrc l1)).
      apply (Permutation_middle).
      apply (Permutation_trans H5) ; auto.
      apply Permutation_app_head.
      assert (In pSrc (child_todo (nwState x' (parent pSrc)))).

      assert (pSrc = (parent pSrc) \/ pSrc <> (parent pSrc)) as psrcpdst.
      apply classic.
      destruct psrcpdst as [psrc|pdst].
      subst. rewrite <- psrc in *. rewrite <- psrc in *.
      apply eqb_false_iff in Heqb. intuition.


      apply (pSrc_in_child_todo x' tr1 H pSrc (parent pSrc) (nwState x' pSrc).(ass_list)) ; auto.
      rewrite H3. apply in_or_app. simpl. auto.
      assert (NoDup (child_todo (nwState x' (parent pSrc)))).
      apply (Nodup_child_todo x' tr1) ; auto.
      assert (Permutation (pSrc :: n :: n0 :: remove_src pSrc l1) (n :: pSrc :: n0 :: remove_src pSrc l1)).
      apply perm_swap.
      assert (Permutation (pSrc :: n0 :: remove_src pSrc l1) (n0 :: pSrc :: remove_src pSrc l1)).
      apply perm_swap.
      assert (Permutation (pSrc :: remove_src pSrc l1) l1).
      rewrite Heql0 in *.
      assert (In pSrc l1).
      simpl in H6. destruct H6.
      subst.
      assert ((component_index (name_component pSrc) =? component_index (name_component pSrc)) = true).
      apply Nat.eqb_refl. rewrite H6 in Heqb0. inversion Heqb0.
      destruct H6. rewrite H6 in *.
      assert ((component_index (name_component pSrc) =? component_index (name_component pSrc)) = true).
      apply Nat.eqb_refl. rewrite H10 in Heqb1. inversion Heqb1. auto.
      apply NoDup_cons_iff in H7.
      destruct H7.
      apply NoDup_cons_iff in H11.
      destruct H11.
      apply remove_removes_one ; auto.
      apply (Permutation_trans H8) ; auto.
      apply perm_skip.
      apply (Permutation_trans H9) ; auto.
    - unfold InputHandler in H3.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H3 ; subst ; simpl in * ; intuition.      
Qed.

Lemma child_done_when_terminated: forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr -> (forall c,
    (nwState net c).(terminated) = true -> Permutation (child_done (nwState net c)) (children c)).
Proof.
  intros.
  assert (forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr -> (forall c,
  (nwState net (Checker c)).(terminated) = true ->
  child_todo (nwState net (Checker c)) = [])).
  apply terminated_child_todo_null.
  specialize (H1 net tr H (name_component c)).
  simpl in *. rewrite checker_name in *. intuition.
  assert (Permutation ((nwState net c).(child_done) ++ (nwState net c).(child_todo)) (children c)).
  apply (child_done_children_list_children net tr) ; auto.
  rewrite H2 in H1. rewrite app_nil_r in H1.
  auto.
Qed.

Lemma all_subtree_terminated: forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr -> forall c,
  (nwState net c).(terminated) = true ->
  (forall (d : Name), descendand d c -> 
    (nwState net d).(terminated) = true).
Proof.
  intros net tr H.
  unfold step_async_star in H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind.
  + intros ; subst ; simpl in *. auto.  
  + subst. intros.
    invc H0 ; simpl in *.
    - destruct p. simpl in *.
      assert (terminated (nwState x' pSrc) = true).
      apply (packets_work'wrap x' tr1 H pSrc pDst pBody) ; auto.
      rewrite H4. apply in_or_app. simpl. auto.
      assert (pDst = parent pSrc).
      apply (packets_work'''' x' tr1 H pSrc pDst pBody) ; auto.
      rewrite H4. apply in_or_app. simpl. auto.
      subst.
      unfold NetHandler in H5.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition; simpl in * ; inversion H5 ; subst ; intuition ; simpl in *. 
      apply (H6 c) ; auto.
      apply (H6 c) ; auto.
      apply (H6 c) ; auto.
      apply (H6 (parent pSrc)) ; auto.
      apply (H6 c) ; auto.
      apply (H6 (parent pSrc)) ; auto.
      apply (H6 c) ; auto.
      clear H5 H2. admit.
      (* es gibt nur noch einen in der child_todo, 
        (das ist pSrc) entweder d war vom pSrc-zweig, 
        oder von einem anderen und ist dadurch schon drin *)
      apply (H6 c) ; auto.
      apply (H6 (parent pSrc)) ; auto.
      apply (H6 c) ; auto.
    - intuition.
      specialize (H0 c).
      unfold InputHandler in H4.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H4 ; subst ; simpl in * ; intuition.
      
Admitted.


(* Lemma nearly_all_subtree_in_ass_list: forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr -> (forall c d,
  In d (children c) -> (~ In d (child_todo (nwState net c))) ->
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
  intros.
  assert (H0' := H0).
  apply (terminated_child_todo_null net tr) in H0' ; auto.
  assert (Permutation (child_done (nwState net (Checker c)))  (children (Checker c))).
  assert (Permutation ((nwState net (Checker c)).(child_done) ++ (nwState net (Checker c)).(child_todo)) (children (Checker c))).
  apply (child_done_children_list_children net tr) ; auto.
  rewrite H0' in *. rewrite app_nil_r in H3. auto.
  assert (forall d, Permutation (children (Checker c)) (child_done (nwState net (Checker c)))  -> In d (children (Checker c)) -> In d (child_done (nwState net (Checker c)))).
  apply Permutation_in.
  apply Permutation_sym in H3.
  assert (forall d : Name, In d (children (Checker c)) -> In d (child_done (nwState net (Checker c)))).
  intros.
  apply (H4 d0) ; auto.
  clear H4.
  assert (forall d : Name, In d (children (Checker c)) -> (forall e, In e (nwState net d).(ass_list) -> In e (nwState net (Checker c)).(ass_list))).
  intros.
  apply (child_done_in_ass_list net tr H (Checker c) d0) ; auto.
  clear H5.
  unfold descendand in *. unfold children in *.
  clear H3. clear H0'.
  induction g ; simpl in * ; intuition.
  + 
Admitted.



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
  5. child_todo, terminated und consistent ghost-variable, nur noch outputs *)

End Consistency_Checker.