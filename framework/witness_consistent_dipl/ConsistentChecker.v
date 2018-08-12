
Require Import GraphBasics.Graphs.
Require Import Coq.Logic.Classical_Prop.
Require Import Verdi.Verdi.

Require Export StructTact.Fin.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Require Import Verdi.ExtrOcamlBasicExt.
Require Import Verdi.ExtrOcamlList.

Require Import FunInd.

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
  assign_list : Certificate;
  child_todo : list Name;
}.

(* initialization of the network *)
Definition init_Data (me: Name) := 
  mkData []
         (children me).



Definition Input := Msg.
Definition Output := bool.


Definition InputHandler (me : Name) (i : Input) (data: Data) :
            (list Output) * Data * list (Name * Certificate) :=
	match (children me) with
  | [] => ([], (mkData ((assign_list data) ++ i) (children me)), [(parent me, i)])
  |  _ => ([], (mkData ((assign_list data) ++ i) (children me)), [])
  end.


Definition NetHandler (me : Name) (src: Name) (msg : Certificate) (data: Data) :
    (list Output) * Data * list (Name * Msg) :=
  match (child_todo data) with
      | [] =>
        ([check_assign_list (assign_list data)], data, [])
      | [c] =>
        ([], (mkData ((assign_list data) ++ msg) []), [(parent me, (assign_list data ++ msg))])
      | _ =>
        ([], (mkData ((assign_list data) ++ msg) (remove_src src (child_todo data))), [])
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





Fixpoint certificate_has_varb (vl : Certificate) (v : Var) : bool :=
  match vl with
  | nil => false
  | (assign_cons hd hd2) :: tl => var_beq hd v || certificate_has_varb tl v
  end.

Definition certificate_has_var (vl : Certificate) (v : Var) : Prop :=
  certificate_has_varb vl v = true.

Definition isa_aVarComponent (aVar : Var) (c : Name) : Prop :=
  certificate_has_var (init_combined c) aVar.

Variable null_Value : Value.

Fixpoint valueOfa (aVar : Var) (cert : list Assignment) : Value :=
  match cert with
  | [] => null_Value
  | hd :: tl => let (var, val) := hd in if var_beq var aVar then val else valueOfa aVar tl
  end.

Definition valueOf (aVar : Var) (c : Name) : Value :=
  valueOfa aVar (init_combined c).


Lemma has_var_exists_val : forall var d,
  isa_aVarComponent var d -> exists val : Value, In (assign_cons var val) (init_combined d).
Proof.
  intros var d H.
  unfold isa_aVarComponent in H.
  unfold certificate_has_var in H.
  induction init_combined ; simpl in * ; intuition.
  + inversion H.
  + break_match ; subst.
    apply orb_prop in H.
    destruct H ; intuition.
    exists v1 ; intuition. left. unfold var_beq in H. break_match ; subst ; intuition.
    inversion H.
    destruct H0.
    exists x.
    auto.
Qed.

(* Lemma is_in_cons_cert_then_take_it : forall var val d,
  In (assign_cons var val) (init_combined d) -> valueOf var d = val.
Proof.
  intros var val d H.
  (* assert (is_consistent (init_combined d)). *)
  (* apply init_certificate_is_consistent. *)
  unfold valueOf.
  induction (init_combined d).
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
Qed. *)

Lemma is_in_isa : forall v2 v1 n,
  In (assign_cons v2 v1) (init_combined n) -> isa_aVarComponent v2 n.
Proof.
  intros v2 v1 n H.
  unfold isa_aVarComponent.
  induction (init_combined n).
  + induction H. 
  + simpl in *.
    destruct H.
    - subst.
      unfold certificate_has_var.
      unfold certificate_has_varb.
      unfold var_beq.
      break_match.
      simpl. auto.
      intuition.
    - apply IHc in H.
      unfold certificate_has_var in *.
      unfold certificate_has_varb in *. simpl in *.
      break_match ; subst ; simpl.
      apply orb_true_intro.
      right.
      auto.
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

Lemma root_is_ancestor2 : forall (v : V_set) a g x,
  descendand' v a g x (root' v a g) = true ->
(exists
       (vl : V_list) (el : E_list) (w : Walk v a (name_component x)
                                          (name_component (root' v a g)) vl el),
       parent_walk' (name_component x) (name_component (root' v a g)) vl el v a g w).
Proof.
  intros v a g.
  induction g ; simpl in * ; intuition ; unfold eqn in *.
  + repeat break_match ; subst ; intuition ; simpl in *.
    exists []. exists [].
    assert (Walk (V_single x) A_empty x x [] []).
    apply W_null ; auto. apply In_single.
    exists H0. unfold parent_walk'. intros. inversion H1. inversion H.
  + destruct (root' v0 a0 g0).
    repeat break_match ; subst ; intuition ; simpl in * ; unfold component_name in *.
      inversion e0. inversion e1. subst. assert (v1' := v1). apply n in v1'. intuition.
      inversion e0. subst. unfold parent_walk'. simpl. exists ([x]). exists ([E_ends y x]).
        assert (Walk (V_union (V_single y) v0) (A_union (E_set x y) a0) y x [x] [E_ends y x]).
        apply W_step ; auto. apply W_null ; auto. apply In_right ; auto.
        apply In_left. apply In_single. apply In_left. apply E_left.
        exists H0. intros. break_match ; subst ; intuition. simpl in *.
        inversion H1 ; intuition. inversion H2. rewrite cnnc. auto.
        inversion H1 ; intuition. inversion H2 ; subst ; simpl in *. unfold name_component in *.
        repeat break_match ; intuition. inversion H2.
      inversion e0. subst. unfold parent_walk'. simpl. exists []. exists [].
        assert (Walk (V_union (V_single y) v0) (A_union (E_set x y) a0) y y [] []).
        apply W_null ; auto. apply In_left. apply In_single.
        exists H0. intros. inversion H1.
      specialize (IHg (Checker x)). intuition. simpl in *. repeat destruct H0.
        exists (x :: x0). exists (E_ends y x :: x1).
        assert (Walk (V_union (V_single y) v0) (A_union (E_set x y) a0) y c (x :: x0) (E_ends y x :: x1)).
        apply W_step ; auto.
        apply (Walk_subgraph v0 _ a0 _) ; auto.
        unfold V_included. unfold Included ; intros. apply In_right ; auto.
        unfold A_included. unfold Included ; intros. apply In_right ; auto.
        apply In_left. apply In_single.
        apply In_left. apply E_left.
        exists H1. unfold parent_walk' ; intros ; simpl in *.
        break_match ; subst ; simpl in *. destruct H2. inversion H2. rewrite cnnc. auto.
        assert (v0 y). apply (W_inxyel_inxvl v0 a0 x c x0 x1 x2) in H2 ; auto.
        simpl in H2. destruct H2. subst. auto. apply (W_invl_inv v0 a0 x c x0 x1 x2) in H2. auto.
        intuition.
      destruct H2. inversion H2 ; subst. rewrite cnnc in n2. intuition.
        unfold parent_walk' in H0. apply (H0 c1 c2) ; auto.
      specialize (IHg x0). intuition. repeat destruct H0.
        exists x1. exists x2.
        assert (Walk (V_union (V_single y) v0) (A_union (E_set x y) a0) (name_component x0) c x1 x2).
        apply (Walk_subgraph v0 _ a0 _) ; auto.
        unfold V_included. unfold Included ; intros. apply In_right ; auto.
        unfold A_included. unfold Included ; intros. apply In_right ; auto.
        exists H1. unfold parent_walk' in * ; intros.
        simpl in *. specialize (H0 c1 c2). intuition.
        break_match ; subst ; simpl in * ; intuition.
        assert (v0 y). apply (W_inxyel_inxvl v0 a0 (name_component x0) c x1 x2 x3) in H2 ; auto.
        simpl in H2. destruct H2. subst. unfold name_component in n0.
        break_match. intuition. apply (W_invl_inv v0 a0 (name_component x0) c x1 x2 x3) in H0. auto.
        intuition.
  + specialize (IHg x0).
    intuition.
    repeat destruct H0.
    exists x1. exists x2.
    destruct (root' v0 a0 g0). simpl in *.
    assert (Walk v0 (A_union (E_set x y) a0) (name_component x0) c x1 x2).
    apply (Walk_subgraph v0 _ a0 _) ; auto.
    unfold V_included. unfold Included ; intros. auto.
    unfold A_included. unfold Included ; intros. apply In_right ; auto.
    exists H1. unfold parent_walk' in * ; intros.
    simpl in *. specialize (H0 c1 c2). intuition.
  + rewrite <- e in *.
    rewrite <- e0 in *.
    specialize (IHg x).
    intuition.
Qed.

Definition Trace := list (name * (input + list output)).

Definition net_reachable (net : network) : Prop :=
  exists (tr : Trace), refl_trans_1n_trace step_async step_async_init net tr.

Definition net_reachable' (net : network) (tr : Trace) : Prop :=
  refl_trans_1n_trace step_async step_async_init net tr.

Definition c_finished net c : Prop :=
  (nwState net c).(child_todo) = [].

Definition c_no_change_step net c : Prop :=
  forall net2 tr2,
  step_async (params := Checker_MultiParams) net net2 tr2 ->
  nwState net2 c = nwState net c.

Definition c_no_change net c : Prop :=
  forall net2 tr2,
  refl_trans_1n_trace step_async  net net2 tr2 ->
  nwState net2 c = nwState net c.

Lemma terminated_no_change_s : forall net c,
  net_reachable net ->
  c_finished net c ->
  c_no_change_step net c.
Proof.
  unfold c_no_change_step. unfold c_finished. unfold net_reachable.
  intros net c H1 H. intros.
  destruct H1. simpl in *.
  inversion H0 ; simpl in * ; subst ; intuition.
  + unfold NetHandler in H3.
    repeat break_match ; subst ; intuition ; simpl in * ; break_match ; subst ; intuition ; destruct d.
    - inversion H3. subst. auto.
    - rewrite H in Heql0. inversion Heql0.
    - rewrite H in Heql0. inversion Heql0.
  + unfold InputHandler in H2.
    repeat break_match ; subst ; intuition ; simpl in * ; break_match ; subst ; intuition ; destruct d.
    - inversion H2. auto.
    - inversion H2. auto.
Qed.

Lemma terminated_no_change_s' : forall net net2 tr2 c,
  net_reachable net ->
  c_finished net c ->
  step_async (params := Checker_MultiParams) net net2 tr2 ->
  c_finished net2 c.
Proof.
  intros net net2 tr2 c H7 H H0.
  assert (c_no_change_step net c).
  apply (terminated_no_change_s net) ; auto.
  unfold c_finished in *. unfold net_reachable in *.
  destruct H7.
  unfold c_no_change_step in H1.
  specialize (H1 net2 tr2).
  intuition.
  rewrite H3. auto.
Qed.

Lemma terminated_no_change : forall net c,
  net_reachable net ->
  c_finished net c ->
  c_no_change net c.
Proof.
  intros net c H7 H.
  unfold c_no_change.
  intros.
  induction H0 using refl_trans_1n_trace_n1_ind ; intuition ; simpl in *.
  unfold c_finished in H.
  rewrite <- H2 in *.
  assert (c_finished x' c).
  unfold c_finished.
  auto.
  assert (c_finished x'' c).
  apply (terminated_no_change_s' x' x'' tr2 c) ; auto.
  unfold net_reachable in *. destruct H7.
  exists (x0 ++ tr1).
  apply (refl_trans_1n_trace_trans H3) ; auto.
  assert (c_no_change_step x' c).
  apply (terminated_no_change_s x' c) ; auto.
  unfold net_reachable.
  unfold net_reachable in *. destruct H7.
  exists (x0 ++ tr1).
  apply (refl_trans_1n_trace_trans H4) ; auto.
  unfold c_no_change_step in H4.
  apply (H4 x'' tr2) ; auto.
Qed.

Theorem root_ends_false_witness_inconsistent: forall net (tr : Trace) (c : Name),
  net_reachable' net tr ->
  In (c, inr [false]) tr ->
  ~ Witness_consistent.

Theorem everything_can_end : forall b net tr,
  net_reachable' net tr ->
  {net2 : network & {tr2 : Trace & 
    refl_trans_1n_trace step_async net net2 tr2 /\
    In (root, inr [b]) (tr ++ tr2)}}.

Theorem every_step_is_towards_an_end : forall b net tr net2 tr2,
  net_reachable' net tr ->
  step_async net net2 tr2 ->
  {net3 : network & {tr3 : Trace & 
    refl_trans_1n_trace step_async net2 net3 tr3 /\
    In (root, inr [b]) (tr ++ tr2 ++ tr3)}}.


Inductive n_step : nat -> network -> network -> Prop :=
  | n_step0 : forall net net2, net = net2 -> n_step 0 net net2
  | n_stepn : forall n net net2, 
                (exists net', n_step (n-1) net net' /\ 
                 exists tr, step_async (params := Checker_MultiParams) net' net2 tr) ->
                   n_step n net net2.

Variable Component_count : nat.

Theorem terminates_after_2n : forall (net : network) (b : bool) (tr : Trace),
  n_step (2*Component_count) step_async_init net ->
  net_reachable' net tr ->
  In (root, inr [b]) tr.
  


Axiom input_to_every_comp : forall (net : network) (tr : Trace),
  net_reachable' net tr ->
  exists (net2 : network), exists (tr2 : Trace),
    refl_trans_1n_trace step_async net net2 tr2 /\
    forall (c : Name) (cert : Certificate), v (name_component c) ->
      In (c, inl cert) tr.


Function filter_inputs (tr : Trace) : list (Name * Input) :=
  match tr with
  | [] => []
  | (c, inl cert) :: tl => (c, cert) :: filter_inputs tl
  | (c, inr cert) :: tl => filter_inputs tl
  end.

Axiom no_duplicate_inputs : forall (net : network) (tr : Trace),
  net_reachable' net tr ->
  NoDup (filter_inputs tr).























Lemma terminated_means_no_change_global: forall net net2 tr c,
  (forall (c : Component), (nwState net (Checker c)).(terminated) = true) ->
  step_async_star (params := Checker_MultiParams) net net2 tr ->
  nwState net2 (Checker c) = nwState net (Checker c).
Proof.
  intros net net2 tr c H0 H1.
  apply (terminated_means_no_change net net2 tr c) ; auto.
Qed.

Lemma Drei_zwei' : forall c,
  is_consistent (nwState step_async_init (Checker c)).(assign_list).
Proof.
  intros c.
  simpl.
  apply init_combined_is_consistent.
Qed.

Lemma Drei_zwei'' : forall net tr c,
  step_async_star (params := Checker_MultiParams) step_async_init net tr ->
  (is_consistent (nwState net (Checker c)).(assign_list)) ->
  (nwState net (Checker c)).(consistent) = true.
Proof.
  intros net tr c H H0.
  remember step_async_init as y in *.
  assert (is_consistent (nwState step_async_init (Checker c)).(assign_list)) as new.
  apply Drei_zwei'.
  induction H using refl_trans_1n_trace_n1_ind.
  + subst.
    simpl in *.
    reflexivity.
  + subst.
    simpl in *.
    assert (is_consistent (assign_list (nwState x' (Checker c)))).
    assert (exists xyz: Certificate, assign_list (nwState x'' (Checker c)) = assign_list (nwState x' (Checker c)) ++ xyz).
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
          assert (assign_list d = assign_list (nwState x' (Checker c)) ++ pBody p). rewrite <- H8. auto.
          rewrite H1 in H0. apply <- check_assign_list_works in H0. auto.
        rewrite <- e in *. inversion H6. rewrite H4 in *. reflexivity.
        auto.
        auto.
        auto.
        auto.
    - simpl in *.
      unfold InputHandler in H5.
      repeat break_match.
        inversion H5. rewrite <- e in *. auto.
        apply <- check_assign_list_works in H0. rewrite <- e in *. inversion H5. simpl in *.
          assert (assign_list d = assign_list (nwState x' (Checker c))). rewrite <- H7. auto.
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
  is_consistent (nwState net (Checker c)).(assign_list)).
Proof.
  intros net tr c H H1.

  {
  unfold is_consistent.
  destruct assign1. destruct assign2.
  intros.
  remember step_async_init as y in *.
  assert (is_consistent (assign_list (nwState step_async_init (Checker c)))) as H19.
  simpl.
  apply init_combined_is_consistent.
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
        assert (assign_list d = assign_list (nwState x' (Checker c))).
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
          apply check_assign_list_works in H13.
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
          apply check_assign_list_works in H12.
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
  ~ is_consistent (nwState net (Checker c)).(assign_list).
Proof.
  intros net tr c H H0.
  remember step_async_init as y in *.
  induction H0 using refl_trans_1n_trace_n1_ind.
  + subst.
    intuition.
  + subst. simpl in *.
    assert (exists xyz: Certificate, assign_list (nwState x'' (Checker c)) = assign_list (nwState x' (Checker c)) ++ xyz).
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
        apply app_inv_head in H1. rewrite H1 in *. apply check_assign_list_works in H2'.
        apply (eq_true_false_abs (check_assign_list (assign_list (nwState x' (Checker c)) ++ x)) H2' H).
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
        apply <- check_assign_list_works in H0.
        apply (eq_true_false_abs (check_assign_list (assign_list (nwState x' (Checker c)))) H0 H).
        apply (eq_true_false_abs (consistent (nwState x' (Checker c))) H2 H).
        rewrite <- e in *. inversion H4. rewrite <- H6 in H. simpl in *.
        apply (eq_true_false_abs (consistent (nwState x' (Checker c))) H2 H).
        apply (eq_true_false_abs (consistent (nwState x' (Checker c))) H2 H).
Qed.


Lemma cert_stays_in_assign_list : forall net tr c a,
  step_async_star step_async_init net tr ->
  In a (init_combined c) ->
  In a (assign_list (nwState net (Checker (name_component c)))).
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
  right. exists (parent pDst, assign_list (nwState x' pDst) ++ pBody).
  auto.
Qed.

Lemma Nethandler_correct: forall x' p out d nextDst msg,
  NetHandler (pDst p) (pSrc p) (pBody p) (nwState x' (pDst p)) = (out, d, [(nextDst, msg)]) ->
  (parent (pDst p) = nextDst) /\ (msg = (assign_list (nwState x' (pDst p))) ++ pBody p).
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
  exists ((parent h, assign_list (nwState x' h))). auto.
  left. auto.
Qed.

Lemma Inputhandler_correct: forall inp0 x' h out d nextDst msg,
  InputHandler h inp0 (nwState x' h) = (out, d, [(nextDst, msg)]) ->
  (parent h = nextDst) /\ (msg = (assign_list (nwState x' h))).
Proof.
  intros.
  unfold InputHandler in H.
  repeat (break_match ; subst ; simpl in * ; inversion H).
  auto.
Qed.

Lemma only_child_in_assign_list: forall net tr c a,
  step_async_star (params := Checker_MultiParams) step_async_init net tr ->
  In a (assign_list (nwState net (Checker c))) -> exists d : Name, In d ((component_name c) :: (children (component_name c))) /\ In a (assign_list (nwState net d)).
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



Lemma packet_source_terminated : forall x tr,
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

Lemma packet_source_terminated' : forall x tr,
  refl_trans_1n_trace step_async step_async_init x tr -> forall (pSrc pDst : Name) pBody,
  In {| pSrc := pSrc; pDst := pDst; pBody := pBody |} (nwPackets x) -> 
  terminated (nwState x pSrc) = true.
Proof.
  intros.
  assert (forall x tr,
  refl_trans_1n_trace step_async step_async_init x tr -> forall p,
  In p (nwPackets x) -> let (pSrc, pDst, pBody) := p in
  terminated (nwState x pSrc) = true).
  apply (packet_source_terminated).
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

Lemma p_dst_eq_psrc : forall x tr,
  refl_trans_1n_trace step_async step_async_init x tr -> forall p,
  In p (nwPackets x) -> let (pSrc, pDst, pBody) := p in
  pDst = parent pSrc.
Proof.
  intros x tr H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind ; intros ; subst ; simpl in *.
  + inversion H.
  + assert (H2' := H2).
    apply (packet_source_terminated x'' (tr1 ++ tr2)) in H2' ; auto.
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

Lemma packets_dst_eq_src : forall x (tr : list (Name * (Input + list Output))),
  refl_trans_1n_trace step_async step_async_init x tr -> forall (pSrc pDst: Name) (pBody : Msg),
  In {| pSrc := pSrc; pDst := pDst; pBody := pBody |} (nwPackets x) -> 
  pDst = parent pSrc.
Proof.
  intros.
  assert (forall x tr,
  refl_trans_1n_trace step_async step_async_init x tr -> forall p,
  In p (nwPackets x) -> let (pSrc, pDst, pBody) := p in
  pDst = parent pSrc).
  apply p_dst_eq_psrc.
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
        apply (packet_source_terminated' x' tr1 H pSrc pDst pBody) ; auto.
        rewrite H4. apply in_or_app. simpl. auto. 
        destruct p. simpl in *. subst. apply eqb_false_iff in Heqb. intuition.
      apply (H3 (pDst p) (pDst p) ) ; auto.
      apply (H3 c (pDst p)) ; auto.
      apply (H3 (pDst p) d) ; auto.
      apply (H3 c d) ; auto.
      apply (H3 (pDst p) d) ; auto.
      apply (H3 c d) ; auto.
      destruct p. simpl in *. rewrite <- H0 in *.
        apply (packet_source_terminated' x' tr1 H pSrc pDst pBody) ; auto.
        rewrite H4. apply in_or_app. simpl. auto.
      apply (H3 (pDst p) d) ; auto.
      apply (H3 c d ) ; auto.
      destruct p. simpl in *. rewrite <- H0 in *.
        apply (packet_source_terminated' x' tr1 H pSrc pDst pBody) ; auto.
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

Lemma NoDup_packets : forall x' tr,
  step_async_star (params := Checker_MultiParams) step_async_init x' tr ->
  NoDup (nwPackets x').
Proof.
  intros net tr H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind ; simpl in *.
  + subst.
    simpl in *.
    intuition.
  + subst. simpl in *.
    intuition.
    invc H0 ; simpl in * ; intuition.
    - destruct p. simpl in *.
      assert ((nwState x' pSrc).(terminated) = true).
      apply (packet_source_terminated' x' tr1 H pSrc pDst pBody) ; auto.
      rewrite H3. apply in_or_app. simpl. auto.
      assert (pDst = parent pSrc).
      apply (packets_dst_eq_src x' tr1 H pSrc pDst pBody) ; auto.
      rewrite H3. apply in_or_app. simpl. auto.

      subst.
      unfold NetHandler in H4.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H4 ; subst ; simpl in * ; intuition ; rewrite H3 in *.
      apply NoDup_remove_1 in H2 ; auto.
      apply NoDup_remove_1 in H2 ; auto.
      apply NoDup_remove in H2. destruct H2.
      apply NoDup_cons ; auto. intuition.
      assert ((nwState x' (parent pSrc)).(terminated) = true).
      apply (packet_source_terminated' x' tr1 H (parent pSrc) (parent (parent pSrc)) (assign_list (nwState x' (parent pSrc)) ++ pBody)) ; auto.
      rewrite H3. apply in_or_app. simpl. apply in_app_or in H6. destruct H6 ; auto.
      apply eqb_false_iff in Heqb. intuition.
      apply NoDup_remove_1 in H2 ; auto.
    - unfold InputHandler in H3.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H3 ; subst ; simpl in * ; intuition.
      apply NoDup_cons ; auto.
      intuition.
      assert ((nwState x' h).(terminated) = true).
      apply (packet_source_terminated' x' tr1 H h (parent h) (assign_list (nwState x' h))) ; auto.
      apply eqb_false_iff in Heqb. intuition.
Qed.

Lemma not_parent_in_packets : forall x' tr,
  step_async_star (params := Checker_MultiParams) step_async_init x' tr ->
  (
  forall pSrc pDst pBody pDst2 pBody2,
  In {| pSrc := pSrc; pDst := pDst; pBody := pBody |} (nwPackets x') ->
  In {| pSrc := parent pSrc; pDst := pDst2; pBody := pBody2 |} (nwPackets x') -> 
  (pSrc = parent pSrc /\ pDst = pDst2 /\ pBody = pBody2)).
Proof.
(*     Dieses Lemma kann man nicht induktiv beweisen.
       Das liegt daran, dass man mit einem induktiven Beweis f\u00fcr alle Situationen, in denen die 
       Vorbedingung gilt, zeigen kann, dass die Nachbedingung gilt. Hier wollen wir die Nachbedingung
       beweisen, _obwohl die Vorbedingung nicht gilt_. (Zumindest in manchen Unterf\u00e4llen nicht.)
       In solchen Situationen hat ein induktiver Beweis keine Aussagekraft.     *)
intros net tr H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind ; intros pSrc pDst pBody pDst2 pBody2 H2 H3 ; simpl in *.
  + subst.
    simpl in *.
    intuition.
  + subst. simpl in *.
    intuition.
    assert (pDst = parent pSrc) as pDst'.
    apply (packets_dst_eq_src x'' (tr1 ++ tr2) H1 pSrc pDst pBody) ; auto.
    subst.
    invc H0 ; simpl in * ; intuition.
    - destruct p. simpl in *.
      assert ((nwState x' pSrc0).(terminated) = true).
      apply (packet_source_terminated' x' tr1 H pSrc0 pDst pBody0) ; auto.
      rewrite H5. apply in_or_app. simpl. auto.
      assert (pDst = parent pSrc0).
      apply (packets_dst_eq_src x' tr1 H pSrc0 pDst pBody0) ; auto.
      rewrite H5. apply in_or_app. simpl. auto.

      subst.
      unfold NetHandler in H6.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H6 ; subst ; simpl in * ; intuition ; rewrite H5 in * ; clear H6.
      apply (H4 pSrc (parent pSrc) pBody pDst2 pBody2) ; auto.
      apply in_or_app. simpl. apply in_app_or in H2. destruct H2 ; auto.
      apply in_or_app. simpl. apply in_app_or in H3. destruct H3 ; auto.
      apply (H4 pSrc (parent pSrc) pBody pDst2 pBody2) ; auto.
      apply in_or_app. simpl. apply in_app_or in H2. destruct H2 ; auto.
      apply in_or_app. simpl. apply in_app_or in H3. destruct H3 ; auto.
      inversion H7. inversion H3. subst. auto.
      inversion H7. subst. rewrite H6 in *.
      clear H7. admit.
      inversion H3. subst. admit.
      apply (H4 pSrc (parent pSrc) pBody pDst2 pBody2) ; auto.
      apply in_or_app. simpl. apply in_app_or in H3. destruct H3 ; auto.
      apply in_or_app. simpl. apply in_app_or in H7. destruct H7 ; auto.
      apply (H4 pSrc (parent pSrc) pBody pDst2 pBody2) ; auto.
      apply in_or_app. simpl. apply in_app_or in H2. destruct H2 ; auto.
      apply in_or_app. simpl. apply in_app_or in H3. destruct H3 ; auto.
    - 
Admitted.

Lemma pbody_is_asslist : forall x' tr,
  step_async_star (params := Checker_MultiParams) step_async_init x' tr ->
  (
  forall pSrc pDst pBody,
  In {| pSrc := pSrc; pDst := pDst; pBody := pBody |} (nwPackets x') ->
  pBody = (nwState x' pSrc).(assign_list)).
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
      apply (packet_source_terminated' x' tr1 H pSrc0 pDst0 pBody0) ; auto.
      rewrite H4. apply in_or_app. simpl. auto.
      assert (pDst0 = parent pSrc0).
      apply (packets_dst_eq_src x' tr1 H pSrc0 pDst0 pBody0) ; auto.
      rewrite H4. apply in_or_app. simpl. auto.

      subst.
      unfold NetHandler in H5.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H5 ; subst ; simpl in * ; intuition ; rewrite H4 in *.
      apply (H3 (parent pSrc0) pDst pBody) ; auto. apply in_or_app. simpl. apply in_app_or in H2. destruct H2 ; auto.
      apply (H3 (parent pSrc0) pDst pBody) ; auto. apply in_or_app. simpl. apply in_app_or in H2. destruct H2 ; auto.
      inversion H6. subst. auto.

      assert (In {| pSrc := pSrc0; pDst := parent pSrc0; pBody := pBody0 |} (nwPackets x')).
      rewrite H4. apply in_or_app. simpl. auto.
      apply (not_parent_in_packets x' tr1 H _ _ _ pDst pBody) in H2 ; auto.
      assert (In {| pSrc := parent pSrc0; pDst := pDst; pBody := pBody |} (nwPackets x')).
      rewrite H4.
      apply in_or_app. simpl. apply in_app_or in H6. destruct H6 ; auto. intuition.
      subst.
      assert (NoDup (nwPackets x')).
      apply (NoDup_packets x' tr1) ; auto. rewrite H4 in *.
      apply NoDup_remove in H2. rewrite <- H8 in *. destruct H2. intuition.
      rewrite H4 in *.
      apply in_or_app. simpl. apply in_app_or in H6. destruct H6 ; auto. intuition.

      assert (In {| pSrc := pSrc0; pDst := parent pSrc0; pBody := pBody0 |} (nwPackets x')).
      rewrite H4. apply in_or_app. simpl. auto.
      apply (not_parent_in_packets x' tr1 H _ _ _ pDst pBody) in H6.
      assert (In {| pSrc := parent pSrc0; pDst := pDst; pBody := pBody |} (nwPackets x')).
      rewrite H4.
      apply in_or_app. simpl. apply in_app_or in H2. destruct H2 ; auto. intuition.
      subst.
      assert (NoDup (nwPackets x')).
      apply (NoDup_packets x' tr1) ; auto. rewrite H4 in *.
      apply NoDup_remove in H6. rewrite <- H8 in *. destruct H6. intuition.
      rewrite H4 in *.
      apply in_or_app. simpl. apply in_app_or in H2. destruct H2 ; auto. intuition.



      apply (H3 pSrc pDst pBody) ; auto. apply in_or_app. simpl. apply in_app_or in H2. destruct H2 ; auto.
      apply (H3 pSrc pDst pBody) ; auto. apply in_or_app. simpl. apply in_app_or in H2. destruct H2 ; auto.
      inversion H6. subst. intuition.
      apply (H3 pSrc pDst pBody) ; auto. apply in_or_app. simpl. apply in_app_or in H6. destruct H6 ; auto.
      apply (H3 pSrc pDst pBody) ; auto. apply in_or_app. simpl. apply in_app_or in H2. destruct H2 ; auto.
    - specialize (H3 pSrc pDst pBody).
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
(*     Dieses Lemma kann man nicht induktiv beweisen.
       Das liegt daran, dass man mit einem induktiven Beweis f\u00fcr alle Situationen, in denen die 
       Vorbedingung gilt, zeigen kann, dass die Nachbedingung gilt. Hier wollen wir die Nachbedingung
       beweisen, _obwohl die Vorbedingung nicht gilt_. (Zumindest in manchen Unterf\u00e4llen nicht.)
       In solchen Situationen hat ein induktiver Beweis keine Aussagekraft.     *)
  intros net tr H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind ; intros pSrc pDst pBody H2 psrcpdst ; simpl in *.
  + subst.
    simpl in *.
    intuition.
  + subst. simpl in *.
    intuition.
    assert (pDst = parent pSrc) as pDst'.
    apply (packets_dst_eq_src x'' (tr1 ++ tr2) H1 pSrc pDst pBody) ; auto.
    subst.
    invc H0 ; simpl in * ; intuition.
    - (* unfold NetHandler in H5.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H5 ; subst ; simpl in * ; intuition. admit. admit.
      inversion H0. subst. *)
      assert (forall n m , l = [(n, m)] -> (parent (Net.pDst p) = n) /\ (m = (assign_list (nwState x' (Net.pDst p))) ++ Net.pBody p)) as new.
      intros. subst.
      apply (Nethandler_correct x' p out d) ; auto.

      destruct p. simpl in *.

      assert (pBody0 = (nwState x' pSrc0).(assign_list)) as newnewnew.
      apply (pbody_is_asslist x' tr1 H pSrc0 pDst pBody0) ; auto.
      rewrite H4. apply in_or_app. simpl. auto.
      assert ((nwState x' pSrc0).(terminated) = true).
      apply (packet_source_terminated' x' tr1 H pSrc0 pDst pBody0) ; auto.
      rewrite H4. apply in_or_app. simpl. auto.
      assert (pDst = parent pSrc0).
      apply (packets_dst_eq_src x' tr1 H pSrc0 pDst pBody0) ; auto.
      rewrite H4. apply in_or_app. simpl. auto.

      subst.
      unfold NetHandler in H5.
(*       repeat break_match ; simpl in * ; simpl in * ; intuition ; inversion H5 ; simpl in * ; intuition.
      admit. admit. admit. admit. admit. admit. subst. simpl in *. intuition. *)

      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H5 ; subst ; simpl in * ; intuition ; clear H5.
      rewrite H4 in *. rewrite <- e. apply (H3 pSrc (parent pSrc) pBody) ; auto.
      apply in_app_or in H2. destruct H2 ; apply in_or_app ; simpl ; auto.
      specialize (H3 pSrc (parent pSrc) pBody).
      rewrite e in *. rewrite Heql0 in *. rewrite H4 in *.
      assert (In pSrc []). apply H3 ; auto.
      apply in_app_or in H2. destruct H2 ; apply in_or_app ; simpl ; auto. inversion H5.
      inversion H6. subst. intuition.
      assert (H3' := H3).
      specialize (H3' pSrc (parent pSrc) pBody).
      rewrite e in *. rewrite Heql0 in *. rewrite H4 in *.
      assert (In {| pSrc := pSrc; pDst := (parent pSrc0); pBody := pBody |}
        (xs ++ {| pSrc := pSrc0; pDst := parent pSrc0; pBody := assign_list (nwState x' pSrc0) |} :: ys)).
      apply in_or_app. simpl. apply in_app_or in H6. destruct H6 ; auto. intuition.
      specialize (H3 pSrc0 (parent pSrc0) (assign_list (nwState x' pSrc0))).
      assert (In {| pSrc := pSrc0; pDst := parent pSrc0; pBody := assign_list (nwState x' pSrc0) |}
       (xs ++ {| pSrc := pSrc0; pDst := parent pSrc0; pBody := assign_list (nwState x' pSrc0) |} :: ys)).
      apply in_or_app. simpl. auto.
      intuition. rewrite Heql0 in *.
      assert (pSrc0 = parent pSrc0 \/ pSrc0 <> parent pSrc0).
      apply classic.
      destruct H3.
      subst. rewrite <- H3 in *. rewrite <- H3 in *. subst.
      (* pSrc and (parent pSrc) in the list of x'' *)
      admit.
      intuition. inversion H9 ; intuition. inversion H7 ; intuition.
      subst. (* pSrc and (parent pSrc) in the list of x'' *)
      admit.
      assert ((remove_src pSrc0 (n :: n0 :: l1)) = if component_index (name_component pSrc0) =? component_index (name_component n)
   then n0 :: l1
   else
    n
    :: (if component_index (name_component pSrc0) =? component_index (name_component n0)
        then l1
        else n0 :: remove_src pSrc0 l1)).
      simpl. auto.
      rewrite <- H5 in *.
      assert (H3' := H3).
      specialize (H3 pSrc (parent pSrc) pBody).
      specialize (H3' pSrc0 (parent pSrc0) (assign_list (nwState x' pSrc0))).
      rewrite <- e in *.
      rewrite H4 in *. rewrite Heql0 in *.
      assert (pSrc = pSrc0 \/ pSrc <> pSrc0).
      apply classic.
      destruct H6. subst. (* pSrc0 zweimal in nwPackets x' drin *)
      admit.
      assert (In pSrc (n :: n0 :: l1)).
      apply H3 ; auto.
      apply in_or_app. simpl. apply in_app_or in H2. destruct H2 ; auto.
      apply remove_src_still_in ; auto.
      apply (H3 pSrc (parent pSrc) pBody) ; auto. rewrite H4 in *.
      apply in_app_or in H2. destruct H2 ; apply in_or_app ; simpl ; auto.
      apply (H3 pSrc (parent pSrc) pBody) ; auto. rewrite H4 in *.
      apply in_app_or in H2. destruct H2 ; apply in_or_app ; simpl ; auto.
      inversion H6. subst. clear H7 n H6 new.
      rewrite H4 in *. assert (H3' := H3).
(*       specialize (H3' pSrc0 (parent pSrc0) (assign_list (nwState x' pSrc0))).
      assert (pSrc0 = parent pSrc0 -> False). admit.
      assert (In {| pSrc := pSrc0; pDst := parent pSrc0; pBody := assign_list (nwState x' pSrc0) |}
        (xs ++ {| pSrc := pSrc0; pDst := parent pSrc0; pBody := assign_list (nwState x' pSrc0) |} :: ys)).
      admit. rewrite Heql0 in *. intuition. *)
      specialize (H3 (parent pSrc0) (parent (parent pSrc0)) (assign_list (nwState x' (parent pSrc0)))).
      apply H3 ; auto. admit.


      apply (H3 pSrc (parent pSrc) pBody) ; auto. rewrite H4 in *.
      apply in_app_or in H6. destruct H6 ; apply in_or_app ; simpl ; auto.
      apply (H3 pSrc (parent pSrc) pBody) ; auto. rewrite H4 in *.
      apply in_app_or in H2. destruct H2 ; apply in_or_app ; simpl ; auto.
  - unfold InputHandler in H4.
    specialize (H3 pSrc (parent pSrc) pBody).
    repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H4 ; subst ; simpl in * ; intuition ; clear H4.
    inversion H0. subst. symmetry in H4. intuition.
    inversion H0. subst.
    admit.
Admitted.

Lemma child_done_in_assign_list: forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr -> (forall c d,
    (In d (child_done (nwState net c))) ->
    (forall e, In e (nwState net d).(assign_list) -> In e (nwState net c).(assign_list))).
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
    - assert (forall n m , l = [(n, m)] -> (parent (pDst p) = n) /\ (m = (assign_list (nwState x' (pDst p))) ++ pBody p)) as new.
      intros. subst.
      apply (Nethandler_correct x' p out d0) ; auto.

      destruct p. simpl in *.
      assert (pBody = (nwState x' pSrc).(assign_list)) as newnewnew.
      apply (pbody_is_asslist x' tr1 H pSrc pDst pBody) ; auto.
      rewrite H5. apply in_or_app. simpl. auto.


      assert ((nwState x' pSrc).(terminated) = true).
      apply (packet_source_terminated' x' tr1 H pSrc pDst pBody) ; auto.
      rewrite H5. apply in_or_app. simpl. auto.
      assert (pDst = parent pSrc).
      apply (packets_dst_eq_src x' tr1 H pSrc pDst pBody) ; auto.
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

      assert (pBody = (nwState x' pSrc).(assign_list)) as newnewnew.
      apply (pbody_is_asslist x' tr1 H pSrc pDst pBody) ; auto.
      rewrite H3. apply in_or_app. simpl. auto.


      assert ((nwState x' pSrc).(terminated) = true).
      apply (packet_source_terminated' x' tr1 H pSrc pDst pBody) ; auto.
      rewrite H3. apply in_or_app. simpl. auto.
      assert (pDst = parent pSrc).
      apply (packets_dst_eq_src x' tr1 H pSrc pDst pBody) ; auto.
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
    - assert (forall n m , l = [(n, m)] -> (parent (pDst p) = n) /\ (m = (assign_list (nwState x' (pDst p))) ++ pBody p)) as new.
      intros. subst.
      apply (Nethandler_correct x' p out d) ; auto.

      destruct p. simpl in *.

      assert (pBody = (nwState x' pSrc).(assign_list)) as newnewnew.
      apply (pbody_is_asslist x' tr1 H pSrc pDst pBody) ; auto.
      rewrite H3. apply in_or_app. simpl. auto.


      assert ((nwState x' pSrc).(terminated) = true).
      apply (packet_source_terminated' x' tr1 H pSrc pDst pBody) ; auto.
      rewrite H3. apply in_or_app. simpl. auto.
      assert (pDst = parent pSrc).
      apply (packets_dst_eq_src x' tr1 H pSrc pDst pBody) ; auto.
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
      apply (pSrc_in_child_todo x' tr1 H pSrc (parent pSrc) (nwState x' pSrc).(assign_list)) ; auto.
      rewrite H3. apply in_or_app. simpl. right. auto.
      rewrite Heql0 in newnew. simpl in newnew. destruct newnew. auto. intuition.
      specialize (H2 (parent pSrc)). rewrite Heql0 in H2. subst.
      rewrite app_nil_r. 
      assert (Permutation (pSrc :: child_done (nwState x' (parent pSrc))) (child_done (nwState x' (parent pSrc)) ++ [pSrc])).
      apply Permutation_cons_append.
      apply Permutation_sym. apply Permutation_sym in H2. apply Permutation_sym in H5.
      apply (Permutation_trans H2 H5) ; auto.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H4 ; subst ; simpl in * ; intuition.
      apply cinc in Heqb0. subst.
      specialize (H2 (parent n)). rewrite Heql0 in H2. auto.
      assert (Permutation (n :: child_done (nwState x' (parent n)) ++ n0 :: l1) (child_done (nwState x' (parent n)) ++ n :: n0 :: l1)).
      apply (Permutation_cons_app (child_done (nwState x' (parent n))) ) ; auto.
      apply Permutation_sym. apply Permutation_sym in H2. apply Permutation_sym in H5.
      apply (Permutation_trans H2 H5) ; auto.
      apply cinc in Heqb1. subst.
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


      apply (pSrc_in_child_todo x' tr1 H pSrc (parent pSrc) (nwState x' pSrc).(assign_list)) ; auto.
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
  (forall (d : Name), descendand d c = true -> 
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
      apply (packet_source_terminated' x' tr1 H pSrc pDst pBody) ; auto.
      rewrite H4. apply in_or_app. simpl. auto.
      assert (pDst = parent pSrc).
      apply (packets_dst_eq_src x' tr1 H pSrc pDst pBody) ; auto.
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
      clear H5 H2.
        assert (In pSrc (child_todo (nwState x' (parent pSrc)))).
        assert (pSrc = (parent pSrc) \/ pSrc <> (parent pSrc)).
        apply classic. destruct H2. rewrite <- H2 in *. apply eqb_false_iff in Heqb. intuition.
        apply (pSrc_in_child_todo x' tr1 H _ (parent pSrc) pBody) ; auto.
        rewrite H4. apply in_or_app. simpl. auto.
        rewrite Heql0 in H2. inversion H2 ; subst ; intuition. clear H2.
        assert (exists (child : Name), In child (children (parent pSrc)) /\ descendand d child = true).
        clear H6 H0 H4 Heql0 Heqb H1 xs ys pBody H tr1 x'.
        unfold descendand in *. unfold parent in *.
        apply (child_exists v a g d (parent' v a g pSrc)) ; auto.
        repeat destruct H2.
        assert (forall c : name, Permutation (child_done (nwState x' c) ++ child_todo (nwState x' c)) (children c)).
        apply (child_done_children_list_children x' tr1) ; auto.
        specialize (H7 (parent pSrc)).
        apply Permutation_sym in H7.
        apply (Permutation_in _ H7) in H2.
        apply in_app_or in H2. destruct H2.
        apply (child_done_terminated x' tr1) in H2 ; auto.
        apply (H6 x) ; auto.
        rewrite Heql0 in H2. inversion H2 ; subst ; intuition.
        apply (H6 x) ; auto.
      apply (H6 c) ; auto.
      apply (H6 (parent pSrc)) ; auto.
      apply (H6 c) ; auto.
    - intuition.
      specialize (H0 c).
      unfold InputHandler in H4.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H4 ; subst ; simpl in * ; intuition.
      clear H4 Heqb H1 H2 inp0 H0 H tr1.
      assert (False).
      clear x'.
      apply n. unfold children in Heql0. unfold descendand in H3.
      apply (empty_subtree v a g) ; auto.
      inversion H.
Qed.


Lemma all_subtree_in_assign_list: forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr -> (forall c,
  (nwState net (Checker c)).(terminated) = true ->
  (forall d, descendand (component_name d) (component_name c) = true ->
    (forall e, In e (nwState net (Checker d)).(assign_list) -> In e (nwState net (Checker c)).(assign_list)))).
Proof.
  intros.
  assert (H0' := H0).
  apply (terminated_child_todo_null net tr) in H0' ; auto.
  assert (Permutation (child_done (nwState net (Checker c))) (children (Checker c))).
  assert (Permutation ((nwState net (Checker c)).(child_done) ++ (nwState net (Checker c)).(child_todo)) (children (Checker c))).
  apply (child_done_children_list_children net tr) ; auto.
  rewrite H0' in *. rewrite app_nil_r in H3. auto.
  assert (forall d, Permutation (children (Checker c)) (child_done (nwState net (Checker c))) -> In d (children (Checker c)) -> In d (child_done (nwState net (Checker c)))).
  apply Permutation_in.
  apply Permutation_sym in H3.
  assert (forall d : Name, In d (children (Checker c)) -> In d (child_done (nwState net (Checker c)))).
  intros.
  apply (H4 d0) ; auto.
  clear H4.
  assert (forall d' d : Name, descendand' v a g d' (Checker c) = true -> In d (children d') -> (forall e, In e (nwState net d).(assign_list) -> In e (nwState net d').(assign_list))).
  intros.
  apply (child_done_in_assign_list net tr H d' d0) ; auto.
  assert (terminated (nwState net d') = true).
  apply (all_subtree_terminated net tr H (Checker c)) ; auto.
  destruct d'.
  apply (terminated_child_todo_null net tr) in H8 ; auto.
  assert (Permutation (child_done (nwState net (Checker c0))) (children (Checker c0))).
  assert (Permutation ((nwState net (Checker c0)).(child_done) ++ (nwState net (Checker c0)).(child_todo)) (children (Checker c0))).
  apply (child_done_children_list_children net tr) ; auto.
  rewrite H8 in *. rewrite app_nil_r in H9. auto.
  assert (forall d, Permutation (children (Checker c0)) (child_done (nwState net (Checker c0))) -> In d (children (Checker c0)) -> In d (child_done (nwState net (Checker c0)))).
  apply Permutation_in.
  apply Permutation_sym in H9. apply H10 ; auto.
  apply (descendand_trans v a g (Checker c) (Checker d)) ; auto.
  intros.

  apply (H4 e0 d0) ; auto.
Qed.




Lemma packet_msg_from_descendand : forall x tr a0,
  refl_trans_1n_trace step_async step_async_init x tr -> 
  (((forall p, In p (nwPackets x) -> ((let (pSrc, pDst, pBody) := p in
  (In a0 pBody -> exists d : Name, descendand d pSrc = true /\ In a0 (init_combined d))))) /\
  forall c, In a0 (assign_list (nwState x (Checker c))) -> exists d : Name, descendand d (component_name c) = true /\ In a0 (init_combined d))).
Proof.
  intros x tr a0 H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind ; intros ; subst ; simpl in *.
  + split ; intros.
    inversion H.
    exists (component_name c).
    split ; auto.
    apply descendand_refl.
    apply Component_prop_1.
  + intuition.
    assert (H2' := H2).
    apply (packet_source_terminated x'' (tr1 ++ tr2)) in H2' ; auto.
    assert (H2'' := H2).
    apply (p_dst_eq_psrc x'' (tr1 ++ tr2)) in H2'' ; auto.
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
        apply in_or_app. right. simpl. auto. intuition. rewrite cnnc in H2. intuition.
        specialize (H3 {| pSrc := pSrc0; pDst := pDst0; pBody := pBody0 |}).
        assert (In {| pSrc := pSrc0; pDst := pDst0; pBody := pBody0 |} (xs ++ {| pSrc := pSrc0; pDst := pDst0; pBody := pBody0 |} :: ys)).
        apply in_or_app. right. simpl. auto. intuition. intuition.
        destruct H3. exists x. destruct H3. split ; auto.
        unfold descendand in *.
        apply (descendandp1 v a g pDst0 pSrc0 x) ; auto.
        apply (packets_dst_eq_src x' tr1 H pSrc0 pDst0 pBody0) ; auto.
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
      inversion H6. subst. specialize (H4 (name_component h)). unfold component_name in *. rewrite cnnc in H4.
        apply H4. auto.
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
      apply (packet_source_terminated x' tr1) in H0 ; auto. subst. intuition.
      assert (let (pSrc, pDst, pBody) := p in
  In a0 pBody -> 
    exists d : Name, descendand d (component_name (name_component pSrc)) = true /\ In a0 (init_combined d)) as new.
      specialize (H3 p). intuition.
      destruct p ; simpl in *.
      subst. rewrite cnnc in *. intuition.
      unfold NetHandler in H6.  
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H6 ; subst ; simpl in * ; intuition.
      apply in_app_or in H2. destruct H2. intuition.
        specialize (H4 (name_component pSrc)).
        rewrite checker_name in H4.
        intuition. rewrite cnnc in *. destruct H7. destruct H7.
        exists x. split ; auto.
        apply (descendandp1 v a g (Checker c) pSrc) ; auto.
        apply (p_dst_eq_psrc x' tr1) in H0' ; auto.

      apply in_app_or in H2. destruct H2. intuition.
        specialize (H4 (name_component pSrc)).
        rewrite checker_name in H4. intuition. destruct H7. destruct H7.
        exists x. split ; auto. rewrite cnnc in *.
        apply (descendandp1 v a g (component_name c) pSrc) ; auto.
        apply (p_dst_eq_psrc x' tr1) in H0' ; auto.
      intuition.
      simpl in *.
      break_match.
      rewrite <- e in *.
      unfold InputHandler in H5.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H5 ; subst ; simpl in * ; intuition.
      intuition.
Qed.


Lemma only_desc_in_assign_list: forall net tr,
  step_async_star (params := Checker_MultiParams) step_async_init net tr -> (forall a c,
  In a (assign_list (nwState net (Checker c))) -> exists d : Name, descendand d (component_name c) = true /\ In a (init_combined d)).
Proof.
  intros.
  assert (forall x tr a0,
  refl_trans_1n_trace step_async step_async_init x tr -> 
  (((forall p, In p (nwPackets x) -> ((let (pSrc, pDst, pBody) := p in
  (In a0 pBody -> exists d : Name, descendand d pSrc = true /\ In a0 (init_combined d))))) /\
  forall c, In a0 (assign_list (nwState x (Checker c))) -> exists d : Name, descendand d (component_name c) = true /\ In a0 (init_combined d)))).
  apply packet_msg_from_descendand.
  specialize (H1 net tr a0). apply H1 ; auto.
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
  assert (forall d, descendand (component_name d) (root) = true -> 
    (forall e, In e (nwState net (Checker d)).(assign_list) -> In e (nwState net (Checker (name_component root))).(assign_list))).
  destruct root.
  apply (all_subtree_in_assign_list net tr) ; auto.
  rename H3 into Hd.
  assert (forall (c : Name), exists vl el w, parent_walk (name_component c) (name_component root) vl el w) as pwtr.
  unfold parent_walk.
  unfold root.
  intros.
  apply parent_walk_to_root.
  apply Component_prop_1 ; auto.
  assert (forall e : Assignment,
     In e (assign_list (nwState net (Checker (name_component d1)))) ->
     In e (assign_list (nwState net (Checker (name_component root))))).
  apply (Hd (name_component d1)) ; auto.
  rewrite cnnc. unfold descendand. unfold root. apply root_is_ancestor. apply Component_prop_1.
  assert (forall e : Assignment,
     In e (assign_list (nwState net (Checker (name_component d2)))) ->
     In e (assign_list (nwState net (Checker (name_component root))))).
  apply (Hd (name_component d2)) ; auto.
  rewrite cnnc. unfold descendand. unfold root. apply root_is_ancestor. apply Component_prop_1.
  assert (is_consistent (nwState net (Checker (name_component root))).(assign_list)).
  apply (Drei_zwei net tr) ; auto.

  unfold is_consistent in H3.
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
  apply (cert_stays_in_assign_list net tr) ; auto.
  apply H4 ; auto.
  apply (cert_stays_in_assign_list net tr) ; auto.
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
  apply (only_desc_in_assign_list net tr reachable) in H0 ; auto.
  apply (only_desc_in_assign_list net tr reachable) in H1 ; auto.
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
  rewrite cnnc in *.
  unfold descendand in *.
  unfold root in *.

  apply root_is_ancestor2 in H0.
  apply root_is_ancestor2 in H1.
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
  i. sind alle Belegungen der Variablen des Teilbaums in der assign_list
  xii. wenn consistent, dann sind alle Variablen der assign_list sind gleichbelegt
  -> der gesamte Teilbaum hat eine konsistente Belegung
  xiii. wenn nicht consistent, dann existiert eine Variable in der assign_list, die zwei verschiedene Belegungen hat
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