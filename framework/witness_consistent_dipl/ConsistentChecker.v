
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
	match (child_todo data) with
  | [] => ([], data, [(parent me, (assign_list data ++ i))])
  |  _ => ([], (mkData ((assign_list data) ++ i) (children me)), [])
  end.


Definition NetHandler (me : Name) (src: Name) (msg : Certificate) (data: Data) :
    (list Output) * Data * list (Name * Msg) :=
  match (child_todo data) with
      | [] =>
        ([check_assign_list msg], data, [])
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

Definition net_reachable_from (net : network) (net2 : network) : Prop :=
  exists (tr : Trace), refl_trans_1n_trace step_async net net2 tr.

Definition net_reachable_from' (net : network) (net2 : network) (tr : Trace) : Prop :=
  refl_trans_1n_trace step_async net net2 tr.

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
    repeat break_match ; subst ; intuition ; simpl in * ; break_match ; subst ; intuition.
    - inversion H2. auto.
    - inversion H2. subst. rewrite H in Heql0. inversion Heql0.
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

Lemma Drei_zwei' : forall c,
  is_consistent (nwState step_async_init (Checker c)).(assign_list).
Proof.
  intros c.
  simpl.
  unfold is_consistent.
  intros. destruct assign1. destruct assign2. intros. inversion H.
Qed.

Lemma cert_stays_in_ass_list : forall net net2 c a,
  net_reachable_from net net2 ->
  In a (nwState net c).(assign_list) ->
  In a (nwState net2 c).(assign_list).
Proof.
  intros net net2 c a reachable infirst.
  unfold net_reachable_from in reachable.
  destruct reachable.
  remember net as y in *.
  induction H using refl_trans_1n_trace_n1_ind.
  + auto.
  + subst.
    apply IHrefl_trans_1n_trace1 in infirst ; auto.
    clear H1 IHrefl_trans_1n_trace1 H tr1.
    invc H0 ; simpl in * ; break_match ; subst ; intuition.
    - unfold NetHandler in H1.
      repeat break_match ; simpl in * ; inversion H1 ; subst ; auto ; simpl in *.
      apply in_or_app ; auto.
      apply in_or_app ; auto.
    - unfold InputHandler in H.
      repeat break_match ; simpl in * ; inversion H ; subst ; auto ; simpl in *.
      apply in_or_app ; auto.
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
  exists ((parent h, assign_list (nwState x' h) ++ inp0)). auto.
  left. auto.
Qed.

Lemma Inputhandler_correct: forall inp0 x' h out d nextDst msg,
  InputHandler h inp0 (nwState x' h) = (out, d, [(nextDst, msg)]) ->
  (parent h = nextDst) /\ (msg = (assign_list (nwState x' h) ++ inp0)).
Proof.
  intros.
  unfold InputHandler in H.
  repeat (break_match ; subst ; simpl in * ; inversion H).
  split ; auto.
Qed.

Lemma only_child_in_ass_list: forall net c a,
  net_reachable net ->
  In a (assign_list (nwState net c)) -> 
  exists d : Name, In d (c :: (children c)) /\ In a (assign_list (nwState net d)).
Proof.
  intros.
  exists c.
  split.
  simpl ; auto.
  auto.
Qed.

Lemma packet_source_terminated : forall x,
  net_reachable x -> forall p,
  In p (nwPackets x) -> let (pSrc, pDst, pBody) := p in
  c_finished x pSrc.
Proof.
  unfold net_reachable. unfold c_finished. intros x H. destruct H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind ; intros ; subst ; simpl in *.
  + inversion H.
  + destruct p.
    intuition. specialize (H3 {| pSrc := pSrc; pDst := pDst; pBody := pBody |}).
    invc H0 ; simpl in *.
    - unfold NetHandler in H5.
      rewrite H4 in *.
      repeat (break_match ; simpl in * ; subst ; simpl in * ; intuition) ; inversion H5 ; subst ; simpl in * ; intuition.
        assert (In {| pSrc := Net.pDst p; pDst := pDst; pBody := pBody |} (xs ++ p :: ys)).
        apply in_app_or in H2. destruct H2.
        apply in_or_app. left. auto.
        apply in_or_app. right. simpl. auto.
        apply H3 in H0. inversion H0.
        assert (In {| pSrc := Net.pDst p; pDst := pDst; pBody := pBody |} (xs ++ p :: ys)).
        apply in_app_or in H2. destruct H2.
        apply in_or_app. left. auto.
        apply in_or_app. right. simpl. auto.
        apply H3 in H0. inversion H0.
        assert (In {| pSrc := Net.pDst p; pDst := pDst; pBody := pBody |} (xs ++ p :: ys)).
        apply in_app_or in H2. destruct H2.
        apply in_or_app. left. auto.
        apply in_or_app. right. simpl. auto.
        apply H3 in H0. inversion H0.
        assert (In {| pSrc := pSrc; pDst := pDst; pBody := pBody |} (xs ++ p :: ys)).
        apply in_app_or in H2. destruct H2.
        apply in_or_app. left. auto.
        apply in_or_app. right. simpl. auto.
        apply H3 in H0. auto.
        inversion H0. subst. intuition.
        assert (In {| pSrc := pSrc; pDst := pDst; pBody := pBody |} (xs ++ p :: ys)).
        apply in_app_or in H0. destruct H0.
        apply in_or_app. left. auto.
        apply in_or_app. right. simpl. auto.
        apply H3 in H2. auto.
        assert (In {| pSrc := pSrc; pDst := pDst; pBody := pBody |} (xs ++ p :: ys)).
        apply in_app_or in H2. destruct H2.
        apply in_or_app. left. auto.
        apply in_or_app. right. simpl. auto.
        apply H3 in H0. auto.
        assert (In {| pSrc := pSrc; pDst := pDst; pBody := pBody |} (xs ++ p :: ys)).
        apply in_app_or in H2. destruct H2.
        apply in_or_app. left. auto.
        apply in_or_app. right. simpl. auto.
        apply H3 in H0. auto.
        assert (In {| pSrc := pSrc; pDst := pDst; pBody := pBody |} (xs ++ p :: ys)).
        apply in_app_or in H2. destruct H2.
        apply in_or_app. left. auto.
        apply in_or_app. right. simpl. auto.
        apply H3 in H0. auto.
    - unfold InputHandler in H4.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H4 ; subst ; simpl in * ; intuition.
      rewrite Heql0 in H0. inversion H0.
      inversion H0. subst. intuition.
Qed.

Lemma packet_source_terminated' : forall x,
  net_reachable x -> forall (pSrc pDst : Name) pBody,
  In {| pSrc := pSrc; pDst := pDst; pBody := pBody |} (nwPackets x) -> 
  c_finished x pSrc.
Proof.
  intros.
  assert (forall x,
  net_reachable x -> forall p,
  In p (nwPackets x) -> let (pSrc, pDst, pBody) := p in
  c_finished x pSrc).
  apply (packet_source_terminated).
  specialize (H1 x H).
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

Lemma net_reachable_app : forall net net2,
  net_reachable net -> net_reachable_from net net2 ->
  net_reachable net2.
Proof.
  intros net net2 reach1 reach2.
  unfold net_reachable in *.
  unfold net_reachable_from in reach2.
  destruct reach1. destruct reach2.
  exists (x ++ x0).
  apply (refl_trans_1n_trace_trans H H0).
Qed.

Lemma p_dst_eq_psrc : forall x,
  net_reachable x -> forall p,
  In p (nwPackets x) -> let (pSrc, pDst, pBody) := p in
  pDst = parent pSrc.
Proof.
  unfold net_reachable.
  intros x H. destruct H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind ; intros ; subst ; simpl in *.
  + inversion H.
  + assert (H2' := H2).
    apply (packet_source_terminated x'') in H2' ; auto.
    unfold c_finished in *.
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
      destruct p. simpl in *. subst.
      unfold NetHandler in H4.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H4 ; subst ; simpl in * ; intuition ; clear H4.
      apply (silly_lemma2 pSrc0 (parent pSrc0) pBody0) in H2. intuition.
      inversion H0. auto.
      apply H0'. apply (silly_lemma2 pSrc0 (parent pSrc0) pBody0). intuition.
      apply H0'. apply (silly_lemma2 pSrc0 (parent pSrc0) pBody0). intuition.
      apply H0'. apply (silly_lemma2 pSrc0 (parent pSrc0) pBody0). intuition.
      inversion H0. auto.
      apply H0'. apply (silly_lemma2 pSrc0 (parent pSrc0) pBody0). intuition.
      apply H0'. apply (silly_lemma2 pSrc0 (parent pSrc0) pBody0). intuition.
    - intuition.
      unfold InputHandler in H3.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H3 ; subst ; simpl in * ; intuition.
      inversion H4. auto.
      specialize (H0 {| pSrc := h; pDst := pDst; pBody := pBody |}). intuition.
      inversion H4. auto.
      specialize (H0 {| pSrc := pSrc; pDst := pDst; pBody := pBody |}). intuition.
      specialize (H0 {| pSrc := h; pDst := pDst; pBody := pBody |}). intuition.
      specialize (H0 {| pSrc := pSrc; pDst := pDst; pBody := pBody |}). intuition.
    - apply (net_reachable_app x' x'') ; auto.
      unfold net_reachable. exists tr1. auto.
      unfold net_reachable_from. exists tr2.
      assert (tr2 = [] ++ tr2). simpl. auto.
      rewrite H3. assert (refl_trans_1n_trace step_async x' x' []).
      apply RT1nTBase. apply (RT1n_step x'' tr2 H4 H0).
Qed.

Lemma packets_dst_eq_src : forall x,
  net_reachable x -> forall (pSrc pDst: Name) (pBody : Msg),
  In {| pSrc := pSrc; pDst := pDst; pBody := pBody |} (nwPackets x) -> 
  pDst = parent pSrc.
Proof.
  intros.
  assert (forall x,
  net_reachable x -> forall p,
  In p (nwPackets x) -> let (pSrc, pDst, pBody) := p in
  pDst = parent pSrc).
  apply p_dst_eq_psrc.
  specialize (H1 x H {| pSrc := pSrc; pDst := pDst; pBody := pBody |} H0).
  simpl in *.
  auto.
Qed.

Lemma terminated_child_todo_null_null: forall net,
  net_reachable net -> (forall c,
  children (Checker c) = [] -> 
  child_todo (nwState net (Checker c)) = []).
Proof.
  unfold net_reachable.
  intros net H. destruct H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind ; intros ; simpl in *.
  + subst.
    simpl in *.
    auto.
  + subst. simpl in *.
    intuition.
    invc H0 ; simpl in *.
    - unfold NetHandler in H5.
      repeat (break_match ; simpl in * ; subst ; simpl in * ; intuition) ; inversion H5 ; subst ; simpl in * ; intuition.
      rewrite <- e in * ; auto. apply H3 in H2. subst.
      rewrite H2 in Heql0.
      inversion Heql0.
      rewrite <- e in * ; auto. apply H3 in H2. subst.
      rewrite H2 in Heql0.
      inversion Heql0.
      rewrite <- e in * ; auto. apply H3 in H2. subst.
      rewrite H2 in Heql0.
      inversion Heql0.
    - unfold InputHandler in H4.
      repeat break_match ; simpl in * ; subst ; simpl in * ; intuition ; inversion H4 ; subst ; simpl in * ; intuition.
Qed.

Lemma terminated_child_todo_null: forall net,
  net_reachable net -> (forall c,
  c_finished net c ->
  child_todo (nwState net c) = []).
Proof.
  intros net H.
  unfold c_finished. auto.
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


















End Consistency_Checker.