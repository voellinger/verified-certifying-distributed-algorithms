
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


Record Data := mkData{
  checkerknowledge: Checkerknowledge; 
  checkerinput : Checkerinput;
  var_list : Certificate;
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


(* Sendet zu Beginn hoch, falls *me* ein Blatt ist *)
Definition InputHandler (me : Name) (c : Input) (state: Data) :
            (list Output) * Data * list (Name * Msg) :=
  if (eqb (terminated state) true) then
  ([] , (mkData
            (checkerknowledge state)
            (checkerinput state)
            (var_list state)
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
            (var_list state)
            (true)
            (true)
            (child_list state)),
      [(parent me, (var_list state))])
  | _ =>
    ([] , (mkData
            (checkerknowledge state)
            (checkerinput state)
            (var_list state)
            (terminated state)
            (consistent state)
            (child_list state)),
      [])
  end.



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

Fixpoint check_var_list (vl : list Assignment) : bool :=
  match vl with
  | nil => true
  | hd :: tl => (is_always hd tl) && check_var_list tl
  end.

Definition is_consistent (cert : Certificate) : Prop :=
  forall (assign1 assign2 : Assignment), 
    let (var1, val1) := assign1 in
      let (var2, val2) := assign2 in
        In assign1 cert -> In assign2 cert ->
          var1 = var2 -> val1 = val2.

Lemma check_var_list_works : forall (cert : Certificate),
  (check_var_list cert) = true <-> is_consistent cert.
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
    - unfold check_var_list in H.
      unfold is_always in H.
      admit.
    - assert (check_var_list cert = true).
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
      induction cert.
        simpl. destruct a0. reflexivity.
        simpl in *.
        destruct a0. destruct a1.
        destruct (var_beq v0 v2).
        unfold is_consistent in H.
        specialize (H (assign_cons v0 v1)).
        
          
      unfold is_always.
      unfold is_consistent in H.
      simpl in *.
      admit.
      rewrite H1.
      auto.
      
      

Definition NetHandler (me : Name) (src: Name) (child_cert : Msg) (state: Data) :
    (list Output) * Data * list (Name * Msg) :=
  if (eqb (terminated state) true) then
  ([] , (mkData
            (checkerknowledge state)
            (checkerinput state)
            (var_list state)
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
            (var_list state)
            (terminated state)
            (consistent state)
            (child_list state)),
      [])
  | [c] =>
    ([check_var_list ((var_list state) ++ child_cert)] , (mkData
            (checkerknowledge state)
            (checkerinput state)
            ((var_list state) ++ child_cert)
            (true)
            (check_var_list ((var_list state) ++ child_cert))
            ([])),
      [(parent me, (var_list state))])
  | _ =>
    ([] , (mkData
            (checkerknowledge state)
            (checkerinput state)
            ((var_list state) ++ child_cert)
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

Definition descendand (d : Name) : Set :=
  {vl : V_list & {el : E_list & {w : Walk v a (name_component d) (name_component root) vl el & parent_walk (name_component d) (name_component root) vl el w}}}.

Definition root_subtree_consistent :=
  forall a d1 d2, descendand d1 -> descendand d2 -> isa_aVarComponent a d1 -> isa_aVarComponent a d2 -> valueOf a d1 = valueOf a d2.

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
  descendand root.
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

Lemma Drei_zwei : forall net tr c,
  (nwState net (Checker c)).(terminated) = true ->
  (nwState net (Checker c)).(consistent) = true ->
  step_async_star (params := Checker_MultiParams) step_async_init net tr ->
  is_consistent (nwState net (Checker c)).(var_list).



1. wenn Zustand terminated erreicht (true), dann bleibt er immer true (vllt NetHandler anpassen daf\u00fcr, indem am Anfang abgefragt wird, ob schon terminated)
2. wenn terminated, dann \u00e4ndert sich consistent nicht mehr            (vllt NetHandler anpassen daf\u00fcr, indem am Anfang abgefragt wird, ob schon terminated)
3. wenn terminated, dann 
  i. sind alle Belegungen der Variablen des Teilbaums in der var_list
  ii. wenn consistent, dann sind alle Variablen der var_list sind gleichbelegt
  -> der gesamte Teilbaum hat eine konsistente Belegung
  iii. wenn nicht consistent, dann existiert eine Variable in der var_list, die zwei verschiedene Belegungen hat
  -> es existieren zwei Komponenten im Teilbaum, die f\u00fcr eine Variable verschiedene Belegungen haben
5. wenn alle Variablen im Teilbaum gleichbelegt sind, dann ist der Zeuge konsistent
6. wenn nicht alle Variablen im Teilbaum gleichbelegt sind, dann ist der Zeuge nicht konsistent


M\u00f6gliche Verbesserungen:
  1. bei Doppelbelegungen nur "false" nach oben reichen
  2. ansonsten nur eine Belegung je Variable nach oben reichen
  3. die erste if-abfrage im Nethandler streichen
  4. root braucht an niemanden senden, dann kann auch das erste Pattern weg
  5. entweder einen terminated state und consistent state, oder nur outputs

End ConnectedChecker.