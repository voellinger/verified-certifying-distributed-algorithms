
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


Section ConnectedChecker.


(* All components are already indexed by natural numbers via GraphBasics. *)
Definition Component_Index := nat.
(* A distance for how long a message has traveled to the recipient. *)
Definition Distance := nat.


(* This is the content of a message. It consists of:
  - var 
  - local leader for the var
  - distance from where it was sent (the temporary local leader)
  - last sender (parent), so that the receiving node can make a parent towards the temporary local leader
*)
Inductive Msg := leader : (Var * Component_Index * Distance * Name) -> Msg.

Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
Proof.
Admitted.
(* Proof.
  intros x y.
  decide equality.
  destruct p.
  destruct p0.
  assert (H1: {n = n0} + {n <> n0}).
  apply Nat.eq_dec.
  destruct H1.
  rewrite e.
  assert (H2: {v0 = v1} + {v0 <> v1}).
  (* This worked because Var was nat before *)
  unfold Nat in *.
  apply Nat.eq_dec.
  destruct H2.
  left.
  rewrite e0.
  reflexivity.
  right.
  intuition.
  inversion H.
  intuition.
  right.
  intuition.
  inversion H.
  intuition.
Qed.
 *)
Record Data := mkData{
  checkerknowledge: Checkerknowledge; 
  checkerinput : Checkerinput;
  leaders : list Msg
}.

(* all components first are their own leader for all fact_vars *)
Fixpoint init_leader_list (n:Name) (c: Certificate) :=
  match c with
  | [] => []
  | hd :: tl => (leader (assignment_var hd, component_index (name_component n), 0, n)) :: init_leader_list n tl
  end.

(* initialization of the network *)
Definition init_Data (me: Name) := 
  mkData (init_Checkerknowledge me) (init_Checkerinput me) (init_leader_list me (certificate (init_Checkerinput me))).


Definition set_leaders (d : Data) (new_leaders : list Msg) := mkData (checkerknowledge d) (checkerinput d) new_leaders.

Fixpoint sendlist (neighbors: list Component) (new_l: Msg): list (Name * Msg) :=
  match neighbors with 
    | nil => []
    | hd :: tl => (Checker hd, new_l) :: (sendlist tl new_l)
  end.

(* The component sends itself as the leader for all its fact_vars to all its neighbours *)
Fixpoint initial_send_list (me : Name) (var_l : list Var) neighbours: list (Name * Msg) :=
  match var_l with
    | [] => []
    | hd :: tl => sendlist neighbours (leader (hd, component_index (name_component me), 0, me)) ++ initial_send_list me tl neighbours
  end.

(* This input starts a checker *)
Inductive Input := alg_terminated : Input.

(* kann weggelassen werden? *)
Definition Output := Msg.


(* Sendet zu Beginn die Initial-Liste an alle Nachbarn *)
Definition InputHandler (me : Name) (c : Input) (state: Data) :
            (list Output) * Data * list (Name * Msg) := 
	match me  with
    | Checker x => let myneighbours := (neighbors v a g x) in
      ([] , (mkData (checkerknowledge state) (checkerinput state) (leaders state)), initial_send_list me (var_l (checkerknowledge state)) myneighbours)
    end.

Fixpoint find_leader (k : Var) (leaders : list Msg) : option nat :=
  match leaders with
  | [] => None
  | leader (var, ind, dis, par) :: tl => if var_beq k var
                            then Some ind
                            else find_leader k tl
  end.

Definition get_leader_index k (leaders: list Msg) : nat :=
  match (find_leader k leaders) with
  | Some x => x
  | None => 0
  end.

Fixpoint set_leader var n d p (ls: list Msg) : list Msg :=
  match ls with
  | [] => [leader (var, n, d, p)]
  | leader (k, ind, dis, par) :: tl => if var_beq k var
                                 then leader (k, n, dis, par) :: tl
                                 else set_leader var n d p tl
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


Lemma set_leader_sets_leader: forall var n (ls: list Msg) d p,
    n = get_leader_index var (set_leader var n d p ls).
Proof.
  intros var n ls d p.
  induction ls.
    simpl.
    unfold get_leader_index.
    simpl.
    rewrite var_eq_refl.
    reflexivity.

    destruct a0.
    destruct p0.
    destruct p0.
    destruct p0.
    assert (v0 = var \/ v0 <> var).
    apply classic.
    destruct H.

    rewrite H.
    simpl.
    rewrite var_eq_refl.
    unfold get_leader_index.
    simpl.
    rewrite var_eq_refl.
    reflexivity.

    assert (var_beq v0 var = false).
    unfold var_beq.
    destruct var_eq_dec.
    intuition.
    reflexivity.
    simpl.
    rewrite H0.
    apply IHls.
Qed.


Fixpoint varList_has_varb (vl : list Var) (v : Var) : bool :=
  match vl with
  | nil => false
  | hd :: tl => var_beq hd v && varList_has_varb tl v
  end.

Definition varList_has_var (vl : list Var) (v : Var) : Prop :=
  varList_has_varb vl v = true.

Definition NetHandler (me : Name) (src: Name) (le : Msg) (state: Data) : 
    (list Output) * Data * list (Name * Msg) :=
    match le with
      | leader (var, n, d, p)  => if (varList_has_varb (var_l (checkerknowledge state)) var) && Nat.ltb (get_leader_index var (leaders state)) n
        then ([], set_leaders state (set_leader var n d p (leaders state)), sendlist (neighbor_l (checkerknowledge state)) (leader (var, n, d+1, me)))
          else ([], state, [])
    end.

Definition isa_aVarComponent (aVar : Var) (c : Component) : Prop :=
  varList_has_var (init_var_l (component_name c)) aVar.

Inductive aVarTree : Var -> V_set -> A_set -> V_set -> A_set -> Set :=
  | CC_isolated : forall (aVar : Var) (v : V_set)(a : A_set) (x : Component), isa_aVarComponent aVar x -> v x -> aVarTree aVar v a (V_single x) A_empty
  | CC_leaf: forall (aVar : Var) (v : V_set) (a : A_set) (vT : V_set) (aT : A_set) x y,
      vT x -> ~ vT y -> v y -> a (A_ends x y) -> isa_aVarComponent aVar y -> aVarTree aVar v a vT aT -> aVarTree aVar v a (V_union (V_single y) vT) (A_union (E_set x y) aT)
  | CC_eq: forall aVar (v : V_set) (a : A_set) vT vT' aT aT',
    vT = vT' -> aT = aT' -> aVarTree aVar v a vT aT -> aVarTree aVar v a vT' aT'.

Lemma aVarTree_is_Connected : forall (aVar : Var) (v : V_set) (a : A_set) (vT: V_set) (aT: A_set),
  aVarTree aVar v a vT aT -> Connected vT aT.
Proof.
  intros aVar v a vT aT cc.
  induction cc.
  + apply C_isolated.
  + apply C_leaf.
    apply IHcc.
    apply v1.
    apply n.
  + rewrite <- e in *.
    rewrite <- e0 in *.
    apply IHcc.
Qed.

Definition max_aVarVset (aVar : Var) (a : A_set) (vT : V_set) : Prop :=
  (forall c1 c2 : Component, (vT c1 /\ a (A_ends c1 c2) /\ isa_aVarComponent aVar c2) -> vT c2).

Lemma only_aVars_inaVarTree: forall (aVar : Var) (v : V_set) (a : A_set) (vT : V_set) (aT : A_set) (cc : aVarTree aVar v a vT aT) (x : Component),
  vT x -> isa_aVarComponent aVar x.
Proof.
  intros aVar v c vT aT cc x vTx.
  induction cc.
  + inversion vTx.
    rewrite H in *.
    apply i.
  + inversion vTx.
    inversion H.
    rewrite <- H1 ; auto.
    apply (IHcc H).
  + rewrite <- e in vTx.
    apply (IHcc vTx).
Qed.

Lemma only_vs_inaVarTree: forall (aVar : Var) (v : V_set) (a : A_set) (vT : V_set) (aT : A_set) (cc : aVarTree aVar v a vT aT) (x : Component),
  vT x -> v x.
Proof.
  intros aVar v c vT aT cc x H.
  induction cc.
  + inversion H.
    rewrite <- H0.
    apply v1.
  + inversion H.
    inversion H0.
    rewrite <- H2.
    apply v2.
    apply IHcc.
    apply H0.
  + rewrite <- e in *.
    apply (IHcc H).
Qed.

Lemma only_as_inaVarTree: forall (aVar : Var) (v : V_set) (a : A_set) (c0 : Connected v a) (vT : V_set) (aT : A_set) (cc : aVarTree aVar v a vT aT) (x : Arc),
  aT x -> a x.
Proof.
  intros aVar v a c0 vT aT cc x H.
  induction cc.
  + inversion H.
  + inversion H.
    inversion H0.
    apply a1.
    assert (Graph v0 a0).
    apply (Connected_Isa_Graph v0 a0 c0).
    apply (G_non_directed v0 a0 H3 x0 y a1).
    apply IHcc.
    apply c0.
    apply H0.
  + rewrite <- e0 in *.
    apply (IHcc c0 H).
Qed.

Lemma Walk_in_bigger_conn : forall (v vB : V_set) (a aB : A_set) (v1 v2 : Component) (vl : V_list) (el : E_list),
  V_included v vB -> A_included a aB -> Walk v a v1 v2 vl el -> Walk vB aB v1 v2 vl el.
Proof.
  intros v vB a aB v1 v2 vl el vI aI w.
  induction w.
  + apply W_null.
    unfold V_included in vI.
    unfold Included in vI.
    apply (vI x v0).
  + apply W_step.
    apply IHw.
    unfold V_included in vI.
    unfold Included in vI.
    apply (vI x v0).
    unfold A_included in aI.
    unfold Included in aI.
    apply (aI (A_ends x y) a0).
Qed.

Definition aVarWalk (aVar : Var) (v : V_set) (a : A_set) (c1 c2 : Component) (vl : V_list) (el : E_list) (w : Walk v a c1 c2 vl el) :=
  forall (c : Component), In c (c1 :: vl) -> isa_aVarComponent aVar c.

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

Lemma aVarTrees_are_aVarWalks: forall (aVar : Var) (v : V_set) (a : A_set) (c0 : Connected v a) (vT : V_set) (aT : A_set) (cc : aVarTree aVar v a vT aT),
 (forall (v1 v2 : Component), vT v1 -> vT v2 -> {vl : V_list & {el : E_list & {w : Walk v a v1 v2 vl el & aVarWalk aVar v a v1 v2 vl el w}}}).
Proof.
  intros aVar v a c0 vT aT cc v1 v2 vTv1 vTv2.
  assert (cc' := cc).
  apply aVarTree_is_Connected in cc.
  apply (Connected_path) with (x := v1) (y := v2) in cc.
  destruct cc.
  destruct s.
  exists x.
  exists x0.
  apply Path_isa_trail in p.
  apply Trail_isa_walk in p.
  assert (p' := p).
  apply (Walk_in_bigger_conn vT v aT a v1 v2 x x0) in p.
  exists p.
  unfold aVarWalk.
  intros.
  inversion H.
  rewrite <- H0.
  apply W_endx_inv in p'.
  apply (only_aVars_inaVarTree aVar v a vT aT cc' v1 p').
  assert (vT c).
  apply (W_invl_inv vT aT v1 v2 x x0 p' c H0).
  apply (only_aVars_inaVarTree aVar v a vT aT cc' c H1).
  unfold V_included. unfold Included.
  intros.
  apply (only_vs_inaVarTree aVar v a vT aT cc') in H.
  apply H.
  unfold A_included. unfold Included.
  intros.
  apply (only_as_inaVarTree aVar v a c0 vT aT cc') in H.
  apply H.
  apply vTv1.
  apply vTv2.
Qed.

Lemma aVarWalk_in_aVarTree: forall (aVar : Var) (v : V_set) (a : A_set) (vT : V_set) (aT : A_set) (cc : aVarTree aVar v a vT aT) 
                       (v1 v2: Component) (vl : V_list) (el : E_list) (w : Walk v a v1 v2 vl el),
  max_aVarVset aVar a vT -> vT v1 -> aVarWalk aVar v a v1 v2 vl el w -> vT v2.
Proof.
  intros aVar v a vT aT cc v1 v2 vl el w CC vTv1 aWalk.
  induction w ; unfold max_aVarVset in CC.
  + apply vTv1.
  + apply IHw.
    unfold aVarWalk in aWalk.
    specialize (aWalk y).
    simpl in aWalk.
    intuition.
    apply (CC x y).
    auto.
    unfold aVarWalk in *.
    intros.
    apply aWalk.
    inversion H.
    simpl.
    right. left. auto.
    simpl. right. right. auto.
Qed.

(* wenn sich zwei CCs in c \u00fcberschneiden, so sind \u00fcber c aVar-Walks m\u00f6glich und daher CC1 = CC2 *)
Lemma two_aVarTrees_same_v: forall (aVar : Var) (v : V_set) (a : A_set) (c0 : Connected v a) (v1 v2: V_set) (a1 a2: A_set) (c1 : aVarTree aVar v a v1 a1) (c2: aVarTree aVar v a v2 a2),
  max_aVarVset aVar a v1 -> max_aVarVset aVar a v2 -> {c : Component & (v1 c /\ v2 c)} -> 
    (forall x : Component, v1 x -> v2 x).
Proof.
  intros aVar v a c0 v1 v2 a1 a2 c1 c2 acc1 acc2 same.
  destruct same.
  destruct a0. intros.
  apply (aVarTrees_are_aVarWalks aVar v a c0 v1 a1 c1 x x0) in H1.
  destruct H1.
  destruct s.
  destruct s.
  apply (aVarWalk_in_aVarTree aVar v a v2 a2 c2 x x0 x1 x2 x3 acc2 H0 a0).
  apply H.
Qed.

Lemma aVarTree_a_means_v: forall (aVar : Var) (v : V_set) (a : A_set) (vT : V_set) (aT : A_set) (cc : aVarTree aVar v a vT aT) 
                       (v1 v2: Component),
  aT (A_ends v1 v2) -> (vT v1 /\ vT v2).
Proof.
  intros aVar v a vT aT cc v1 v2 acca.
  induction cc.
  + inversion acca.
  + inversion acca.
    - inversion H.
      rewrite <- H2 in *.
      rewrite <- H3 in *.
      split.
      apply In_right. apply v3.
      apply In_left.
      apply In_single.
      split.
      apply In_left ; apply In_single.
      rewrite <- H2 in *.
      rewrite <- H3 in *.
      apply In_right. apply v3.
    - apply IHcc in H.
      destruct H.
      split ; apply In_right.
      apply H.
      apply H1.
  + rewrite <- e in *.
    rewrite <- e0 in *.
    apply (IHcc acca).
Qed.

Lemma aVarTree_a_means_a: forall (aVar : Var) (v : V_set) (a : A_set) (c0 : Connected v a) (vT : V_set) (aT : A_set) (cc : aVarTree aVar v a vT aT) 
                       (ar: Arc),
  aT ar -> a ar.
Proof.
  intros aVar v a c0 vT aT cc ar acca.
  induction cc.
  + inversion acca.
  + inversion acca.
    inversion H.
    apply a1.
    assert (Graph v0 a0).
    apply (Connected_Isa_Graph v0 a0 c0).
    apply (G_non_directed v0 a0 H2 x y a1).
    apply (IHcc c0 H).
  + rewrite <- e0 in *.
    apply (IHcc c0 acca).
Qed.

Lemma two_aVarTrees_same: forall (aVar : Var) (v : V_set) (a : A_set) (c0 : Connected v a) (v1 v2: V_set) (a1 a2: A_set) (c1 : aVarTree aVar v a v1 a1) (c2: aVarTree aVar v a v2 a2),
  max_aVarVset aVar a v1 -> max_aVarVset aVar a v2 -> {c : Component & (v1 c /\ v2 c)} -> 
    (v1 = v2).
Proof.
  intros aVar v a c0 v1 v2 a1 a2 c1 c2 acc1 acc2 same.
  + assert (forall x : Component, v1 x -> v2 x).
    intros.
    apply (two_aVarTrees_same_v aVar v a c0 v1 v2 a1 a2 c1 c2 acc1 acc2 same x) in H.
    apply H.
    assert ({c : Component & v2 c /\ v1 c}).
    destruct same.
    destruct a0.
    exists x. auto.
    assert (forall x : Component, v2 x -> v1 x).
    intros.
    apply (two_aVarTrees_same_v aVar v a c0 v2 v1 a2 a1 c2 c1 acc2 acc1 H0 x) in H1.
    apply H1.
    apply U_set_eq.
    split.
    apply H.
    apply H1.
Qed.

Lemma two_aVarTrees_same': forall (aVar : Var) (v : V_set) (a : A_set) (c0 : Connected v a) (v1 v2: V_set) (a1 a2: A_set) (c1 : aVarTree aVar v a v1 a1) (c2: aVarTree aVar v a v2 a2),
  max_aVarVset aVar a v1 -> max_aVarVset aVar a v2 -> {ar : Arc & (a1 ar /\ a2 ar)} -> 
    (v1 = v2).
Proof.
  intros aVar v a c0 v1 v2 a1 a2 c1 c2 acc1 acc2 same.
  destruct same.
  destruct a0.
  assert (forall v1 v2 v0 a0 aVar (c1 : aVarTree aVar v a v0 a0), a0 (A_ends v1 v2) -> (v0 v1 /\ v0 v2)).
  - intros.
    induction c3.
    + inversion H1.
    + inversion H1.
      inversion H2.
      rewrite <- H5 in *.
      rewrite <- H6 in *.
      split.
      apply In_right.
      apply v5.
      apply In_left.
      apply In_single.
      split.
      apply In_left.
      apply In_single.
      rewrite <- H5 in *.
      rewrite <- H6 in *.
      apply In_right.
      apply v5.
      apply (aVarTree_a_means_v aVar0 v4 a0 vT aT c3) in H2.
      destruct H2.
      split.
      apply In_right.
      apply H2.
      apply In_right.
      apply H4.
    + rewrite <- e in *.
      rewrite <- e0 in *.
      apply (IHc3 c0) ; auto.
  - destruct x.
    specialize (H1 v0 v3).
    assert (v1 v0 /\ v1 v3).
    apply (H1 v1 a1 aVar c1 H).
    assert (v2 v0 /\ v2 v3).
    apply (H1 v2 a2 aVar c2 H0).
    destruct H2.
    destruct H3.
    apply (two_aVarTrees_same aVar v a c0 _ _ _ _ c1 c2 acc1 acc2).
    exists v0.
    auto.
Qed.

Definition root_of_Vset (vT : V_set) (root: Component) : Prop :=
  (vT root /\ forall (c : Component), vT c -> component_index c <= component_index root).

Lemma root_same_aVarTrees_same : forall (aVar : Var) (v : V_set) (a : A_set) (c0 : Connected v a) (vT1 vT2 : V_set) (aT1 aT2 : A_set),
  aVarTree aVar v a vT1 aT1 -> aVarTree aVar v a vT2 aT2 -> max_aVarVset aVar a vT1 -> max_aVarVset aVar a vT2 ->
  {c : Component & (root_of_Vset vT1 c /\ root_of_Vset vT2 c)} -> vT1 = vT2.
Proof.
  intros aVar v a c0 vT1 vT2 aT1 aT2 aTree1 aTree2 maTree1 maTree2 H.
  destruct H.
  destruct a0 as [rmaTree1 rmaTree2].
  unfold root_of_Vset in *.
  destruct rmaTree1. destruct rmaTree2.
  apply (two_aVarTrees_same aVar v a c0 vT1 vT2 aT1 aT2 aTree1 aTree2 maTree1 maTree2).
  exists x.
  auto.
Qed.

Lemma components_comparable : forall (c1 c2 : Component),
  {component_index c1 <= component_index c2} +
  {component_index c1 > component_index c2}.
Proof.
  intros c1.
  destruct c1.
  induction n.
  + left.
    destruct c2.
    simpl.
    induction n.
    reflexivity.
    auto.
  + intros c2.
    specialize (IHn c2).
    destruct c2.
    simpl in *.
    destruct IHn.
    assert ({n = n0} + {n <> n0}).
    apply Nat.eq_dec.
    destruct H.
    right.
    intuition.
    left.
    intuition.
    right.
    intuition.
Qed.

Lemma aVarTree_root_exists : forall (aVar : Var) (v : V_set) (a : A_set) (vT : V_set) (aT : A_set) (aTree : aVarTree aVar v a vT aT),
  {c : Component & root_of_Vset vT c}.
Proof.
  intros aVar v a vT aT aTree.
  induction aTree.
  + exists x.
    unfold root_of_Vset.
    auto.
    split.
    apply In_single.
    intros.
    inversion H. auto.
  + destruct IHaTree.
    assert ({component_index x0 <= component_index  y} +
            {component_index x0 > component_index y}).
    apply components_comparable.
    destruct H.
    exists y.
    unfold root_of_Vset.
    split.
    apply In_left. apply In_single.
    intros.
    unfold root_of_Vset in r.
    destruct r.
    inversion H.
    inversion H2. auto.
    apply H1 in H2.
    intuition.
    exists x0.
    unfold root_of_Vset in *.
    destruct r.
    split.
    apply In_right.
    apply H.
    intros.
    inversion H1.
    inversion H2.
    rewrite <- H4 in *.
    intuition.
    apply H0.
    apply H2.
  + rewrite <- e in *.
    apply IHaTree.
Qed.

Lemma aVarTrees_same_root_same : forall (aVar : Var) (v : V_set) (a : A_set) (vT1 vT2 : V_set) (aT1 aT2 : A_set),
  aVarTree aVar v a vT1 aT1 -> aVarTree aVar v a vT2 aT2 -> max_aVarVset aVar a vT1 -> max_aVarVset aVar a vT2 ->
  vT1 = vT2 -> {c : Component & (root_of_Vset vT1 c /\ root_of_Vset vT2 c)}.
Proof.
  intros aVar v a vT1 vT2 aT1 aT2 aTree1 aTree2 maTree1 maTree2 vT1vT2.
  apply aVarTree_root_exists in aTree1.
  apply aVarTree_root_exists in aTree2.
  destruct aTree1. destruct aTree2.
  unfold root_of_Vset in *.
  destruct r. destruct r0.
  exists x.
  split.
  auto.
  split ; rewrite <- vT1vT2 in *.
  apply H.
  apply H0.
Qed.

Definition is_aVarspanning (aVar : Var) (v : V_set) (vT : V_set) : Prop := 
  forall c, (v c /\ isa_aVarComponent aVar c) -> vT c.

Definition all_maxaVarTreesSame (aVar : Var) (v : V_set) (a : A_set) : Prop :=
(forall vT1 vT2 aT1 aT2 (aTree1 : aVarTree aVar v a vT1 aT1) (aTree2 : aVarTree aVar v a vT2 aT2),
    (max_aVarVset aVar a vT1 /\ max_aVarVset aVar a vT2) ->
    vT1 = vT2).

Lemma aVarTree_no_notaVars : forall (aVar : Var) (v : V_set) (a : A_set) (vT : V_set) (aT : A_set) 
  (aTree : aVarTree aVar v a vT aT) (c : Component),
  ~ isa_aVarComponent aVar c -> ~ vT c.
Proof.
  intros aVar v a vT aT atree c not.
  induction atree.
  + intuition.
    inversion H.
    rewrite <- H0 in not.
    intuition.
  + intuition.
    inversion H.
    inversion H1.
    rewrite <- H3 in *.
    intuition.
    intuition.
  + rewrite <- e.
    apply (IHatree not).
Qed.

Lemma aVarTree_remains : forall (aVar : Var) (v0 vT: V_set) (a0 aT: A_set) 
  (g : Connected v0 a0) (x y : Component) (aTree : aVarTree aVar v0 a0 vT aT),
  aVarTree aVar (V_union (V_single y) v0) (A_union (E_set x y) a0) vT aT.
Proof.
  intros aVar v0 vT a0 aT g x y aTree.
  induction aTree.
  + apply CC_isolated ; auto.
    apply In_right ; auto.
  + apply CC_leaf ; auto.
    apply In_right ; auto.
    apply In_right ; auto.
  + rewrite <- e0 in *.
    rewrite <- e in *.
    apply IHaTree ; auto.
Qed.

Lemma aVarTree_remains' : forall (aVar : Var) (v0 vT: V_set) (a0 aT: A_set) 
  (g : Connected v0 a0) (x y : Component) (aTree : aVarTree aVar v0 a0 vT aT),
  aVarTree aVar v0 (A_union (E_set x y) a0) vT aT.
Proof.
  intros aVar v0 vT a0 aT g x y aTree.
  induction aTree.
  + apply CC_isolated ; auto.
  + apply CC_leaf ; auto.
    apply In_right ; auto.
  + rewrite <- e0 in *.
    rewrite <- e in *.
    apply IHaTree ; auto.
Qed.

Lemma maxaVarTree_remains : forall (aVar : Var) (v0 vT: V_set) (a0 aT: A_set) 
  (g : Connected v0 a0) (x y : Component) (aTree : aVarTree aVar v0 a0 vT aT),
  ~(isa_aVarComponent aVar x /\ isa_aVarComponent aVar y) ->
  max_aVarVset aVar a0 vT -> max_aVarVset aVar (A_union (E_set x y) a0) vT.
Proof.
  intros aVar v0 vT a0 aT g x y aTree onenot matree.
  unfold max_aVarVset in *. intros.
  destruct H.
  destruct H0.
  assert (~ isa_aVarComponent aVar x \/ ~ isa_aVarComponent aVar y).
  assert (isa_aVarComponent aVar x \/ ~ isa_aVarComponent aVar x).
  apply classic.
  assert (isa_aVarComponent aVar y \/ ~isa_aVarComponent aVar y).
  apply classic.
  destruct H2.
  destruct H3.
  assert ((isa_aVarComponent aVar x /\ isa_aVarComponent aVar y)).
  auto.
  intuition.
  right ; auto.
  left ; auto.
  clear onenot.
  inversion H0.
  + inversion H3.
    rewrite <- H6 in *.
    rewrite <- H7 in *.
    clear H7 H6 H4 H3 x0 H0 c1 c2.
    destruct H2.
    apply (aVarTree_no_notaVars aVar v0 a0 vT aT aTree x) in H0.
    intuition.
    intuition.
    rewrite <- H6 in *.
    rewrite <- H7 in *.
    clear H7 H6 H4 H3 x0 H0 c1 c2.
    destruct H2.
    intuition.
    apply (aVarTree_no_notaVars aVar v0 a0 vT aT aTree y) in H0.
    intuition.
  + apply (matree c1 c2) ; auto.
Qed.

Lemma maxaVarTree_remains' : forall (aVar : Var) (v0 vT: V_set) (a0 aT: A_set) 
  (g : Connected v0 a0) (x y : Component) (aTree : aVarTree aVar v0 a0 vT aT),
  (vT x /\ vT y) ->
  max_aVarVset aVar a0 vT -> max_aVarVset aVar (A_union (E_set x y) a0) vT.
Proof.
  intros aVar v0 vT a0 aT g x y aTree both matree.
  unfold max_aVarVset in *.
  intros.
  destruct both as [vtx vty].
  destruct H.
  destruct H0.
  inversion H0.
  + inversion H2.
    rewrite <- H6 ; auto.
    rewrite <- H6 ; auto.
  + apply (matree c1 c2) ; auto.
Qed.

Lemma combine_aTrees'' : forall (aVar : Var) (vX v0: V_set) (aX a0: A_set)(c0 : Connected v0 a0)
    (x y : Component) (xTree : aVarTree aVar v0 a0 vX aX),
  vX x -> ~ v0 y ->
  max_aVarVset aVar a0 vX -> isa_aVarComponent aVar y ->
  aVarTree aVar (V_union (V_single y) v0) (A_union (E_set x y) a0) (V_union (V_single y) vX) (A_union (E_set x y) aX).
Proof.
  intros aVar vX v0 aX a0 c0 x y xTree vx nvy maxX isay.
  assert (aVarTree aVar (V_union (V_single y) v0) (A_union (E_set x y) a0) vX aX).
  apply (aVarTree_remains aVar v0 vX a0 aX c0 x y xTree).
  apply (CC_leaf) ; auto.
  - induction xTree.
    + intuition.
      inversion H0.
      rewrite H1 in *.
      intuition.
    + unfold not ; intros.
      inversion H0.
      inversion H1.
      rewrite H3 in *.
      apply (Connected_Isa_Graph) in c0.
      apply (G_ina_inv2 v0 a0) in a1 ; auto.
      apply (only_vs_inaVarTree aVar v0 a0 vT aT) in H1 ; auto.
    + rewrite <- e in *.
      rewrite <- e0 in *.
      apply IHxTree ; auto.
  - apply In_left.
    apply In_single.
  - apply In_left.
    apply E_right.
Qed.

Lemma combine_aTrees''' : forall (aVar : Var) (vX v0: V_set) (aX a0: A_set) (c0 : Connected v0 a0)
    (x y : Component) (xTree : aVarTree aVar v0 a0 vX aX),
  vX x -> ~ v0 y ->
  max_aVarVset aVar a0 vX -> isa_aVarComponent aVar y ->
  max_aVarVset aVar (A_union (E_set x y) a0) (V_union (V_single y) vX).
Proof.
  intros aVar vX v0 aX a0 c0 x y xTree vx nvy maxX isay.
  unfold max_aVarVset in * ; intros.
  destruct H.
  destruct H0.
  inversion H.
  + inversion H2.
    rewrite <- H4 in *.
    inversion H0.
    - inversion H5.
      rewrite H8 in *.
      apply (only_vs_inaVarTree aVar v0 a0 vX aX) in vx.
      intuition.
      apply xTree.
      rewrite <- H8 in *.
      apply In_right ; auto.
    - apply (Connected_Isa_Graph) in c0.
      apply (G_ina_inv1 v0 a0) in H5 ; auto.
      intuition.
  + inversion H0.
    - inversion H4.
      apply In_left. apply In_single.
      rewrite <- H7 in *.
      rewrite <- H8 in *.
      apply In_right ; auto.
    - apply In_right.
      apply (maxX c1 c2) ; auto.
Qed.

Lemma combine_aTrees' : forall (aVar : Var) (vX vY v0: V_set) (aX aY a0: A_set) (xTree : aVarTree aVar v0 a0 vX aX)
    (yTree : aVarTree aVar v0 a0 vY aY) (x y : Component) (c0 : Connected v0 a0),
  vX x -> vY y -> ~ vY x ->  ~ a0 (A_ends x y) -> 
  max_aVarVset aVar a0 vX -> max_aVarVset aVar a0 vY ->
  max_aVarVset aVar (A_union (E_set x y) a0) (V_union vX vY).
Proof.
  intros aVar vX vY v0 aX aY a0 xTree yTree x y c0 vx vy notvxy axy maxX maxY.
  unfold max_aVarVset in * ; intros.
  destruct H.
  destruct H0.
  inversion H.
  + rewrite <- H3 in *.
    inversion H0.
    - inversion H4.
        rewrite <- H7 in *.
        rewrite <- H8 in *.
        apply In_right ; auto.
        rewrite H8 in *.
        apply In_left ; auto.
    - apply In_left.
      apply (maxX x0 c2) ; auto.
  + rewrite <- H3 in *.
    inversion H0.
    - inversion H4.
      rewrite H8 in *.
      apply In_right ; auto.
      rewrite H8 in *.
      apply In_left ; auto.
    - apply In_right.
      apply (maxY x0 c2) ; auto.
Qed.

(* Definition aVarTree' (aVar : Var) (vT v : V_set) (aT a : A_set) :=
  (forall (c : Component), v c -> isa_aVarComponent aVar c) /\
  V_included vT v /\ A_included aT a /\
  forall (c1 c2 : Component), v c1 -> v c2 -> exists (vl : V_list) (el : E_list) (p : Path vT aT c1 c2 vl el), 1 = 1. *)

Lemma combine_aTrees : forall (aVar : Var) (vX v: V_set) (aX a : A_set) (x y : Component) (c0 : Connected v a),
  vX x ->  aVarTree aVar v a vX aX ->
  forall (vY : V_set) (aY : A_set), vY y -> (V_inter vX vY = V_empty) ->  ~ a (A_ends x y) ->
  aVarTree aVar v a vY aY ->
  aVarTree aVar v (A_union (E_set x y) a) (V_union vX vY) (A_union (E_set x y) (A_union aX aY)).
Proof.
  intros aVar vX v0 aX a0 x y c0 vx xTree.
  assert (xTree' := xTree).
  apply (aVarTree_remains' aVar v0 vX a0 aX c0 x y) in xTree' ; auto.
  induction xTree ; intros vY aY vy interempty axy yTree.
  + inversion vx.
    rewrite H in *.
    clear H ; clear x0.
    assert (yTree' := yTree).
    apply (aVarTree_remains' aVar v0 vY a0 aY c0 x y) in yTree' ; auto.
    assert ((A_union A_empty aY) = aY).
    rewrite A_union_neutral.
    reflexivity.
    rewrite H.
    assert ((A_union (E_set x y) aY) = (A_union (E_set y x) aY)).
    rewrite E_set_eq.
    auto.
    rewrite H0 ; clear H0.
    apply (CC_leaf aVar v0 (A_union (E_set x y) a0) vY aY y x) ; auto.
    unfold V_inter in interempty.
    unfold not ; intros.
    assert ((Inter Vertex (V_single x) vY) x).
    apply In_inter ; auto.
    rewrite interempty in H1.
    inversion H1.
    apply In_left ; apply E_left.
  + assert (aVarTree aVar v0 (A_union (E_set x y) a0) (V_union (V_single y0) (V_union vT vY))
  (A_union (E_set x0 y0) (A_union (E_set x y) (A_union aT aY)))).
    assert (yTree' := yTree).
    apply (aVarTree_remains' aVar v0 vY a0 aY c0 x y) in yTree' ; auto.
    - induction yTree.
      {
        inversion vy.
        rewrite H in *.
        clear H x1.
        assert (A_union aT A_empty = aT).
        admit.
        rewrite H ; clear H.
        assert ((V_union (V_single y0) (V_union vT (V_single y))) = (V_union (V_single y) (V_union (V_single y0) vT))).
        admit.
        rewrite H ; clear H.
        assert ((A_union (E_set x0 y0) (A_union (E_set x y) aT)) = (A_union (E_set x y) (A_union (E_set x0 y0) aT))).
        admit.
        rewrite H ; clear H.
        apply (CC_leaf aVar v0 (A_union (E_set x y) a0) (V_union (V_single y0) vT) (A_union (E_set x0 y0) aT) x y) ; auto.
        unfold not ; intros.
        inversion H.
        inversion H0.
        rewrite H2 in interempty.
        assert ((V_inter (V_union (V_single y) vT) (V_single y)) y).
        apply In_inter ; auto.
        apply In_left ; auto.
        rewrite interempty in H3 ; inversion H3.
        assert ((V_inter (V_union (V_single y0) vT) (V_single y)) y).
        apply In_inter. apply In_right ; auto.
        apply In_single.
        rewrite interempty in H2 ; inversion H2.
        apply In_left ; apply E_right.
      }
      {
      }
    
(* (*   intros aVar vX vY v0 aX aY a0 x y c0 vx vy notvxy axy xTree.
  apply (aVarTree_remains' aVar v0 vX a0 aX c0 x y) in xTree ; auto.
  assert ((A_union (E_set x y) a0) (A_ends x y)) as H5.
  apply In_left.
  apply E_right.
  assert (Connected v0 (A_union (E_set x y) a0)) as H7.
  admit.
  assert (A_included a0 (A_union (E_set x y) a0)) as H8.
  admit.
  induction xTree ; intros yTree.
  + (* apply (aVarTree_remains' aVar v0 vY a0 aY c0 x y) in yTree ; auto. *)
    inversion vx.
    rewrite H in *.
    assert ((A_union A_empty aY) = aY).
    rewrite A_union_neutral.
    reflexivity.
    rewrite H0.
    rewrite E_set_eq.
    apply (CC_leaf aVar v0 a1 vY aY y x) ; auto.
    admit.
    admit.
  + induction yTree.
    - simpl in *.
      admit.
    -  *)
  intros aVar vX vY v0 aX aY a0 x y c0 vx vy notvxy axy ainc yTree.
  apply (aVarTree_remains' aVar v0 vY a0 aY c0 x y) in yTree ; auto.
  assert (Connected v0 (A_union (E_set x y) a0)) as H7.
  apply C_edge ; admit.
  assert ((A_union (E_set x y) a0) (A_ends x y)) as axy2.
  admit.
  assert ((A_union (E_set x y) a0) (A_ends y x)) as axy3.
  admit.
  induction yTree ; intros xTree.
  + assert (xTree' := xTree).
    apply (aVarTree_remains' aVar v0 vX a0 aX c0 x y) in xTree' ; auto.
    inversion vy.
    rewrite H in *.
    induction xTree.
    - assert (A_union (E_set x y) (A_union A_empty A_empty) = A_union (E_set x y) A_empty).
      rewrite A_union_neutral.
      reflexivity.
      rewrite H0.
      inversion vx.
      rewrite H1 in *.
      rewrite V_union_commut.
      apply (CC_leaf aVar v0 a1 (V_single x) A_empty x y) ; auto.
      admit.
    - 
      
    inversion vy.
    rewrite H in *.
    assert ((V_union vX (V_single y)) = (V_union (V_single y) vX)).
    rewrite (V_union_commut).
    unfold V_union.
    reflexivity.
    rewrite H0.
    assert ((A_union aX A_empty) = aX).
    rewrite (A_union_commut).
    rewrite A_union_neutral.
    reflexivity.
    rewrite H1.
    apply (CC_leaf aVar v0 a1 vX aX x y) ; auto.
    
  + assert ((V_union vX (V_union (V_single y0) vT)) = (V_union (V_single y0) (V_union vX vT))).
    admit.
    rewrite H.
    assert ((A_union (E_set x y) (A_union aX (A_union (E_set x0 y0) aT))) = (A_union (E_set x0 y0) (A_union (E_set x y) (A_union aX aT)))).
    admit.
    rewrite H0.
    assert (aVarTree aVar v0 a1 (V_union vX vT)
            (A_union (E_set x y) (A_union aX aT))).
    apply IHyTree ; auto.

  + rewrite <- e in *.
    rewrite <- e0 in *.
    apply IHyTree ; auto.  *)
Admitted.



Lemma exists_maxaVarTree : forall (aVar : Var) (v : V_set) (a : A_set) (c0 : Connected v a) (c : Component), 
  v c -> isa_aVarComponent aVar c -> exists (vT : V_set) (aT : A_set) (aTree : aVarTree aVar v a vT aT),
  (vT c /\ max_aVarVset aVar a vT).
Proof.
  (* intros aVar v a c0. 
  assert (forall c : Component, v c -> isa_aVarComponent aVar c -> aVarTree aVar v a (V_single c) A_empty).
  intros.
  apply CC_isolated ; auto.
  induction c0 ; intros d vd isad.
  + exists (V_single d).
    exists (A_empty).
    assert (aVarTree aVar (V_single x) A_empty (V_single d) A_empty).
    apply (H d vd isad).
    exists H0.
    clear H0.
    split.
    apply In_single.
    intros.
    unfold max_aVarVset ; intros.
    destruct H0.
    destruct H1.
    inversion H1.
  + assert (isa_aVarComponent aVar y \/ ~ isa_aVarComponent aVar y).
    apply classic.
    destruct H0. (* ist die neue Komponente eine aVar? j/n*)
    - assert (isa_aVarComponent aVar x \/ ~ isa_aVarComponent aVar x).
      apply classic.
      destruct H1.
      { inversion vd.
        + admit.
        + assert (forall c : Component,
        v0 c ->
        isa_aVarComponent aVar c ->
        aVarTree aVar v0 a0
          (V_single c) A_empty).
          intros.
          apply CC_isolated ; auto.
          assert (v1' := v1).
          apply (IHc0 H4 x) in v1 ; auto.
          clear H4.
          clear H3 vd.
          admit.
      }
      { destruct vd.
        inversion H2.
        rewrite <- H3 in *.
        exists (V_single y).
        exists (A_empty).
        assert (aVarTree aVar (V_union (V_single y) v0)(A_union (E_set x y) a0) (V_single y) A_empty).
        apply (H y).
        apply In_left.
        apply In_single.
        auto.
        exists H4.
        split.
        auto.
        unfold max_aVarVset ; intros.
        destruct H5.
        inversion H5.
        rewrite <- H7 in *.
        destruct H6.
        inversion H6.
        inversion H9.
        rewrite <- H12 in n.
        intuition.
        rewrite <- H12 in *.
        intuition.
        apply Connected_Isa_Graph in c0.
        apply (G_ina_inv1 v0 a0 c0 y c2) in H9.
        intuition.
        apply IHc0 in H2.
        destruct H2.
        destruct H2.
        destruct H2.
        destruct H2.
        exists x1.
        exists x2.
        assert (aVarTree aVar (V_union (V_single y) v0) (A_union (E_set x y) a0) x1 x2).
        apply (aVarTree_remains ) ; auto.
        exists H4.
        split.
        auto.
        apply (maxaVarTree_remains aVar v0 x1 a0 x2 c0 x y x3).
        intuition.
        intuition.
        intros.
        apply CC_isolated ; auto.
        auto.
      }
    - destruct vd. (* ist die Komponente f\u00fcr die wir zeigen sollen, dass sie drin ist die neue Komponente? j/n*)
      { inversion H1.
        rewrite <- H2 in *.
        assert (V_single y y).
        apply In_single.
        assert (aVarTree aVar (V_union (V_single y) v0)(A_union (E_set x y) a0) (V_single y) A_empty).
        apply (H y).
        apply In_left.
        apply In_single.
        auto.
        exists (V_single y).
        exists (A_empty).
        exists H4.
        split.
        auto.
        apply (only_aVars_inaVarTree aVar (V_union (V_single y) v0) (A_union (E_set x y) a0) (V_single y) A_empty H4) in H3.
        intuition.
      }
      { apply IHc0 in H1.
        clear IHc0.
        destruct H1.
        destruct H1.
        destruct H1.
        destruct H1.
        admit. admit. admit.
      }
  + assert (isa_aVarComponent aVar x \/ ~isa_aVarComponent aVar x).
    apply classic.
    destruct H0.
    - assert (isa_aVarComponent aVar y \/ ~isa_aVarComponent aVar y).
      apply classic.
      destruct H1.
      { admit.
        (* assert (forall c : Component,
      v0 c ->
      isa_aVarComponent aVar c ->
      exists (vT : V_set) (aT : A_set) (_ : aVarTree aVar v0
      (A_union (E_set x y) a0) vT aT),
        vT c /\ max_aVarVset aVar (A_union (E_set x y) a0) vT).
        apply (IHc0).
        clear IHc H.
        assert (Hx := H2 x v1 H0).
        assert (Hy := H2 y v2 H1).
        assert (Hd := H2 d vd isad).
        clear H2.
        destruct Hx as [vX Hx].
        destruct Hx as [aX Hx].
        destruct Hx as [xTree Hx].
        destruct Hx as [vXx maxX].
        destruct Hy as [vY Hy].
        destruct Hy as [aY Hy].
        destruct Hy as [yTree Hy].
        destruct Hy as [vYy maxY].
        destruct Hd as [vD Hd].
        destruct Hd as [aD Hd].
        destruct Hd as [dTree Hd].
        destruct Hd as [vDd maxD].
        (* 
           Zwei F\u00e4lle: d liegt in (vTx oder vTy) oder nicht 
             ja: zwei F\u00e4lle: (vTx und vTy haben gemeinsame Knoten) oder nicht
                ja : nehme vTd (alle drei sind die gleichen Knotenmengen)
                nein : nehme Union vTx vTy
             nein: nehme vTd und trivial
        *)
        assert ((vD x \/ vD y) \/ ~(vD x \/ vD y)).
        apply classic.
        destruct H.
        + assert (vX y \/ ~ vX y).
          apply classic.
          destruct H2.
          - exists vD.
            exists aD.
            exists dTree.
            split.
            auto.
            assert (vD x /\ vD y).
            assert (vX = vY).
            apply (two_aVarTrees_same aVar vX vY aX aY xTree yTree).
            unfold max_aVarVset. (* apply maxX. *)
            admit. admit. admit.
            assert (vD = vX).
            admit.
            split.
            rewrite H4 ; auto.
            rewrite H4 ; rewrite H3 ; auto.
            apply (maxaVarTree_remains' aVar v0 vD a0 aD c x y dTree H3 maxD).
          - exists (V_union vX vY).
            exists (A_union (A_union (E_set x y) aX) aY).
            assert (aVarTree aVar (V_union vX vY) (A_union (A_union (E_set x y) aX) aY)).
            
            admit.
(*             beweise, dass zwei bisher getrennte maxTrees vereint ein neuer maxtree sind *)
            admit.
        + exists vD.
          exists aD.
          exists dTree.
          split.
          auto.
          intros.
          apply (maxD c1 c2).
          destruct H2.
          destruct H3.
          split. auto.
          split.
          inversion H3.
          inversion H5.
          rewrite <- H8 in H2.
          assert (False).
          apply H ; auto.
          intuition.
          rewrite <- H8 in H2.
          assert (False).
          apply H ; auto.
          intuition.
          auto.
          auto. *)
      }
      { apply IHc0 in vd.
        clear IHc0.
        destruct vd.
        destruct H2.
        destruct H2.
        destruct H2.
        exists x0. exists x1. admit. (* exists x2.
        split. auto.
        apply (maxaVarTree_remains aVar v0 x0 a0 x1 c x y x2).
        intuition.
        apply H3.
        intros.
        apply (H c0). 
        auto. auto. auto. *)
      }
    - apply IHc0 in vd.
      clear IHc0.
      destruct vd.
      destruct H1.
      destruct H1.
      destruct H1.
      exists x0. exists x1. admit. admit. admit. (*  exists x2.
      split. auto.
      apply (maxaVarTree_remains aVar v0 x0 a0 x1 c x y x2).
      intuition.
      apply H2.
      intros.
      apply (H c0).
      auto. auto. auto. *)
  + rewrite <- e0 in *.
    rewrite <- e in *.
    apply (IHc0 H d vd isad). *)
Admitted.

Lemma allMaxTreesSame_spanningTree : forall (aVar : Var) (v : V_set) (a : A_set) (c : Connected v a) (vT : V_set) (aT : A_set),
  all_maxaVarTreesSame aVar v a -> aVarTree aVar v a vT aT -> max_aVarVset aVar a vT -> 
  is_aVarspanning aVar v vT.
Proof.
  intros aVar v a c vT aT allSame aTree maTree.
  unfold is_aVarspanning.
  intros.
  destruct H.
  apply (exists_maxaVarTree aVar v a) in H.
  destruct H.
  destruct H.
  destruct H.
  destruct H.
  unfold all_maxaVarTreesSame in allSame.
  specialize (allSame vT x aT x0).
  assert (vT = x).
  apply allSame.
  auto.
  auto.
  split ; auto.
  rewrite H2.
  apply H.
  apply c.
  apply H0.
Qed.

Lemma spanningTree_max : forall (aVar : Var) (v : V_set) (a : A_set) (c : Connected v a) (vT : V_set) (aT : A_set),
  is_aVarspanning aVar v vT -> aVarTree aVar v a vT aT ->
  max_aVarVset aVar a vT.
Proof.
  intros aVar v a c vT aT isspanning spanningtree.
  unfold max_aVarVset ; intros.
  destruct H.
  destruct H0.
  unfold is_aVarspanning in isspanning.
  assert (v c2).
  assert (Graph v a).
  apply Connected_Isa_Graph.
  apply c.
  apply (G_ina_inv2 v a H2 c1 c2 H0).
  apply (isspanning c2).
  auto.
Qed.

Lemma aVarTree_means_component : forall (aVar : Var) (v : V_set) (a : A_set) (c : Connected v a) (vT : V_set) (aT : A_set),
  aVarTree aVar v a vT aT -> {x : Component & vT x}.
Proof.
  intros aVar v a c vT aT atree.
  induction atree.
  + exists x.
    apply In_single.
  + destruct IHatree.
    apply c.
    exists x.
    apply In_right.
    apply v1.
  + rewrite <- e in *.
    apply IHatree.
Qed.

Lemma cdr_app :
 forall vl vl' : V_list, vl <> nil -> cdr (vl ++ vl') = cdr vl ++ vl'.
Proof.
        simple induction vl; simpl; intros.
        absurd (V_nil = V_nil); auto.

        trivial.
Qed.

Lemma neq_symm: forall (X : Type) {p q: X}, p <> q -> q <> p.
Proof.
  intros X p q pq.
  unfold not.
  intros.
  apply pq.
  symmetry.
  apply H.
Qed.

Lemma cdr_rev: forall (x: Component) (vl: V_list),
  In x (cdr (rev vl)) -> In x vl.
Proof.
  intros x vl i.
  induction vl.
  simpl in i.
  inversion i.
  unfold In.
  simpl in i.
  destruct vl.
  simpl in i.
  inversion i.
  rewrite cdr_app in i.
  apply in_app_or in i.
  destruct i.
  right.
  apply IHvl.
  apply H.
  left.
  inversion H.
  apply H0.
  inversion H0.
  apply neq_symm.
  apply app_cons_not_nil.
Qed.

Lemma aVarwalk_reverse: forall (aVar : Var) (v : V_set) (a : A_set) (c : Connected v a) (vl : V_list) (el : E_list) (x y : Component)
  (w : Walk v a x y vl el) (aw : aVarWalk aVar v a x y vl el w),
  {vl0 : V_list & {el0 : E_list & {ww: Walk v a y x vl0 el0 & aVarWalk aVar v a y x vl0 el0 ww
                                /\ vl0 = (cdr (rev (x :: vl))) 
                                /\ el0 = (E_reverse el)}}}.
Proof.
  intros aVar v a c vl el x y w aw.
  induction w.
  + exists V_nil.
    exists E_nil.
    exists (W_null v a x v0).
    split.
    apply aw.
    split.
    auto.
    auto.
  + assert (Walk v a x z (y :: vl) (E_ends x y :: el)).
    apply W_step ; auto.
    assert (Graph v a).
    apply Connected_Isa_Graph.
    apply c.
    apply (Walk_reverse v a H0 x z (y :: vl) (E_ends x y :: el)) in H.
    exists (cdr (rev (x :: y :: vl))).
    exists (E_reverse (E_ends x y :: el)).
    exists H.
    split.
    unfold aVarWalk in aw.
    unfold aVarWalk.
    intros.
    destruct vl.
    inversion H1.
    rewrite <- H2 in *.
    inversion w.
    rewrite <- H5 in *.
    apply (aw y).
    simpl.
    right. left. auto.
    simpl in H2.
    destruct H2.
    rewrite <- H2.
    apply (aw x).
    simpl.
    auto.
    inversion H2.
    inversion H1.
    rewrite <- H2 in *.
    assert (w' := w).
    apply (W_iny_vl v a y z (v1 :: vl) el) in w'.
    apply (aw z).
    simpl.
    destruct w'.
    right. right. left. auto.
    right. right. right. auto.
    intuition.
    inversion H3.
    apply cdr_rev in H2.
    apply (aw c0 H2).
    split ; auto.
Qed.

Lemma spanningTree_aTree_max : forall (aVar : Var) (v : V_set) (a : A_set) (c : Connected v a)(vT1 vT2 : V_set) (aT1 aT2 : A_set),
  is_aVarspanning aVar v vT1 -> aVarTree aVar v a vT1 aT1 -> 
  aVarTree aVar v a vT2 aT2 -> max_aVarVset aVar a vT2 -> vT1 = vT2.
Proof.
  intros aVar v a c vt1 vt2 at1 at2 isspanning spantree atree maxtree.
  apply U_set_eq.
  split ; intros.
  + assert (atree' := atree).
    apply (aVarTree_means_component aVar v a c vt2 at2) in atree'.
    destruct atree'.
    assert (v0' := v0).
    assert (v0'' := v0).
    apply (only_aVars_inaVarTree aVar v a vt2 at2 atree) in v0.
    apply (only_vs_inaVarTree aVar v a vt2 at2 atree) in v0'.
    unfold is_aVarspanning in isspanning.
    assert (vt1 x0).
    apply (isspanning x0) ; auto.
    assert (H0' := H0).
    apply (aVarTrees_are_aVarWalks aVar v a c vt1 at1 spantree x x0) in H0'.
    destruct H0'.
    destruct s.
    destruct s.
    assert (Graph v a).
    apply Connected_Isa_Graph.
    apply c.
    assert (x3' := x3).
    apply (Walk_reverse v a H1 x x0 x1 x2) in x3'.
    apply (aVarWalk_in_aVarTree aVar v a vt2 at2 atree x0 x (cdr (rev (x :: x1))) (E_reverse x2) x3') ; auto.
    apply (aVarwalk_reverse aVar v a c x1 x2 x x0 x3) in a0.
    destruct a0.
    destruct s.
    destruct s.
    destruct a0.
    destruct H3.
    unfold aVarWalk in *.
    intros.
    apply (H2 c0).
    simpl in H5.
    destruct H5.
    rewrite H5.
    simpl. left. auto.
    rewrite H3.
    simpl.
    right. apply H5.
    apply H.
  + assert (H' := H).
    apply (only_aVars_inaVarTree aVar v a vt2 at2 atree) in H.
    unfold is_aVarspanning in isspanning.
    apply (only_vs_inaVarTree aVar v a vt2 at2 atree) in H'.
    apply (isspanning x) ; auto.
Qed.

Lemma spanningTree_allMaxTreesSame : forall (aVar : Var) (v : V_set) (a : A_set) (c : Connected v a)(vT : V_set) (aT : A_set),
  is_aVarspanning aVar v vT -> aVarTree aVar v a vT aT -> 
  all_maxaVarTreesSame aVar v a.
Proof.
  intros aVar v a c vT aT isspanning atree.
  unfold all_maxaVarTreesSame.
  intros.
  destruct H.
  unfold is_aVarspanning in isspanning.
  assert (vT = vT1).
  apply (spanningTree_aTree_max aVar v a c vT vT1 aT aT1) ; auto.
  assert (vT = vT2).
  apply (spanningTree_aTree_max aVar v a c vT vT2 aT aT2) ; auto.
  rewrite <- H1.
  auto.
Qed.
    
  
  

Variable state_of : Component -> Data.

Definition get_aVar_leader (aVar : Var) (c : Component) : Component :=
  index (get_leader_index aVar (leaders (state_of c))).








Variable get_aVar_CC : Var -> Component -> (V_set * A_set). 
  (* v muss endlich sein, um das vllt \u00fcber CV_list zu definieren:
     man \u00fcbergibt get_aVar_CC aVar c [CV-Liste] V_nil A_nil
     in jedem Schritt wird c abgearbeitet, indem die Nachbarn untersucht werden 
     wenn Nachbar aVar und in [CV-Liste], dann werden dessen Nachbarn untersucht,
     Nachbar wird von [CV-Liste] gestrichen und n\u00e4chster Nachbar untersucht. *)

Axiom get_aVar_vTaT_is_CC : forall (aVar : Var) (c : Component),
  let (vT, aT) := get_aVar_CC aVar c in
  {v2 : V_set & {a2 : A_set & {_: aVarTree aVar v2 a2 & (vT = v2 /\ aT = a2 /\ v2 c /\ max_aVarVset aVar v2 a2)}}}.

Definition is_aVar_vcc_leader (aVar : Var) (vT : V_set) (c : Component) : Prop :=
  vT c /\ forall (v : Component), vT v -> get_aVar_leader aVar v = c.

Definition is_local_aVar_leader (aVar : Var) (c : Component) : Prop :=
  let (vT, aT) := get_aVar_CC aVar c in
    is_aVar_vcc_leader aVar vT c.

Definition all_leaders_correctly_voted : Prop :=
  forall (aVar : Var), In aVar allVar -> 
   (forall (v1 : Component), v v1 -> is_local_aVar_leader aVar (get_aVar_leader aVar v1)).



(* 

  Theorem: F\u00fcr jeden a-Teilgraph T gilt: in jeder Zusammenhangskomponente K von T gibt es genau einen Leader, der Teil von K ist.

  Invarianten: Nachrichten k\u00f6nnen nur eine Komponente au\u00dferhalb des a-Teilgraphen geschickt werden
  Invarianten: Von allen Komponenten, die man gesehen hat, nimmt man die "h\u00f6chst"-m\u00f6gliche.

  Lemma: Man nimmt nie einen kleineren Leader, als man schon hat.
  Lemma: Man nimmt nur einen Leader von alpha, wenn alpha Teil vom Zeugen des Leaders ist.
  Lemma: Man kann keine Komponente als Leader w\u00e4hlen, wenn der "Zeugenschnitt" mit der Komponente leer ist.
  
*)
(* TODO: bipartition pr\u00fcfen und mit master mergen *)
End ConnectedChecker.