
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
  - last sender, so that the receiving node can make a parent towards the temporary local leader
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

Definition isa_aVar_Component (aVar : Var) (c: Component) : Prop :=
  varList_has_var (init_var_l (component_name c)) aVar.

Inductive aVar_Conn_Comp : Var -> V_set -> A_set -> Set :=
  | CC_isolated : forall (aVar : Var) (x : Component), isa_aVar_Component aVar x -> v x -> aVar_Conn_Comp aVar (V_single x) A_empty
  | CC_leaf: forall (aVar : Var) (vCC : V_set) (aCC : A_set) x y,
      vCC x -> ~ vCC y -> v y -> a (A_ends x y) -> isa_aVar_Component aVar y -> aVar_Conn_Comp aVar vCC aCC -> aVar_Conn_Comp aVar (V_union (V_single y) vCC) (A_union (E_set x y) aCC)
  | CC_edge : forall (aVar : Var)  (vCC : V_set) (aCC : A_set) v1 v2,
      ~ aCC (A_ends v1 v2) -> ~aCC (A_ends v2 v1) -> a (A_ends v1 v2) -> aVar_Conn_Comp aVar vCC aCC -> vCC v1 -> vCC v2 -> v1 <> v2 -> 
      aVar_Conn_Comp aVar vCC (A_union (E_set v1 v2) aCC)
  | CC_eq: forall aVar vCC vCC' aCC aCC',
    vCC = vCC' -> aCC = aCC' -> aVar_Conn_Comp aVar vCC aCC -> aVar_Conn_Comp aVar vCC' aCC'.

Lemma aVar_Conn_Comp_is_Connected : forall (aVar : Var) (vCC: V_set) (aCC: A_set),
  aVar_Conn_Comp aVar vCC aCC -> Connected vCC aCC.
Proof.
  intros aVar vCC aCC cc.
  induction cc.
  + apply C_isolated.
  + apply C_leaf.
    apply IHcc.
    apply v0.
    apply n.
  + apply C_edge.
    apply IHcc.
    apply v0.
    apply v3.
    apply n1.
    apply n.
    apply n0.
  + rewrite <- e in *.
    rewrite <- e0 in *.
    apply IHcc.
Qed.

(* Definition isa_aVar_Conn_Comp (aVar : Var) (vCC : V_set) (aCC : A_set): Prop :=
  vCC <> V_empty /\
  V_included vCC v /\ A_included aCC a /\
  (forall (v1 : Component), vCC v1 -> isa_aVar_Component aVar v1) /\
  (forall (v1 v2 : Component), aCC (A_ends v1 v2) -> (vCC v1 /\ vCC v2)).

Lemma isa_aVar_Conn_Comp_isa_aVar_Conn_Comp : forall (aVar : Var) (vCC : V_set) (aCC : A_set),
  isa_aVar_Conn_Comp aVar vCC aCC -> aVar_Conn_Comp aVar vCC aCC.
Proof.
  intros aVar vCC aCC H.
  unfold isa_aVar_Conn_Comp in H.
  destruct H.
  destruct H0.
  destruct H1.
  destruct H2.
  assert ({x : Component & vCC x}).
  admit.
  destruct H4.
  assert (aVar_Conn_Comp aVar (V_single x) (A_empty)).
  apply (CC_isolated aVar x).
  apply (H2 x v0).
  unfold V_included in H0 ; unfold Included in H0.
  apply (H0 x v0). *)
  

Definition aVar_Connected_Component (aVar : Var) (vCC : V_set) (aCC : A_set): Prop :=
  (forall c1 c2 : Component, (vCC c1 /\ a (A_ends c1 c2) /\ isa_aVar_Component aVar c2) -> vCC c2) /\
  (forall c1 c2 : Component, vCC c1 /\ vCC c2 /\ a (A_ends c1 c2) -> aCC (A_ends c1 c2)).

(* 
Definition disjoint_CC (v1 v2: V_set) (a1 a2: A_set) (aVar : Var) (c1 : aVar_Conn_Comp aVar v1 a1) (c2: aVar_Conn_Comp aVar v2 a2) : Prop := 
  V_inter v1 v2 = V_empty. *)

Lemma only_aVars_inCC: forall (vCC : V_set) (aCC : A_set) (aVar : Var) (cc : aVar_Conn_Comp aVar vCC aCC) (x : Component),
  vCC x -> isa_aVar_Component aVar x.
Proof.
  intros vCC aCC aVar cc x vCCx.
  induction cc.
  + inversion vCCx.
    rewrite H in *.
    apply i.
  + inversion vCCx.
    inversion H.
    rewrite <- H1 ; auto.
    apply (IHcc H).
  + apply (IHcc vCCx).
  + rewrite <- e in vCCx.
    apply (IHcc vCCx).
Qed.

Lemma only_vs_inCC: forall (vCC : V_set) (aCC : A_set) (aVar : Var) (cc : aVar_Conn_Comp aVar vCC aCC) (x : Component),
  vCC x -> v x.
Proof.
  intros vCC aCC aVar cc x H.
  induction cc.
  + inversion H.
    rewrite <- H0.
    apply v0.
  + inversion H.
    inversion H0.
    rewrite <- H2.
    apply v1.
    apply IHcc.
    apply H0.
  + apply (IHcc H).
  + rewrite <- e in *.
    apply (IHcc H).
Qed.

Lemma only_as_inCC: forall (vCC : V_set) (aCC : A_set) (aVar : Var) (cc : aVar_Conn_Comp aVar vCC aCC) (x : Arc),
  aCC x -> a x.
Proof.
  intros vCC aCC aVar cc x H.
  induction cc.
  + inversion H.
  + inversion H.
    inversion H0.
    apply a0.
    assert (Graph v a).
    apply (Connected_Isa_Graph v a g).
    apply (G_non_directed v a H3 x0 y a0).
    apply IHcc.
    apply H0.
  + inversion H.
    inversion H0.
    apply a0.
    assert (Graph v a).
    apply (Connected_Isa_Graph v a g).
    apply (G_non_directed v a H3 v1 v2 a0).
    apply IHcc.
    apply H0.
  + rewrite <- e0 in *.
    apply (IHcc H).
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

Definition aVar_Walk (aVar : Var) (c1 c2 : Component) (vl : V_list) (el : E_list) (w : Walk v a c1 c2 vl el) :=
  forall (c : Component), In c (c1 :: vl) -> isa_aVar_Component aVar c.


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

Lemma CCs_are_aVar_Walks: forall (aVar : Var) (vCC : V_set) (aCC : A_set) (cc : aVar_Conn_Comp aVar vCC aCC),
 (forall (v1 v2 : Component), vCC v1 -> vCC v2 -> {vl : V_list & {el : E_list & {w : Walk v a v1 v2 vl el & aVar_Walk aVar v1 v2 vl el w}}}).
Proof.
  intros aVar vCC aCC cc v1 v2 vCCv1 vCCv2.
  assert (cc' := cc).
  apply aVar_Conn_Comp_is_Connected in cc.
  apply (Connected_path) with (x := v1) (y := v2) in cc.
  destruct cc.
  destruct s.
  exists x.
  exists x0.
  apply Path_isa_trail in p.
  apply Trail_isa_walk in p.
  assert (p' := p).
  apply (Walk_in_bigger_conn vCC v aCC a v1 v2 x x0) in p.
  exists p.
  unfold aVar_Walk.
  intros.
  inversion H.
  rewrite <- H0.
  apply W_endx_inv in p'.
  apply (only_aVars_inCC vCC aCC aVar cc' v1 p').
  assert (vCC c).
  apply (W_invl_inv vCC aCC v1 v2 x x0 p' c H0).
  apply (only_aVars_inCC vCC aCC aVar cc' c H1).
  unfold V_included. unfold Included.
  intros.
  apply (only_vs_inCC vCC aCC aVar cc') in H.
  apply H.
  unfold A_included. unfold Included.
  intros.
  apply (only_as_inCC vCC aCC aVar cc') in H.
  apply H.
  apply vCCv1.
  apply vCCv2.
Qed.

Lemma aVar_Walk_in_CC: forall (aVar : Var) (vCC : V_set) (aCC : A_set) (cc : aVar_Conn_Comp aVar vCC aCC) 
                       (v1 v2: Component) (vl : V_list) (el : E_list) (w : Walk v a v1 v2 vl el),
  aVar_Connected_Component aVar vCC aCC -> vCC v1 -> aVar_Walk aVar v1 v2 vl el w -> vCC v2.
Proof.
  intros aVar vCC aCC cc v1 v2 vl el w CC vCCv1 aWalk.
  induction w ; unfold aVar_Connected_Component in CC ; destruct CC.
  + apply vCCv1.
  + apply IHw.
    unfold aVar_Walk in aWalk.
    specialize (aWalk y).
    simpl in aWalk.
    intuition.
    apply (H x y).
    auto.
    unfold aVar_Walk in *.
    intros.
    apply aWalk.
    inversion H1.
    simpl.
    right. left. auto.
    simpl. right. right. auto.
Qed.

(* wenn sich zwei CCs in c \u00fcberschneiden, so sind \u00fcber c aVar-Walks m\u00f6glich und daher CC1 = CC2 *)
Lemma two_CCs_same_v: forall (aVar : Var) (v1 v2: V_set) (a1 a2: A_set) (c1 : aVar_Conn_Comp aVar v1 a1) (c2: aVar_Conn_Comp aVar v2 a2),
  aVar_Connected_Component aVar v1 a1 -> aVar_Connected_Component aVar v2 a2 -> {c : Component & (v1 c /\ v2 c)} -> 
    (forall x : Component, v1 x -> v2 x).
Proof.
  intros aVar v1 v2 a1 a2 c1 c2 acc1 acc2 same.
  destruct same.
  destruct a0. intros.
  apply (CCs_are_aVar_Walks aVar v1 a1 c1 x x0) in H1.
  destruct H1.
  destruct s.
  destruct s.
  apply (aVar_Walk_in_CC aVar v2 a2 c2 x x0 x1 x2 x3 acc2 H0 a0).
  apply H.
Qed.

Lemma CC_all_connections: forall (aVar : Var) (vCC : V_set) (aCC : A_set) (cc : aVar_Conn_Comp aVar vCC aCC) 
                       (v1 v2: Component),
  aVar_Connected_Component aVar vCC aCC -> vCC v1 -> vCC v2 -> a (A_ends v1 v2) -> aCC (A_ends v1 v2).
Proof.
  intros aVar vCC aCC cc v1 v2 CC vCCv1 vCCv2 aends.
  unfold aVar_Connected_Component in CC.
  destruct CC.
  specialize (H0 v1 v2).
  apply H0.
  auto.
Qed.

Lemma CC_a_means_v: forall (aVar : Var) (vCC : V_set) (aCC : A_set) (cc : aVar_Conn_Comp aVar vCC aCC) 
                       (v1 v2: Component),
  aCC (A_ends v1 v2) -> (vCC v1 /\ vCC v2).
Proof.
  intros aVar vCC aCC cc v1 v2 acca.
  induction cc.
  + inversion acca.
  + inversion acca.
    - inversion H.
      rewrite <- H2 in *.
      rewrite <- H3 in *.
      split.
      apply In_right. apply v0.
      apply In_left.
      apply In_single.
      split.
      apply In_left ; apply In_single.
      rewrite <- H2 in *.
      rewrite <- H3 in *.
      apply In_right. apply v0.
    - apply IHcc in H.
      destruct H.
      split ; apply In_right.
      apply H.
      apply H1.
  + inversion acca.
    - inversion H.
      rewrite <- H2 in *.
      rewrite <- H3 in *.
      auto.
      rewrite <- H2.
      rewrite <- H3.
      auto.
    - apply (IHcc H).
  + rewrite <- e in *.
    rewrite <- e0 in *.
    apply (IHcc acca).
Qed.

Lemma CC_a_means_a: forall (aVar : Var) (vCC : V_set) (aCC : A_set) (cc : aVar_Conn_Comp aVar vCC aCC) 
                       (ar: Arc),
  aCC ar -> a ar.
Proof.
  intros aVar vCC aCC cc ar acca.
  induction cc.
  + inversion acca.
  + inversion acca.
    inversion H.
    apply a0.
    assert (Graph v a).
    apply (Connected_Isa_Graph v a g).
    apply (G_non_directed v a H2 x y a0).
    apply (IHcc H).
  + inversion acca.
    inversion H.
    apply a0.
    assert (Graph v a).
    apply (Connected_Isa_Graph v a g).
    apply (G_non_directed v a H2 v1 v2 a0).
    apply (IHcc H).
  + rewrite <- e0 in *.
    apply (IHcc acca).
Qed.

Lemma two_CCs_same_a: forall (aVar : Var) (v1 v2: V_set) (a1 a2: A_set) (c1 : aVar_Conn_Comp aVar v1 a1) (c2: aVar_Conn_Comp aVar v2 a2),
  aVar_Connected_Component aVar v1 a1 -> aVar_Connected_Component aVar v2 a2 -> {c : Component & (v1 c /\ v2 c)} -> 
    (forall x : Arc, a1 x -> a2 x).
Proof.
  intros aVar v1 v2 a1 a2 c1 c2 acc1 acc2 same.
  assert (same' := same).
  destruct same.
  destruct a0. intros.
  destruct x0.
  assert (H1' := H1).
  apply (CC_a_means_v aVar v1 a1 c1 v0 v3) in H1.
  destruct H1.
  apply (two_CCs_same_v aVar v1 v2 a1 a2 c1 c2 acc1 acc2 same') in H1.
  apply (two_CCs_same_v aVar v1 v2 a1 a2 c1 c2 acc1 acc2 same') in H2.
  apply (CC_all_connections aVar v2 a2 c2 v0 v3 acc2).
  apply H1.
  apply H2.
  apply (CC_a_means_a aVar v1 a1 c1 (A_ends v0 v3)) in H1'.
  apply H1'.
Qed.

Lemma two_CCs_same: forall (aVar : Var) (v1 v2: V_set) (a1 a2: A_set) (c1 : aVar_Conn_Comp aVar v1 a1) (c2: aVar_Conn_Comp aVar v2 a2),
  aVar_Connected_Component aVar v1 a1 -> aVar_Connected_Component aVar v2 a2 -> {c : Component & (v1 c /\ v2 c)} -> 
    (v1 = v2 /\ a1 = a2).
Proof.
  intros aVar v1 v2 a1 a2 c1 c2 acc1 acc2 same.
  split.
  + assert (forall x : Component, v1 x -> v2 x).
    intros.
    apply (two_CCs_same_v aVar v1 v2 a1 a2 c1 c2 acc1 acc2 same x) in H.
    apply H.
    assert ({c : Component & v2 c /\ v1 c}).
    destruct same.
    destruct a0.
    exists x. auto.
    assert (forall x : Component, v2 x -> v1 x).
    intros.
    apply (two_CCs_same_v aVar v2 v1 a2 a1 c2 c1 acc2 acc1 H0 x) in H1.
    apply H1.
    apply U_set_eq.
    split.
    apply H.
    apply H1.
  + assert (forall x : Arc, a1 x -> a2 x).
    intros.
    apply (two_CCs_same_a aVar v1 v2 a1 a2 c1 c2 acc1 acc2 same x) in H.
    apply H.
    assert (forall x : Arc, a2 x -> a1 x).
    intros.
    assert ({c : Component & v2 c /\ v1 c}).
    destruct same.
    destruct a0.
    exists x0. auto.
    apply (two_CCs_same_a aVar v2 v1 a2 a1 c2 c1 acc2 acc1 H1 x) in H0.
    apply H0.
    apply U_set_eq.
    split.
    apply H.
    apply H0.
Qed.

Lemma two_CCs_same': forall (aVar : Var) (v1 v2: V_set) (a1 a2: A_set) (c1 : aVar_Conn_Comp aVar v1 a1) (c2: aVar_Conn_Comp aVar v2 a2),
  aVar_Connected_Component aVar v1 a1 -> aVar_Connected_Component aVar v2 a2 -> {ar : Arc & (a1 ar /\ a2 ar)} -> 
    (v1 = v2 /\ a1 = a2).
Proof.
  intros aVar v1 v2 a1 a2 c1 c2 acc1 acc2 same.
  destruct same.
  destruct a0.
  assert (forall v1 v2 v a aVar (c1 : aVar_Conn_Comp aVar v a), a (A_ends v1 v2) -> (v v1 /\ v v2)).
  - intros.
    induction c0.
    + inversion H1.
    + inversion H1.
      inversion H2.
      rewrite <- H5 in *.
      rewrite <- H6 in *.
      split.
      apply In_right.
      apply v4.
      apply In_left.
      apply In_single.
      split.
      apply In_left.
      apply In_single.
      rewrite <- H5 in *.
      rewrite <- H6 in *.
      apply In_right.
      apply v4.
      apply (CC_a_means_v aVar0 vCC aCC c0) in H2.
      destruct H2.
      split.
      apply In_right.
      apply H2.
      apply In_right.
      apply H4.
    + inversion H1.
      inversion H2.
      rewrite <- H5 in *.
      rewrite <- H6 in *.
      split.
      apply v6.
      apply v7.
      rewrite <- H5 in *.
      rewrite <- H6 in *.
      split ; auto.
      apply (CC_a_means_v aVar0 vCC aCC c0) in H2.
      destruct H2.
      auto.
    + rewrite <- e in *.
      rewrite <- e0 in *.
      apply (IHc0 H1).
  - destruct x.
    specialize (H1 v0 v3).
    assert (v1 v0 /\ v1 v3).
    apply (H1 v1 a1 aVar c1 H).
    assert (v2 v0 /\ v2 v3).
    apply (H1 v2 a2 aVar c2 H0).
    destruct H2.
    destruct H3.
    apply (two_CCs_same aVar _ _ _ _ c1 c2 acc1 acc2).
    exists v0.
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

Axiom get_aVar_vCCaCC_is_CC : forall (aVar : Var) (c : Component),
  let (vCC, aCC) := get_aVar_CC aVar c in
  {v2 : V_set & {a2 : A_set & {_: aVar_Conn_Comp aVar v2 a2 & (vCC = v2 /\ aCC = a2 /\ v2 c /\ aVar_Connected_Component aVar v2 a2)}}}.

Definition is_aVar_vcc_leader (aVar : Var) (vCC : V_set) (c : Component) : Prop :=
  vCC c /\ forall (v : Component), vCC v -> get_aVar_leader aVar v = c.

Definition is_local_aVar_leader (aVar : Var) (c : Component) : Prop :=
  let (vCC, aCC) := get_aVar_CC aVar c in
    is_aVar_vcc_leader aVar vCC c.

Definition all_leaders_correctly_voted : Prop :=
  forall (aVar : Var), In aVar allVar -> 
   (forall (v1 : Component), v v1 -> is_local_aVar_leader aVar (get_aVar_leader aVar v1)).




TODO getaVarCC mit Typ Connected
     isavarccleader
Definition gamma_i (i:Component)(leader_i:Component)(distance_i:nat)(parent_i:Component)(leader_parent_i:Component)(distance_parent_i:nat)
(leader_neighbors : C_list)
:Prop :=
aSG (A_ends i (parent i)) /\
distance i = distance (parent i) + 1 /\
/\ ((forall (k:Component), In k leader_neighbors-> k = leader i))
/\ ((forall (c:Component), In c (neighbors g i) -> In (leader c) leader_neighbors)). (*consistency in neighbourhood leader*)

Definition gamma_root (i:Component)(leader_i:Component)(distance_i:nat)(parent_i:Component)(leader_neighbors : C_list)
: Prop :=
leader i = i /\
parent i = i /\
distance i = 0
/\ ((forall (k:Component), In k leader_neighbors -> k = leader i))
/\ ((forall (c:Component), In c (neighbors g i)  -> In (leader c) leader_neighbors)). 


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