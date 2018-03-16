
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

Fixpoint sendlist (neighbors: list Component) (new_l: Msg): list (Name * Msg)  :=
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
  | CC_isolated : forall (aVar : Var) (x : Vertex), isa_aVar_Component aVar x -> v x -> aVar_Conn_Comp aVar (V_single x) A_empty
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

Definition aVar_Connected_Component (aVar : Var) (vCC : V_set) (aCC : A_set) (cc : aVar_Conn_Comp aVar vCC aCC): Prop :=
  (forall c1 c2 : Component, (vCC c1 /\ a (A_ends c1 c2) /\ isa_aVar_Component aVar c2) -> vCC c2) /\
  (forall c1 c2 : Component, vCC c1 /\ vCC c2 /\ a (A_ends c1 c2) -> aCC (A_ends c1 c2)).

(* Lemma aVar_Connected_Component_is_Connected : forall (aVar : Var) (vCC: V_set) (aCC: A_set) (cc : aVar_Conn_Comp aVar vCC aCC),
  aVar_Connected_Component aVar vCC aCC cc -> Connected vCC aCC.
Proof.
  intros aVar vCC aCC cc H.
  clear H.
  apply aVar_Conn_Comp_is_Connected in cc.
  apply cc.
Qed.

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

Lemma two_CCs_are_same: forall (v1 v2: V_set) (a1 a2: A_set) (aVar : Var) (c1 : aVar_Conn_Comp aVar v1 a1) (c2: aVar_Conn_Comp aVar v2 a2),
  aVar_Connected_Component aVar v1 a1 c1 -> aVar_Connected_Component aVar v2 a2 c2 -> {c : Component & (v1 c /\ v2 c)} -> 
    ((forall x : Vertex, v1 x -> v2 x) /\ forall x : Arc, a1 x -> a2 x).
Proof.
  intros v1 v2 a1 a2 aVar c1 c2 acc1 acc2 same.
  destruct same.
  destruct a0.
  induction c1.
  inversion H.
  rewrite <- H in *.
  clear H1 ; clear H ; clear x.
  + split.
    intros.
    inversion H.
    rewrite H1 in *.
    apply H0.
    intros.
    inversion H.
  +   
       
    



Lemma two_CCs_are_same: forall (v1 v2: V_set) (a1 a2: A_set) (aVar : Var) (c1 : aVar_Conn_Comp aVar v1 a1) (c2: aVar_Conn_Comp aVar v2 a2),
  aVar_Connected_Component aVar v1 a1 c1 -> aVar_Connected_Component aVar v2 a2 c2 -> {c : Component & (v1 c /\ v2 c)} -> 
    (v1 = v2 /\ a1 = a2).
Proof.
  intros v1 v2 a1 a2 aVar c1. (* intros c1 c2 H1 H2 H3. *)
  induction c1.
  intros c2 H1 H2 H3.
  + destruct H3.
    destruct a0.
    inversion H.
    rewrite <- H3 in *.
    clear H ; clear H3 ; clear x0.
    induction c2.
    - inversion H0.
      auto.
    - clear IHc2.
      destruct H1.
      destruct H2.
      inversion H0.
      inversion H4.
      clear H5 ; clear x1 ; clear H4.
      rewrite H6 in *.
      clear H0.
      specialize (H x x0).
      assert (V_single x x0).
      apply H.
      split.
      apply In_single.
      split.
      admit. (* G_non_directed *)
      apply (only_aVars_inCC vCC aCC aVar c2 x0).
      apply v1.
      inversion H0.
      rewrite <- H4 in *.
      apply n in v1.
      intuition.
      clear H5 ; clear x1.
      
    

    induction c2 ; destruct H3.
    - destruct a0.
      inversion H.
      inversion H0.
      auto.
    - specialize (IHc2 i).
      assert (H1' := H1).
      apply IHc2 in H1.
      destruct H1.
      rewrite <- H0 in *.
      assert (v7 := v1).
      rewrite <- H in v7.
      inversion v7.
      rewrite <- H1 in *.
      unfold aVar_Connected_Component in H1'.
      destruct H1'.
      specialize (H3 x y).
      assert (V_single x y).
      apply H3.
      split ; auto.
      rewrite H1.
      auto.
      inversion H5.
      assert (H7:=v1).
      rewrite <- H1 in H7.
      rewrite H6 in H7.
      apply n in H7.
      
      intuition.
      

      
      
      
  

(* Lemma: if two subgraphs are maximal for some aVar, and share some vertex -> they are the same. *)
Lemma two_max_sgs_are_same: forall (vSG1 vSG2: V_set) (a aSG1 aSG2: A_set) (g : Graph v a) (aVar : Var) 
                                   (sg1 : SubGraph vSG1 v aSG1 a) (sg2 : SubGraph vSG2 v aSG2 a),
  aVar_SubGraph v vSG1 a aSG1 g aVar sg1 -> aVar_SubGraph v vSG2 a aSG2 g aVar sg2 -> 
  aVar_connected_Component v vSG1 a aSG1 g aVar sg1 -> aVar_connected_Component v vSG2 a aSG2 g aVar sg2 -> 
  {c : Component & (vSG1 c /\ vSG2 c)} ->
  (vSG1 = vSG2 /\ aSG1 = aSG2).
Proof.
  intros v vSG1 vSG2 a aSG1 aSG2 g aVar sg1 sg2 H1 H2 H3 H4 H5.
  unfold aVar_SubGraph in *.
  unfold aVar_connected_Component in *.
  destruct H5.
  destruct a0.
  destruct H1.
  destruct H2.
(* Axiom U_set_eq : forall E F : U_set, (forall x : U, E x <-> F x) -> E = F. *)
Admitted.

(* Definition SG_list := list (V_set * A_set).

(* We only use finite subgraphs, therefore this holds. *)
Axiom SG_eq_dec: forall x y : (V_set * A_set), {x = y} + {x <> y}.


(* A Graph is cut into a list of subgraphs, for some aVar. All vertices that are aVar-Components must be represented in some subgraph.
   The list must be unique. For alle subgraphs it must be an aVar-subgraph and maximal. *)
Definition Graph_in_aVar_max_connected_SubGraphs (v : V_set) (a : A_set) (g : Graph v a) (aVar : Var) (sgs : SG_list) : Prop :=
  (forall (comp : Component), (v comp /\ isa_aVar_Component comp aVar) -> (exists vSG aSG, In (vSG, aSG) sgs /\ vSG comp)) /\
  nodup SG_eq_dec sgs = sgs /\
  (forall vSG aSG, In (vSG, aSG) sgs -> (exists (sg : SubGraph vSG v aSG a), 
                                          aVar_SubGraph v vSG a aSG g aVar sg /\ is_max_connected_SubGraph v vSG a aSG g aVar sg)).

Definition Graph_in_SubGraphs (v : V_set) (a : A_set) (g : Graph v a) (aVarSG : list (Var * SG_list)) : Prop :=
  (forall (aVar : Var) (sgl : SG_list), In (aVar, sgl) aVarSG -> (Graph_in_aVar_max_connected_SubGraphs v a g aVar sgl)). *)

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











Theorem 

(* 
  von Samira
  exists (l : Component), v l -> forall (x:Component)(prop1: v x), leader x = l.
*)
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