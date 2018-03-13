
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
Fixpoint initial_send_list (me : Name) cert neighbours: list (Name * Msg) :=
  match cert with
    | [] => []
    | hd :: tl => sendlist neighbours (leader ((assignment_var hd), component_index (name_component me), 0, me)) ++ initial_send_list me tl neighbours
  end.

(* This input starts a checker *)
Inductive Input := alg_terminated : Input.

(* kann weggelassen werden? *)
Definition Output := Msg.


(* eigentlich muss noch irgendwo eine Pr\u00fcfung rein, dass certificate zu var_l passt, denn sonst kann der Algorithmus den Checker betr\u00fcgen... *)
Definition InputHandler (me : Name) (c : Input) (state: Data) :
            (list Output) * Data * list (Name * Msg) := 
	match me  with
    | Checker x => let myneighbours := (neighbors v a g x) in
                     ([] , (mkData (checkerknowledge state) (checkerinput state) (leaders state)), initial_send_list me (certificate(* das hier m\u00fcsste var_l sein oder eine Pr\u00fcfung beinhalten *) (checkerinput state)) myneighbours)
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

(* 

  Theorem: F\u00fcr jeden a-Teilgraph T gilt: in jeder Zusammenhangskomponente K von T gibt es genau einen Leader, der Teil von K ist.

  Invarianten: Nachrichten k\u00f6nnen nur eine Komponente au\u00dferhalb des a-Teilgraphen geschickt werden
  Invarianten: Von allen Komponenten, die man gesehen hat, nimmt man die "h\u00f6chst"-m\u00f6gliche.

  Lemma: Man nimmt nie einen kleineren Leader, als man schon hat.
  Lemma: Man nimmt nur einen Leader von alpha, wenn alpha Teil vom Zeugen des Leaders ist.
  Lemma: Man kann keine Komponente als Leader w\u00e4hlen, wenn der "Zeugenschnitt" mit der Komponente leer ist.
  
*)

Definition NetHandler (me : Name) (src: Name) (le : Msg) (state: Data) : 
    (list Output) * Data * list (Name * Msg) :=
    match le with
      | leader (var, n, d, p)  => if (varList_has_var (var_l (checkerknowledge state)) var) && Nat.ltb (get_leader_index var (leaders state)) n
                                    then ([], set_leaders state (set_leader var n d p (leaders state)), sendlist (neighbor_l (checkerknowledge state)) (leader (var, n, d+1, me)))
                                  else ([], state, [])
    end.


Inductive SubGraph : V_set -> V_set -> A_set -> A_set -> Set :=
  | SG_empty : forall v a (g: Graph v a), SubGraph V_empty v A_empty a
  | SG_vertex: forall (vSG v : V_set) (aSG a : A_set) x (g: Graph v a),
      ~ vSG x -> v x -> SubGraph vSG v aSG a -> SubGraph (V_union (V_single x) vSG) v aSG a
  | SG_vertexp: forall (vSG v : V_set) (aSG a : A_set) x (g: Graph v a),
      Graph (V_union (V_single x) v) a -> SubGraph vSG v aSG a -> SubGraph vSG (V_union (V_single x) v) aSG a
  | SG_edge : forall (vSG v : V_set) (aSG a : A_set) v1 v2 (g: Graph v a),
      ~ aSG (A_ends v1 v2) -> ~aSG (A_ends v2 v1) -> a (A_ends v1 v2) -> SubGraph vSG v aSG a -> vSG v1 -> vSG v2 -> v1 <> v2 -> SubGraph vSG v (A_union (E_set v1 v2) aSG) a
  | SG_edgep : forall (vSG v : V_set) (aSG a : A_set) (x : Arc) v1 v2 (g: Graph v a),
    Graph v (A_union (E_set v1 v2) a) -> SubGraph vSG v aSG a -> SubGraph vSG v aSG (A_union (E_set v1 v2) a)
  | SG_eq: forall vSG vSG' v aSG aSG' a (g: Graph v a),
    vSG = vSG' -> aSG = aSG' -> SubGraph vSG v aSG a -> SubGraph vSG' v aSG' a.
(* TODO: vllt muss auch noch rein: SG_eqp *)

Lemma Graph_is_a_SubGraph: forall v a (g: Graph v a), SubGraph v v a a.
Proof.
  intros v a g.
  induction g.
    apply SG_empty. apply G_empty.

    apply (SG_vertex v0 (V_union (V_single x) v0) a0 a0).
    apply G_vertex.
    apply g0. apply n. apply n. apply In_left. apply In_single.
    apply (SG_vertexp).
    apply g0. apply G_vertex. apply g0. apply n.
    apply IHg.

    apply (SG_edge v0 v0 a0 (A_union (E_set x y) a0) x y).
    apply (G_edge). apply g0. apply v1. apply v2. apply n. apply n0. apply n1. apply n0. apply n1.
    apply In_left. apply E_right.
    apply (SG_edgep v0 v0 a0 a0 (A_ends x y)).
    apply g0. apply G_edge. apply g0. apply v1. apply v2. apply n. apply n0. apply n1.
    apply IHg. apply v1. apply v2. apply n.

    rewrite <- e. rewrite <- e0. apply IHg.
Qed.

Lemma EmptyGraph_isa_SubGraph: forall v a (g: Graph v a), SubGraph V_empty v A_empty a.
Proof.
  intros v a g.
  apply SG_empty. apply g.
Qed.

Lemma SubGraph_isa_Graph : forall vSG v aSG a (g: Graph v a), SubGraph vSG v aSG a -> Graph vSG aSG.
Proof.
  intros vSG v aSG a g H.
  induction H.

    apply G_empty.

    apply G_vertex.
    apply (IHSubGraph g). apply n.

    apply (IHSubGraph g0).

    apply G_edge.
    apply (IHSubGraph g).
    apply v3. apply v4. apply n1. apply n. apply n0.

    apply (IHSubGraph g0).

    rewrite <- e. rewrite <- e0. apply (IHSubGraph g0).
Qed.

Lemma empty_sub_set: forall T vSG, Included T vSG (Empty T) -> vSG = Empty T.
Proof.
  intros.
  apply U_set_eq.
  intros.
  split.
  intros.
  apply (H x H0).
  intros.
  inversion H0.
Qed.

Lemma SubGraph_vertices_included : forall (vSG v : V_set) (aSG a : A_set) (g : Graph v a),
  SubGraph vSG v aSG a -> V_included vSG v.
Proof.
  intros vSG v aSG a g SG.
  induction SG ; unfold V_included ; unfold Included ; intros.
    inversion H.

    inversion H. inversion H0. rewrite H2 in *. apply v1.
    apply IHSG in g0. unfold V_included in g0. unfold Included in g0.
    apply g0 in H0. apply H0.

    apply IHSG in g0. unfold V_included in g0. unfold Included in g0.
    apply g0 in H. apply In_right. apply H.

    apply IHSG in g0. unfold V_included in g0. unfold Included in g0.
    apply g0 in H. apply H.

    apply IHSG in g0. unfold V_included in g0. unfold Included in g0.
    apply g0 in H. apply H.

    apply IHSG in g0. unfold V_included in g0. unfold Included in g0.
    rewrite <- e in *. rewrite e0 in *. apply g0 in H. apply H.
Qed.

Lemma SubGraph_arcs_included : forall (vSG v : V_set) (aSG a : A_set) (g : Graph v a),
  SubGraph vSG v aSG a -> A_included aSG a.
Proof.
  intros vSG v aSG a g SG.
  induction SG ; unfold A_included ; unfold Included ; intros.
    inversion H.

    apply IHSG in g0. unfold A_included in g0. unfold Included in g0.
    apply g0 in H. apply H.

    apply IHSG in g0. unfold A_included in g0. unfold Included in g0.
    apply g0 in H. apply H.


    inversion H. inversion H0. rewrite H2 in *. apply a1.
    apply (G_non_directed v0 a0 g v1 v2 a1).
    apply IHSG in g0. unfold A_included in g0. unfold Included in g0.
    apply (g0 x H0).

    unfold A_union. apply In_right. apply IHSG in g0.
    unfold A_included in g0. unfold Included in g0.
    apply (g0 x0 H).

    apply IHSG in g0. unfold A_included in g0. unfold Included in g0.
    rewrite <- e0 in *. apply (g0 x H).
Qed.

Lemma SubGraph_arcs_correct : forall (vSG v : V_set) (aSG a : A_set) (g : Graph v a),
  SubGraph vSG v aSG a -> (forall (v1 v2 : Component), let ar := (A_ends v1 v2) in
                                 (aSG ar) -> (vSG v1 /\ vSG v2)).
Proof.
  intros vSG v0 aSG a0 g SG.
  induction SG ; unfold V_included ; unfold A_included ; unfold Included ; split ; intros.
    inversion H.

    inversion H.

    unfold V_union. apply In_right.
    apply IHSG with (v1 := v2) (v2 := v3) in g0.
    destruct g0. apply H0. apply H.

    unfold V_union. apply In_right.
    apply IHSG with (v1 := v2) (v2 := v3) in g0.
    destruct g0. apply H1. apply H.

    apply IHSG with (v1 := v1) (v2 := v2) in g0.
    destruct g0. apply H0. apply H.

    apply IHSG with (v1 := v1) (v2 := v2) in g0.
    destruct g0. apply H1. apply H.

    inversion H. inversion H0 ; rewrite H3 in * ; rewrite H4 in *.
    apply v3. apply v4.
    apply IHSG with (v1 := v5) (v2 := v6) in g0.
    destruct g0. apply H2. apply H0.

    inversion H. inversion H0 ; rewrite H3 in * ; rewrite H4 in *.
    apply v4. apply v3.
    apply IHSG with (v1 := v5) (v2 := v6) in g0.
    destruct g0. apply H3. apply H0.

    apply IHSG with (v1 := v3) (v2 := v4) in g0. destruct g0.
    apply H0. apply H.

    apply IHSG with (v1 := v3) (v2 := v4) in g0. destruct g0.
    apply H1. apply H.

    rewrite <- e in *. rewrite <- e0 in *.
    apply IHSG with (v1 := v1) (v2 := v2) in g0. destruct g0.
    apply H0. apply H.

    rewrite <- e in *. rewrite <- e0 in *.
    apply IHSG with (v1 := v1) (v2 := v2) in g0. destruct g0.
    apply H1. apply H.
Qed.

Definition disjoint_G (v0 v1 : V_set) (a0 a1 : A_set) (g0 : Graph v0 a0) (g1: Graph v1 a1) := 
  V_inter v0 v1 = V_empty.

Definition disjoint_SG (v0 v1 v2: V_set) (a0 a1 a2: A_set) (g0 : SubGraph v1 v0 a1 a0) (g1: SubGraph v2 v0 a2 a0) : Prop := 
  V_inter v1 v2 = V_empty.

Fixpoint SG_list_union (vSG : V_set) (aSG : A_set) (v_a_l : list (V_set * A_set)) : (V_set * A_set) :=
  match v_a_l with
  | nil => (vSG, aSG)
  | (v0, a0) :: tl => SG_list_union (V_union vSG v0) (A_union aSG a0) tl
  end.

Definition SGs_cover_Graph (v : V_set) (a : A_set) (g : Graph v a) (v_a_l : list (V_set * A_set)) : Prop :=
  let (vSG_union, aSG_union) := (SG_list_union V_empty A_empty v_a_l) in
    V_included v vSG_union /\ A_included a aSG_union.


(* jeder Komponente wird ein Zertifikat () zugeordnet,
je nach Zertifikat ist die Komponente dann eine a-Komponente oder nicht
der a-Teil-Graph ist der Teil eines Graphen, von dem alle Komponenten a-Komponenten sind 
und keine weiteren a-Komponenten im Graphen sind, aber nicht im aTG. *)


Definition isa_aVar_Component (c: Component) (aVar : Var) : bool :=
  varList_has_var (init_var_l (component_name c)) aVar.


Definition aVar_SubGraph (v vSG: V_set) (a aSG: A_set) (g : Graph v a) (aVar : Var) : SubGraph vSG v aSG a :=
  (forall c : Component, (v c /\ isa_aVar_Component c aVar) -> vSG c) /\
  (forall c1 c2 : Component, (a (A_ends c1 c2) /\ isa_aVar_Component c1 aVar /\ isa_aVar_Component c2 aVar) -> vSG (A_ends c1 c2)).

(* TODO: bipartition pr\u00fcfen und mit master mergen *)


End ConnectedChecker.