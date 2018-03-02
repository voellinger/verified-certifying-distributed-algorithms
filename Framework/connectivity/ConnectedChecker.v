
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




(* This is the content of a message and consists of some var and the current local leader for that var *)
Inductive Leader_Entry := leader : (Var * nat) -> Leader_Entry.

Definition Leader_Entry_eq_dec : forall x y : Leader_Entry, {x = y} + {x <> y}.
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
  leaders : list Leader_Entry
}.

(* all components first are their own leader for all fact_vars *)
Fixpoint init_leader_list (n:Name) (c: Certificate) :=
  match c with
  | [] => []
  | hd :: tl => (leader (assignment_var hd, component_index (name_component n))) :: init_leader_list n tl
  end.

(* initialization of the network *)
Definition init_Data (me: Name) := 
  mkData (init_Checkerknowledge me) (init_Checkerinput me) (init_leader_list me (certificate (init_Checkerinput me))).


Definition set_leaders a v := mkData (checkerknowledge a) (checkerinput a) v.

Fixpoint sendlist (neighbors: list Component) (new_l: Leader_Entry): list (Name * Leader_Entry)  :=
  match neighbors with 
    | nil => []
    | hd :: tl => (Checker hd, new_l) :: (sendlist tl new_l)
  end.

(* The component sends itself as the leader for all its fact_vars to all its neighbours *)
Fixpoint initial_send_list (me : Name) cert neighbours: list (Name * Leader_Entry) :=
  match cert with
    | [] => []
    | hd :: tl => sendlist neighbours (leader ((assignment_var hd), component_index (name_component me))) ++ initial_send_list me tl neighbours
  end.

(* This input starts a checker *)
Inductive Input := alg_terminated : Input.

(* kann weggelassen werden? *)
Definition Output := Leader_Entry.


(*  *)
Definition InputHandler (me : Name) (c : Input) (state: Data) :
            (list Output) * Data * list (Name * Leader_Entry) := 
	match me  with
    | Checker x => let myneighbours := (neighbors v a g x) in
                     ([] , (mkData (checkerknowledge state) (checkerinput state) (leaders state)), initial_send_list me (certificate (checkerinput state)) myneighbours)
    end.

Fixpoint find_leader (k : nat) (leaders : list Leader_Entry) : option nat :=
  match leaders with
  | [] => None
  | leader (var, ind) :: tl => if beq_nat k var
                            then Some ind
                            else find_leader k tl
  end.

Definition get_leader_index k (leaders: list Leader_Entry) : nat :=
  match (find_leader k leaders) with
  | Some x => x
  | None => 0
  end.

Fixpoint set_leader var n (ls: list Leader_Entry) : list Leader_Entry :=
  match ls with
  | [] => [leader (var, n)]
  | leader (k, ind) :: tl => if beq_nat k var 
                                 then leader (var, n) :: tl
                                 else set_leader var n tl
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
  

Lemma set_leader_sets_leader: forall var n (ls: list Leader_Entry),
    n = get_leader_index var (set_leader var n ls).
Proof.
  intros var n ls.
  induction ls.
    destruct var.
    simpl.
    unfold get_leader_index.
    reflexivity.
    simpl.
    unfold get_leader_index.
    unfold find_leader.
    simpl.
    rewrite <- beq_nat_refl.
    reflexivity.

    simpl.
    destruct a0.
    destruct p.
    assert (v0 = var \/ v0 <> var).
    apply classic.
    destruct H.
  
    rewrite H.
    rewrite Nat.eqb_refl.
    unfold get_leader_index.
    simpl.
    rewrite Nat.eqb_refl.
    reflexivity.

    assert(v0 == var = false).
    apply beq_false_nat.
    intuition.
    rewrite H0.
    apply IHls.
Qed.

(* 

  Theorem: F\u00fcr jeden a-Teilgraph gilt: in jeder Zusammenhangskomponente K von T gibt es genau einen Leader, der Teil von K ist.

  Invarianten: Nachrichten k\u00f6nnen nur eins aus der a-Komponente geschickt werden
  Invarianten: Von allen Komponenten, die man gesehen hat, nimmt man die "h\u00f6chst"-m\u00f6gliche.

  Lemma: Man nimmt nie einen kleineren Leader, als man schon hat.
  Lemma: Man nimmt nur einen Leader von alpha, wenn alpha Teil vom Zeugen des Leaders ist.
  Lemma: Man kann keine Komponente als Leader w\u00e4hlen, wenn der "Zeugenschnitt" mit der Komponente leer ist.
  
*)


Definition NetHandler (me : Name) (src: Name) (le : Leader_Entry) (state: Data) : 
    (list Output) * Data * list (Name * Leader_Entry) :=
    match le with
(* Zusatzvariable "terminated", wie/wann wird sie gesetzt? *)
(* mitschicken, von wo der Leader kommt und diese dann r\u00fcckw\u00e4rts als parent/distance-relation aufbauen *)
      | leader (var, n)  => if (Nat.ltb (get_leader_index var (leaders state)) n) then (* //nur, wenn find_leader Some x zur\u00fcck gibt!! *)
                              ([], set_leaders state (set_leader var n (leaders state)), sendlist (neighbor_l (checkerknowledge state)) (leader (var, n)))
                            else ([], state, [])
   end.



(* a-Komponente: ist eine Komponente c, bei der a in der Liste von Variablen von c vorkommt *)

(* a subgraph of g *)
Definition SubGraph (vSG v : V_set) (aSG a : A_set) (g : Graph v a) := 
  (forall (c: Component), vSG c -> v c) /\ 
  (forall (v1 v2 : Component), let ar := (A_ends v1 v2) in
                                 (aSG ar) -> (a ar /\ vSG v1 /\ vSG v2)).


Lemma TotalGraph_isa_SubGraph: forall v a g, SubGraph v v a a g.
Proof.
  intros v a g.
  unfold SubGraph.
  split.
  auto.
  intros.
  split.
  auto.
  split.
  apply (G_ina_inv1 v a g) in H.
  apply H.
  apply (G_ina_inv2 v a g) in H.
  apply H.
Qed.



Lemma SubGraph_isa_Graph : forall vSG v aSG a g, SubGraph vSG v aSG a g -> Graph vSG aSG.
Proof.
  intros vSG v aSG a g H.
  unfold SubGraph in H.
  destruct H.
  induction g.
    assert (vSG = V_empty).
    admit.
    assert (aSG = A_empty).
    admit.
    rewrite H1. rewrite H2.
    apply G_empty.
    
    apply IHg.
    intros.
    apply H in H1.
    inversion H1. inversion H2. clear H3. clear x0.
Admitted.
    
    
  

End ConnectedChecker.