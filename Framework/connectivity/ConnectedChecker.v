
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




(* This is the content of a message and consists of some key and the current local leader for that key *)
Inductive Leader_Entry := leader : (Key * nat) -> Leader_Entry.

Definition Leader_Entry_eq_dec : forall x y : Leader_Entry, {x = y} + {x <> y}.
Proof.
  decide equality.
  destruct p.
  destruct p0.
  assert (H1: {n = n0} + {n <> n0}).
  apply Nat.eq_dec.
  destruct H1.
  rewrite e.
  assert (H2: {k = k0} + {k <> k0}).
  unfold Key in *.
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



Record Localinput: Set := mk_Localinput {
(******** Eingabe des Algorithmus (x)  **********)
  Inp : list inp
}.

Record Checkerinput  := mk_Checkerinput {
(* Ausgabe des Algorithmus (y), Zeuge (w), zu pr\u00fcfende Pr\u00e4dikate *)
  output : list outp;
  certificate : list Fact;
  Local_predicates: list Predicate
}.

Inductive Input : Type :=
  | ci : Checkerinput -> Input
  | li : Localinput -> Input.

(* kann weggelassen werden? *)
Definition Output := Leader_Entry.

Record Data := mkData{
  leaders : list Leader_Entry;
  localinput : Localinput;
  checkerinput : Checkerinput;
  initialized_localinput : bool;
  initialized_checkerinput : bool;
  control_neighborlist : list Component
}.

(* all components first are their own leader for all fact_keys *)
Fixpoint init_leader_list (n:Name) (c: Certificate) :=
  match c with
  | [] => []
  | hd :: tl => (leader (fact_key hd, component_index (name_component n))) :: init_leader_list n tl
  end.

Variable initial_checker_certificate : Certificate.
Variable initial_output : list outp.
Variable initial_checker_predicates : list Predicate.

Definition init_Data (v: V_set) (a: A_set) (g: Connected v a) (n: Name) := mkData
  (init_leader_list n (certificate (mk_Checkerinput initial_output initial_checker_certificate initial_checker_predicates)))
  (mk_Localinput []) 
  (mk_Checkerinput initial_output initial_checker_certificate initial_checker_predicates)
  false 
  false 
  (neighbors v a g (name_component n)).

Definition set_leaders a v := mkData v (localinput a) (checkerinput a) (initialized_localinput a) (initialized_checkerinput a) (control_neighborlist a).
Definition set_init_li a v := mkData (leaders a) (localinput a) (checkerinput a) v (initialized_checkerinput a) (control_neighborlist a).
Definition set_init_ci a v := mkData (leaders a) (localinput a) (checkerinput a) (initialized_localinput a) v (control_neighborlist a).

Fixpoint sendlist (neighbors: list Component) (new_l: Leader_Entry): list (Name * Leader_Entry)  :=
  match neighbors with 
    | nil => []
    | hd :: tl => (Checker hd, new_l) :: (sendlist tl new_l)
  end.

(* The component sends itself as the leader for all its fact_keys to all its neighbours *)
Fixpoint initial_send_list (me : Name) cert neighbours: list (Name * Leader_Entry) :=
  match cert with
    | [] => []
    | hd :: tl => sendlist neighbours (leader (component_index (name_component me), (fact_key hd))) ++ initial_send_list me tl neighbours
  end.


(*  *)
Definition InputHandler (v: V_set) (a: A_set) (g: Connected v a)(me : Name) (c : Input) (state: Data) :
            (list Output) * Data * list (Name * Leader_Entry) := 
	match me,c  with
    (**** Initialisierung mit Localinput  ****)
    | Checker x, li locali   => if  (eqb state.(initialized_localinput) false) then
                                  ([] , (mkData (leaders state) locali (checkerinput state) true (initialized_checkerinput state) (control_neighborlist state)), [])
                                else ([], state, [])
    (**** Initialisierung mit Checkerinput und Senden der ersten Nachrichten  ****)
    | Checker x, ci checkeri => if  (eqb state.(initialized_checkerinput) false) then
                                  let myneighbours := (neighbors v a g x) in
                                  ([] , (mkData (leaders state) (localinput state) checkeri (initialized_localinput state) true (control_neighborlist state)), initial_send_list me (certificate checkeri) myneighbours)
                                else ([], state, [])
    end.

Fixpoint find_leader (k : nat) (leaders : list Leader_Entry) : option nat :=
  match leaders with
  | [] => None
  | leader (key, ind) :: tl => if beq_nat k key 
                            then Some ind
                            else find_leader k tl
  end.

Definition get_leader_index k (leaders: list Leader_Entry) : nat :=
  match (find_leader k leaders) with
  | Some x => x
  | None => 0
  end.

Fixpoint set_leader key n (ls: list Leader_Entry) : list Leader_Entry :=
  match ls with
  | [] => [leader (key, n)]
  | leader (k, ind) :: tl => if beq_nat k key 
                                 then leader (key, n) :: tl
                                 else set_leader key n tl
  end.

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
  

Lemma set_leader_sets_leader: forall key n (ls: list Leader_Entry),
    n = get_leader_index key (set_leader key n ls).
Proof.
  intros.
  induction ls.
    destruct key.
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
    destruct a.
    destruct p.
    assert (k = key \/ k <> key).
    apply classic.
    destruct H.
  
    rewrite H.
    rewrite Nat.eqb_refl.
    unfold get_leader_index.
    simpl.
    rewrite Nat.eqb_refl.
    reflexivity.

    assert(k == key = false).
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
      | leader (key, n)  => if (state.(initialized_localinput) && state.(initialized_checkerinput)) then
                              if (Nat.ltb (get_leader_index key (leaders state)) n) then (* //nur, wenn find_leader Some x zur\u00fcck gibt!! *)
                                ([], set_leaders state (set_leader key n (leaders state)), sendlist (control_neighborlist state) (leader (key, n)))
                              else ([], state, [])
                            else ([], state,[])
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
    
    
  

End ConnectedChecker.