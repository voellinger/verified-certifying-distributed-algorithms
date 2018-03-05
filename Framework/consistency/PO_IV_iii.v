
Require Import GraphBasics.Graphs.
Require Import Coq.Logic.Classical_Prop.
Require Import Verdi.Verdi.

Require Export StructTact.Fin.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Require Import Verdi.ExtrOcamlBasicExt.
Require Import Verdi.ExtrOcamlList.

Load PO_III. 

(* helping functions*)

Fixpoint remove (x : Component) (l : list Component) : list Component :=
    match l with
      | [] => []
      | y::tl => if ((Component_index x) == (Component_index y)) then tl else y::(remove x tl)
    end.

Definition empty (l : list Component) : bool :=
  match l with
  | nil => true
  | a :: m => false
  end.

(***)


Inductive Name := Checker : Component  -> Name.

(* get component from name*)
Definition name_component (n: Name): Component :=
match n with 
  | Checker x => x
end.

Definition Nodes : list Name := (map Checker (CV_list v a g)) . 

Axiom all_Names_Nodes : forall n, In n Nodes.

Axiom NoDup_Nodes : NoDup Nodes.


Definition Name_eq_dec : forall x y : Name, {x = y} + {x <> y}.
  decide equality.
  destruct c. destruct c0. 
  case (eq_nat_dec n n0); intros H.
  left; rewrite H; trivial.
  right; injection; trivial.
Qed.

Inductive Msg := Checkermessage : list Fact -> Msg.

Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
decide equality.
apply list_eq_dec.
apply fact_eq_dec. 
Qed.


Record Checkerknowledge: Set := mk_Checkerknowledge {
  Inp : list inp;
  Sub_predicates: list Predicate;
  facts: list Key
}.

Record Checkerinput  := mk_Checkerinput {
output : list outp;
certificate : list Fact
}.


Inductive Input : Type := 
  | ci : Checkerinput -> Input
  | li : Checkerknowledge -> Input.

Definition Output := Msg.



Record Data := mkData{
 queue : list Component ;
 messages_received : list Component; 
 consistent : bool ; 
 checkerresult: bool; 
 checkerinput : Checkerinput ; 
 localinput : Checkerknowledge; 
 initialized_localinput: bool;
 initialized_checkerinput: bool;
 control_neighbourlist: list Component
 }.


Definition init_Data (n: Name) := mkData
(neighbors g (name_component n)) [] true false (mk_Checkerinput [] [(fact_cons keynull valuenull)] ) (mk_Checkerknowledge []  []  []) false false (neighbors g (name_component n)).

Definition set_queue a v := mkData v  (messages_received a) (consistent a) (checkerresult a) (checkerinput a) (localinput a) (initialized_localinput a) (initialized_checkerinput a)(control_neighbourlist a) .
Definition set_consistent a v:= mkData (queue a) (messages_received a)  v (checkerresult a) (checkerinput a) (localinput a)(initialized_localinput a)(initialized_checkerinput a)(control_neighbourlist a).
Definition set_queue_consistent a q r c:= mkData q r  c (checkerresult a)(checkerinput a) (localinput a)(initialized_localinput a)(initialized_checkerinput a)(control_neighbourlist a).
Definition set_checkeroutput_queue a q r v:= mkData q r (consistent a)  v (checkerinput a) (localinput a)(initialized_localinput a)(initialized_checkerinput a)(control_neighbourlist a).



(* Send messages to all entries of a list (neighbours)*)
Fixpoint sendlist (neighbours: list Component) (me : Component)(cert: list Fact): list (Name * Msg)  :=
         match neighbours with 
              | nil => [(Checker me, Checkermessage cert)]
              | n::m => (Checker n, Checkermessage cert) :: (sendlist m me cert)
         end.



(**** 2 Inputs -> 1. Input Checkerknowledge  2. Input Checkerinput (from component) **)
Definition InputHandler (me : Name) (c : Input) (state: Data) :
            (list Output) * Data * list (Name * Msg) := 
	match me,c  with
    (**** Initialize with Checkerknowledge  **)
    | Checker x, li locali => if  (eqb state.(initialized_localinput)  false) then 
                             (* let myneighbors := (neighbors g x) in*)
                             ( [] , (mkData (queue state) [] true (checkerresult state) (checkerinput state) locali true (initialized_checkerinput state) (control_neighbourlist state)) , [])
      
                              else ([], state, [])
    (**** Initialize with Checkerinput, send message to all neighbours **)             
		| Checker x, ci checkeri => if  (eqb state.(initialized_checkerinput) false)   then 
                                let cert := checkeri.(certificate) in
                                ( [] , (mkData (queue state) [] (consistent state) (checkerresult state) checkeri (localinput state)(initialized_localinput state) true (control_neighbourlist state) ), (sendlist state.(queue) x cert)) 
                                

                                else ([], state, [])
                  
	end.


(** Check Consistency for a single fact *)
Definition One_Fact_Consistency_Check (c1 c2 : list Fact)  (key : Key) : bool := 
match (overlap c1 c2 key) with 
          | (Some x, Some y) => if (beqValue  (findValue  c1 (Some x)) (findValue  c2 (Some y))) then true else false 
          | (None, None) => false
          | (None, Some _ ) => false
          | (Some _, None ) => false
end.


(** Check Consistency for all facts in a fact list; return true if consistency is given for two certificate lists *)
Fixpoint All_Fact_Consistency_Check_ (init: bool) (c1 c2 : list Fact)  (keys : list Key) : bool := 
match keys with 
          | nil  => init 
          | a :: b => ( One_Fact_Consistency_Check c1 c2 a ) && All_Fact_Consistency_Check_ init c1 c2 b
end.

Functional Scheme all_fact_ind := Induction for All_Fact_Consistency_Check_  Sort Prop.

(** Initialize Consistency Check with true - Consistency Check for an empty list of facts returns true as well *)
Definition All_Fact_Consistency_Check := All_Fact_Consistency_Check_ true.

(*stub-function for next phase of checker, e.g. decide sub-predicates*)
Variable Check : Checkerknowledge -> Checkerinput -> bool.

Definition NetHandler (me : Name) (src: Name) (m : Msg) (state: Data) : 
    (list Output) * Data * list (Name * Msg) :=
    
  
   (****  Consistency Check **)
    match m with
      | Checkermessage certif => if  (state.(initialized_localinput) && state.(initialized_checkerinput)) then

                                     let c := state.(checkerinput) in 
                                     let l := state.(localinput) in
                                     let mycertif := c.(certificate) in
                                     let consistent := state.(consistent) && All_Fact_Consistency_Check mycertif certif l.(facts) in
                                      
                                       if (empty (remove (name_component src) state.(queue)) && (eqb consistent true)) then
                                            let result := Check state.(localinput) state.(checkerinput) in (** check () **) 
     	                                      ([], (set_checkeroutput_queue state (remove  (name_component src) state.(queue)) ([(name_component src)] ++ state.(messages_received)) result) , []) (** finales Resultat **)
                                       else ([], (set_queue_consistent state  (remove  (name_component src) state.(queue)) ([(name_component src)] ++ state.(messages_received))  consistent), [])       
                                 else ([], state,[])
   end.



(* verdi stuff*)

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
    nodes := Nodes;
    all_names_nodes := all_Names_Nodes;
    no_dup_nodes := NoDup_Nodes;
    init_handlers := init_Data; 
    input_handlers := InputHandler ;
    net_handlers := NetHandler
    
    }.

(** helping functions for verification **)

(* get certificate in message *)
Definition certificate_from_message ( msg: Msg) :  list Fact :=
match msg with 
  | Checkermessage certif => certif
end. 

Definition initialized (state: Data) :=
(state.(initialized_localinput) && state.(initialized_checkerinput)).

(* If one fact consistency check returns true for x y na, then we have fact consistency for x y na *)
Lemma One_Fact_Consistency_Check_true:
forall cert1 cert2 key, One_Fact_Consistency_Check cert1 cert2 key = true -> consistent_in_var cert1 cert2 key.
Proof.
intros.
unfold One_Fact_Consistency_Check in *.
unfold consistent_in_var.
repeat break_match.
intros.
inversion H0.
apply beqValue_eq in Heqb.
trivial.
discriminate.
discriminate.
discriminate.
discriminate.
Qed.

(* helping lemma *)
Lemma Consistency_Check_List:
forall a c1 c2 keys, (forall k, In k (a :: keys) -> One_Fact_Consistency_Check c1 c2 k = true) -> (forall m : Key, In m keys -> One_Fact_Consistency_Check c1 c2 m = true ).
Proof.
intros.
apply in_cons with (a:=a0) in H0.
apply H in H0.
trivial.
Qed.

(* If one fact consistency check returns true for x y and all facts in fact list, then All_Fact_Consistency Check returns true for x y and fact list*)
Lemma one_fact_all_fact :
forall c1 c2 keys, (forall k,  In k keys ->  One_Fact_Consistency_Check c1 c2 k = true) -> All_Fact_Consistency_Check c1 c2 keys = true.
Proof.
intros.
unfold All_Fact_Consistency_Check.
induction keys.
unfold All_Fact_Consistency_Check_.
trivial.
unfold All_Fact_Consistency_Check_.
apply andb_true_iff.
split.
apply H with (k:=a0).
apply in_eq.
fold All_Fact_Consistency_Check_.
apply IHkeys.
intros.
apply Consistency_Check_List with (a:=a0) (keys :=keys).
apply H .
trivial.
Qed.

Lemma both_one_fact_all_fact :
forall c1 c2 keys, All_Fact_Consistency_Check c1 c2 keys = true -> (forall k,  In k keys ->  One_Fact_Consistency_Check c1 c2 k = true)  .
Proof.
intros.
unfold All_Fact_Consistency_Check in *.
unfold All_Fact_Consistency_Check_ in *.
induction keys.
unfold One_Fact_Consistency_Check.
  repeat break_match; repeat tuple_inversion;
      subst; simpl in *; subst; simpl in *.
trivial.
exfalso.
trivial.
exfalso.
trivial.
exfalso.
trivial.
exfalso.
trivial.

fold All_Fact_Consistency_Check_ in *.
apply andb_true_iff in H.
destruct H.
destruct H0.
rewrite H0 in H.
trivial.
apply IHkeys.
auto.
auto.
Qed.

Variable localin : Checkerknowledge.


Lemma both_one_fact_all_fact_allna :
forall c1 c2, All_Fact_Consistency_Check c1 c2 localin.(facts) = true -> 
(forall k,  In k localin.(facts) ->  One_Fact_Consistency_Check c1 c2 k = true)  .
Proof.
intros.
apply both_one_fact_all_fact with (keys:=localin.(facts)).
trivial.
trivial.
Qed.

Definition keylist (a : list Fact) : list Key :=   map fact_key a.

Variable all_Keys: list Key.
Axiom all_in_all_Keys:
forall key: Key , In key all_Keys.


Axiom keylistprop: forall k cert1 n,  get_pos cert1 k = Some n -> In k (keylist cert1).

Axiom allkeylist: forall k cert1 , In k (facts localin) <-> In k (keylist cert1).

Lemma inkeylist:
forall cert1 cert2 k, overlapping_in_var cert1 cert2 k -> In k (keylist cert1).
Proof.
intros.
unfold overlapping_in_var in *.
unfold overlap in *.
repeat break_match. 
apply keylistprop in Heqo; trivial.
destruct H. destruct H. discriminate.
destruct H. destruct H.  discriminate.
destruct H. destruct H.  discriminate.
Qed.

Lemma All_Fact_Consistency_Check_for_true:
forall cert1 cert2 , All_Fact_Consistency_Check cert1 cert2 localin.(facts) = true -> consistent_in_all_var cert1 cert2.
Proof.
intros.
apply consistency_defs.
unfold consistent_alt.
intros.
apply both_one_fact_all_fact_allna with (k:=k) in H.
unfold overlapping_in_var in H0.
apply One_Fact_Consistency_Check_true in H.
unfold consistent_in_var in H.
unfold overlap in *.
repeat break_match.
destruct H0. destruct H0.
assert (G:=H0). apply H in H0. inversion G. rewrite <- H2. rewrite <-  H3. trivial.
destruct H0. destruct H0. discriminate. 
destruct H0. destruct H0. discriminate. 
destruct H0. destruct H0. discriminate. 
trivial.
apply inkeylist in H0.
apply allkeylist in H0.
trivial.
Qed.




(************************ FOR ALL IN MESSAGES RECEIVED -> ALL FACT CONSISTENCY ********************)



Lemma inititialized_nethandler_b:
forall me src msg data u dataout st', 
NetHandler me src msg data = (u, dataout, st') ->
initialized dataout = true -> initialized data = true.
Proof.
intros.
unfold NetHandler in *.
repeat break_match.
inversion H.
unfold initialized.
trivial.
trivial.
inversion H.
trivial.
Qed.

Lemma inititialized_nethandler_:
forall me src msg data u dataout st', 
NetHandler me src msg data = (u, dataout, st') ->
initialized_localinput data &&
initialized_checkerinput data  = true ->
initialized_checkerinput dataout = true.
Proof.
intros.
unfold NetHandler in *.
repeat break_match.
unfold set_checkeroutput_queue in H.
find_inversion. simpl in *. 
apply andb_true_iff in Heqb.
destruct Heqb.
trivial.
find_inversion. simpl in *. 
apply andb_true_iff in Heqb.
destruct Heqb.
trivial.
discriminate.
Qed.

Lemma inititialized_nethandler_2:
forall me src msg data u dataout st', 
NetHandler me src msg data = (u, dataout, st') ->
initialized_localinput data &&
initialized_checkerinput data  = true ->
initialized_localinput dataout = true.
Proof.
intros.
unfold NetHandler in *.
repeat break_match.
unfold set_checkeroutput_queue in H.
find_inversion. simpl in *. 
apply andb_true_iff in Heqb.
destruct Heqb.
trivial.
find_inversion. simpl in *. 
apply andb_true_iff in Heqb.
destruct Heqb.
trivial.
discriminate.
Qed.

Lemma consistent_nethandler_b:
forall me src msg data u dataout st', 
NetHandler me src msg data = (u, dataout, st') ->
consistent dataout = true -> consistent data = true.
Proof.
intros.
unfold NetHandler in *.
repeat break_match.
unfold set_checkeroutput_queue in H.
find_inversion. simpl in *. trivial.
find_inversion. simpl in *. apply andb_true_iff in H0.
destruct H0. trivial.
inversion H.
trivial.
Qed.

Lemma consistent_inputhandler_b:
forall me input data u dataout l , 
InputHandler me input data = (u, dataout, l) ->
initialized data = true -> 
consistent dataout = true -> consistent data = true.
Proof.
intros.
unfold InputHandler in *.
repeat break_match.
find_inversion. simpl in *. trivial.
find_inversion. trivial.
find_inversion. simpl in *. unfold initialized in H0.
apply andb_true_iff in H0. destruct H0.
apply eqb_prop in Heqb. rewrite H in Heqb. discriminate.
find_inversion. trivial.
Qed.


Lemma initialized_inputhandler_b:
forall me input data u dataout l , 
InputHandler me input data = (u, dataout, l) ->
messages_received dataout <> [] -> 
initialized dataout = true -> initialized data = true.
Proof.
intros.
unfold InputHandler in *.
repeat break_match.
find_inversion. simpl in *. contradiction.

find_inversion. trivial.
find_inversion. simpl in *. contradiction.
find_inversion. trivial.
Qed.


Axiom certificate_from_src :
forall l me src msg data u dataout st', 
NetHandler me src msg data = (u, dataout, st') ->
msg = Checkermessage l ->
getCertificate (name_component src) =  l.

Lemma consistency_check_in_src :
forall me src msg data u dataout st', 
initialized data = true -> 
NetHandler me src msg data = (u, dataout, st') ->
dataout.(consistent) = true -> 
All_Fact_Consistency_Check data.(checkerinput).(certificate) (getCertificate (name_component src))  data.(localinput).(facts) = true.
Proof.
intros.
assert (G:=H0).
unfold NetHandler in H0.
repeat break_match.
- apply andb_true_iff in Heqb0.
destruct Heqb0.
apply eqb_prop in H3.

rewrite  certificate_from_src with (data:=data)(me:=me)(src:=src)(msg:=msg)(u:=u)(dataout:=dataout)(st':=st')(l:=l).
trivial.
apply andb_true_iff  in H3.
destruct H3.
trivial.
trivial.
rewrite Heqm.
trivial.
trivial.
-
rewrite  certificate_from_src with (data:=data)(me:=me)(src:=src)(msg:=msg)(u:=u)(dataout:=dataout)(st':=st')(l:=l).
find_inversion. simpl in *. subst. 
apply andb_true_iff  in H1.
destruct H1.
trivial.
rewrite Heqm.
trivial.
trivial.
- unfold initialized in H.
rewrite H in Heqb. 
discriminate.
Qed.

Lemma consistency_check_NetHandler :
forall me src msg data u dataout st', 
initialized dataout = true -> 
dataout.(consistent) = true ->
NetHandler me src msg data = (u, dataout, st') ->
forall k, 
(In k data.(messages_received)  -> 
All_Fact_Consistency_Check data.(checkerinput).(certificate) (getCertificate  k)  data.(localinput).(facts) = true) ->
(In k dataout.(messages_received) -> 
All_Fact_Consistency_Check data.(checkerinput).(certificate) (getCertificate  k)  data.(localinput).(facts) = true).
Proof.
intros.
assert (G:=H0).
assert (N:=H1).
unfold NetHandler in H1.
repeat break_match.
- apply andb_true_iff in Heqb0.
destruct Heqb0.
apply eqb_prop in H5.
apply andb_true_iff in H5.
inversion H1. simpl in *.
unfold set_checkeroutput_queue in H8.
find_inversion. simpl in *. subst.
destruct H3.
rewrite <- H1.
apply consistency_check_in_src with  (me:=me)(src:=src)(msg:=Checkermessage l)(u:=[])(dataout:= {|
    queue := remove (name_component src) (queue data);
    messages_received := name_component src :: messages_received data;
    consistent := consistent data;
    checkerresult := Check (localinput data) (checkerinput data);
    checkerinput := checkerinput data;
    localinput := localinput data;
    initialized_localinput := initialized_localinput data;
    initialized_checkerinput := initialized_checkerinput data;
    control_neighbourlist := control_neighbourlist data
  |})(st':=[]).
    unfold initialized.
    trivial.
    unfold NetHandler.  
    apply N.
    simpl in *.
    destruct H5.
    trivial.
    apply H2.
    trivial.
   - apply andb_false_iff in Heqb0.
     destruct Heqb0.
     unfold set_queue_consistent in H1.
     find_inversion. simpl in *. subst.
     destruct H3.
     rewrite <- H1.
    apply consistency_check_in_src with  (me:=me)(src:=src)(msg:=Checkermessage l)(u:=[])(dataout:= {|
      queue := remove (name_component src) (queue data);
      messages_received := name_component src :: messages_received data;
      consistent := consistent data &&
                    All_Fact_Consistency_Check
                      (certificate (checkerinput data)) l
                      (facts (localinput data));
      checkerresult := checkerresult data;
      checkerinput := checkerinput data;
      localinput := localinput data;
      initialized_localinput := initialized_localinput data;
      initialized_checkerinput := initialized_checkerinput data;
      control_neighbourlist := control_neighbourlist data |} )(st':=[]).
    unfold initialized.
    trivial.
     unfold NetHandler.  
    apply N.
    simpl in *.
    apply G.
    apply H2. 
    trivial.
    inversion H1. simpl in *. subst.
    unfold set_queue_consistent in G. simpl in *.
    apply eqb_false_iff  in H4.
    contradiction.
   -apply inititialized_nethandler_b with (me:=me)(src:=src) (msg:=msg) (data:=data) (dataout:=dataout) (st':=st') (u:=u) in H.
    unfold initialized in H.
    rewrite H in Heqb.
    discriminate.
    rewrite Heqm.
    trivial.
Qed.

Lemma facts_nethandler:
forall me src msg data u dataout st', 
NetHandler me src msg data = (u, dataout, st') ->
initialized dataout = true -> 
facts (localinput (data)) = facts (localinput (dataout)).
Proof.
intros.
unfold NetHandler in *.
repeat break_match.
find_inversion. simpl in *. reflexivity.
find_inversion. simpl in *. reflexivity.
find_inversion. simpl in *. reflexivity.
Qed.

Lemma certificate_nethandler:
forall me src msg data u dataout st', 
NetHandler me src msg data = (u, dataout, st') ->
initialized dataout = true -> 
(certificate (checkerinput data )) = (certificate (checkerinput dataout)).
Proof.
intros.
unfold NetHandler in *.
repeat break_match.
find_inversion; simpl in *; reflexivity.
find_inversion; simpl in *; reflexivity.
find_inversion; simpl in *; reflexivity.
Qed.
 

Lemma certificate_inputhandler:
forall me input data u dataout l, 
InputHandler me input data = (u, dataout, l) ->
messages_received dataout <> [] -> 
(certificate (checkerinput data )) = (certificate (checkerinput dataout)).
Proof.
intros.
unfold InputHandler in *.
repeat break_match.
find_inversion. simpl in *. contradiction.
find_inversion. trivial. 
find_inversion. simpl in *. contradiction.
find_inversion. trivial. 
Qed.

Lemma facts_inputhandler:
forall me input data u dataout l, 
InputHandler me input data = (u, dataout, l) ->
messages_received dataout <> [] -> 
facts (localinput (data)) = facts (localinput (dataout)).
Proof.
intros.
unfold InputHandler in *.
repeat break_match.
find_inversion. simpl in *. contradiction.
find_inversion. trivial. 
find_inversion. simpl in *. contradiction.
find_inversion. trivial.
Qed. 

Lemma consistency_check_Inputhandler :
forall me input data u dataout l, 
InputHandler me input data = (u, dataout, l) ->
messages_received dataout <> []  -> 
dataout.(consistent) = true ->
forall k, 
(In k data.(messages_received)  -> 
All_Fact_Consistency_Check data.(checkerinput).(certificate) (getCertificate  k)  data.(localinput).(facts) = true) ->
(In k dataout.(messages_received) -> 
All_Fact_Consistency_Check dataout.(checkerinput).(certificate) (getCertificate  k)  dataout.(localinput).(facts) = true).
Proof.
intros.
assert (G:=H).
assert (I:=H).
unfold InputHandler in H.
repeat break_match.
assert (K:=H0).

apply facts_inputhandler with (me:=me) (input:=input) (data:=data) (u:=u) (dataout:=dataout) (l:=l) in H0.
rewrite <- H0.
apply certificate_inputhandler with (me:=me) (input:=input) (data:=data) (u:=u) (dataout:=dataout) (l:=l) in K.
rewrite <- K.
apply H2.
find_inversion. simpl in *. subst.
trivial.
exfalso. trivial.
rewrite Heqi.
rewrite Heqn.
trivial.
rewrite Heqn.
rewrite Heqi.
trivial.

assert (K:=H0).
apply facts_inputhandler with (me:=me) (input:=input) (data:=data) (u:=u) (dataout:=dataout) (l:=l) in H0.
rewrite <- H0.
apply certificate_inputhandler with (me:=me) (input:=input) (data:=data) (u:=u) (dataout:=dataout) (l:=l) in K.
rewrite <- K.
apply H2.
find_inversion. simpl in *. subst.
trivial.
rewrite Heqn.
rewrite Heqi.
trivial.
rewrite Heqn.
rewrite Heqi.
trivial.

find_inversion. simpl in *. exfalso. trivial.


assert (K:=H0).
apply facts_inputhandler with (me:=me) (input:=input) (data:=data) (u:=u) (dataout:=dataout) (l:=l) in H0.
rewrite <- H0.
apply certificate_inputhandler with (me:=me) (input:=input) (data:=data) (u:=u) (dataout:=dataout) (l:=l) in K.
rewrite <- K.
apply H2.
find_inversion. simpl in *. subst.
trivial.
rewrite Heqn.
rewrite Heqi.
trivial.
rewrite Heqn.
rewrite Heqi.
trivial.
Qed.

Lemma notEmptylist:
forall (clist : list Component), clist <> [] -> exists (m:Component), In m clist.
Proof.
intros.
destruct clist.
contradiction.
exists c.
apply  in_eq .
Qed.



Lemma notEmptylist_b:
forall (clist : list Component) m, In m clist -> clist <> [].
Proof.
intros.
destruct clist.
contradiction.
apply not_eq_sym.
apply nil_cons.
Qed.





Lemma All_Fact_Consistency_Check_Network:
forall  net tr,
step_async_star (params := Checker_MultiParams) step_async_init net tr ->
forall component c,
(nwState net (Checker c)).(initialized)  = true -> 
(nwState net (Checker c)).(consistent)  = true -> 
(In component (nwState net (Checker c)).(messages_received) ->
All_Fact_Consistency_Check  (nwState net (Checker c)).(checkerinput).(certificate) (getCertificate  component)  (nwState net (Checker c)).(localinput).(facts) = true).
Proof.
intros net tr H .
remember step_async_init as y in *.
induction H using refl_trans_1n_trace_n1_ind. intros. subst.
simpl in *.
exfalso.
trivial.
intros.
invc H0.

- destruct p. destruct pDst. unfold nwState in *. unfold update in *. repeat break_match. 
+  unfold net_handlers in *. unfold Checker_MultiParams in *. simpl in *.
assert (J:=H3).

apply consistency_check_NetHandler with (me :=(Checker c0)) (src:=pSrc)(u:=out) (st':=l) (k:=component) (data:=(nwState (Checker c0))) (msg:= pBody ) (dataout:=d)  in H3.
rewrite <- certificate_nethandler with (me :=(Checker c0)) (src:=pSrc)(u:=out) (st':=l) (data:=(nwState (Checker c0))) (msg:= pBody ) (dataout:=d).
rewrite <- facts_nethandler with (me :=(Checker c0)) (src:=pSrc)(u:=out) (st':=l) (data:=(nwState (Checker c0))) (msg:= pBody ) (dataout:=d).
apply H3.
trivial.
trivial.
trivial.
trivial.
trivial.
trivial.
apply IHrefl_trans_1n_trace1  with (c:=c0).
trivial.
apply consistent_nethandler_b  with (me :=(Checker c0)) (src:=pSrc)(u:=out) (st':=l)(data:=(nwState (Checker c0))) (msg:= pBody ) (dataout:=d)  in H3.
apply inititialized_nethandler_b  with (me :=(Checker c0)) (src:=pSrc)(u:=out) (st':=l)(data:=(nwState (Checker c0))) (msg:= pBody ) (dataout:=d)  in H2.
trivial.
trivial.
trivial.
apply consistent_nethandler_b  with (me :=(Checker c0)) (src:=pSrc)(u:=out) (st':=l)(data:=(nwState (Checker c0))) (msg:= pBody ) (dataout:=d)  in H3.
trivial.
trivial.
trivial.
+
concludes. apply IHrefl_trans_1n_trace1. trivial. trivial. trivial.
-destruct h. unfold nwState in *. unfold update in *. repeat break_match.
+  unfold input_handlers in *. unfold Checker_MultiParams in *. concludes.
apply consistency_check_Inputhandler with (k:=component) in H5 .
trivial.
assert (G:=H4).
apply notEmptylist_b in H4.
trivial.
trivial.
apply IHrefl_trans_1n_trace1 with (c:=c0).
apply initialized_inputhandler_b in H5.
trivial.
apply notEmptylist_b in H4.
trivial.
trivial.
apply consistent_inputhandler_b in H5.
trivial.
apply initialized_inputhandler_b in H5.
trivial.
apply notEmptylist_b in H4.
trivial.
trivial.
trivial.
trivial.
+ concludes. apply IHrefl_trans_1n_trace1. trivial. trivial. trivial.
Qed.


Axiom all_keys_in_nw:
forall  net tr c,
step_async_star (params := Checker_MultiParams) step_async_init net tr ->
facts (localinput (nwState net (Checker c))) = localin.(facts).

Lemma All_Fact_Check_Network:
forall  net tr,
step_async_star (params := Checker_MultiParams) step_async_init net tr ->
forall component c,
(nwState net (Checker c)).(initialized)  = true -> 
(nwState net (Checker c)).(consistent)  = true -> 
(In component (nwState net (Checker c)).(messages_received)) ->
consistent_in_all_var (nwState net (Checker c)).(checkerinput).(certificate) (getCertificate  component) .
Proof.
intros.
apply All_Fact_Consistency_Check_for_true.
rewrite <- all_keys_in_nw with (net:=net) (tr:=tr) (c:=c).
apply All_Fact_Consistency_Check_Network with (net:=net) (c:=c) (tr:=tr) (component:=component);trivial.
trivial.
Qed.

(********************************* QUEUE EMPTY -> ALL IN MESSAGES RECEIVED ***************************************************************)

Lemma removeprop:
forall name k l1 l2,
 In k (l1 ++ l2) ->
 In k   (remove (name_component name) l1 ++  name_component name :: l2).
Proof.
intros. 
apply in_app_or in H.
destruct H.
apply in_or_app.
- assert ({k= name_component name} + {k <> name_component name}) .
  destruct name.
  destruct k.
  destruct Checker.
  destruct name_component.
  destruct index.
  apply V_eq_dec with (x:= index n1) (y:=index n0).
destruct H0.
right.
rewrite e.
apply in_eq .
left.
induction l1; auto.
destruct H. 
rewrite H. 
unfold remove. 
repeat break_match.
apply beq_nat_true in Heqb.
unfold Component_index in Heqb.
repeat break_match.
rewrite Heqb in n.
contradiction.
simpl.
left.
reflexivity.
unfold remove.
repeat break_match. 
trivial.
fold remove.
unfold In.
right.
unfold In in IHl1.
apply IHl1.
unfold In in H.
trivial.
- apply in_or_app.
right.
apply in_cons with (a:=name_component name) in H.
trivial.
Qed.


Lemma allincontrol_queue_messagesreceived_nethandler:
forall me src msg data u dataout st' k, 
NetHandler me src msg data = (u, dataout, st') ->
(In k (control_neighbourlist data) -> In k ((queue data ) ++ (messages_received data))) ->
(In k (control_neighbourlist dataout) -> In k ( ( queue dataout ) ++ (messages_received dataout))).  
Proof.
intros.
unfold NetHandler in *.
repeat break_match. inversion H.
unfold set_checkeroutput_queue in * .
find_inversion. simpl in *.
apply removeprop with (l1:=queue data) (l2:=messages_received data) (k:=k) (name:=src).


apply H0.
trivial.
intros.
find_inversion.
unfold set_queue_consistent.
simpl in *.
apply removeprop with (l1:=queue data) (l2:=messages_received data) (k:=k) (name:=src).
apply H0.
trivial.
intros.

unfold NetHandler in *.
repeat break_match. inversion H.
unfold set_checkeroutput_queue in * .
find_inversion. apply H0.
trivial.
Qed.


Lemma initialized_false__prop_nethandler_b:
forall me src msg data u dataout st' , 
NetHandler me src msg data = (u, dataout, st') ->
dataout.(initialized_checkerinput) = false -> 
data.(initialized_checkerinput) = false.
Proof.
intros.
unfold NetHandler in *.
repeat break_match.
apply andb_true_iff in Heqb. destruct Heqb. unfold set_checkeroutput_queue. find_inversion. simpl in *.
rewrite  H0 in H2. discriminate.
unfold  set_queue_consistent . find_inversion. simpl in *.
apply andb_true_iff in Heqb. destruct Heqb. rewrite H0 in H1. discriminate.
find_inversion. trivial.
Qed.

Lemma initialized_false_network_nethandler:
forall me src msg data u dataout st' , 
NetHandler me src msg data = (u, dataout, st') ->
data.(initialized_checkerinput) = false -> 
data.(queue) = data.(control_neighbourlist) -> 
dataout.(queue) = dataout.(control_neighbourlist).
Proof.
intros.
assert (G:=H).
unfold NetHandler in *.
repeat break_match.
apply andb_true_iff in Heqb. destruct Heqb. unfold set_checkeroutput_queue. find_inversion. simpl in *. rewrite H0 in H3. discriminate.
apply andb_true_iff in Heqb. destruct Heqb. rewrite H0 in H3. discriminate.
find_inversion. trivial.
Qed.

Lemma initialized_false_network:
forall  net tr ,
step_async_star (params := Checker_MultiParams) step_async_init net tr ->
forall c, 
(nwState net (Checker c)).(initialized_checkerinput) = false -> 
(nwState net (Checker c)).(queue) = (nwState net (Checker c)).(control_neighbourlist).
Proof.
  intros net tr  H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind. intros. subst. reflexivity.
  invc H0. 
  - intros.  destruct p. destruct pDst. unfold nwState in *. unfold update in *. repeat break_match.
  +  unfold net_handlers in *. unfold Checker_MultiParams in *. simpl in *.
     apply initialized_false_network_nethandler in H3. trivial. 
     apply initialized_false__prop_nethandler_b with (msg:=pBody) (src:=pSrc) (data:=(nwState (Checker c0))) (me:=(Checker c0)) (dataout:=d) (u:=out) (st':=l) in H3. trivial. trivial.
     concludes. apply IHrefl_trans_1n_trace1  with (c:=c0). apply initialized_false__prop_nethandler_b with (msg:=pBody) (src:=pSrc) (data:=(nwState (Checker c0))) (me:=(Checker c0)) (dataout:=d) (u:=out) (st':=l) in H3. trivial. trivial.
  +  concludes. apply IHrefl_trans_1n_trace1. trivial.
  - intros. destruct h. unfold nwState in *. unfold update in *. repeat break_match.
  *   unfold input_handlers in *. unfold Checker_MultiParams in *. concludes.
  intros.
  unfold InputHandler in *.
  repeat break_match. 
  find_inversion. simpl in *. discriminate.
  find_inversion. apply IHrefl_trans_1n_trace1  with (c:=c0). trivial.
   find_inversion. simpl in *.  apply IHrefl_trans_1n_trace1  with (c:=c0). trivial. find_inversion. apply IHrefl_trans_1n_trace1  with (c:=c0). trivial.
 *  apply IHrefl_trans_1n_trace1. trivial. trivial.
Qed.

Lemma messages_received_not_empty_nethandler:
forall  net tr,
step_async_star (params := Checker_MultiParams) step_async_init net tr ->
forall c, 
(nwState net (Checker c)).(initialized_checkerinput) = false -> 
(nwState net (Checker c)).(queue) = (nwState net (Checker c)).(control_neighbourlist).
Proof.
  intros net tr  H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind. intros. subst. reflexivity.
  invc H0. 

  - intros. destruct (pDst p) eqn:?. unfold nwState in *. unfold update in *. repeat break_match.
  + 
     unfold net_handlers in *. unfold Checker_MultiParams in *. assert (K:=H3). unfold NetHandler in H3. concludes.
     repeat break_match.
   apply inititialized_nethandler_ in K.  rewrite K in H0. discriminate. trivial.
   apply inititialized_nethandler_ in K.  rewrite K in H0. discriminate. trivial.
     find_inversion. apply IHrefl_trans_1n_trace1.  trivial.
  + apply IHrefl_trans_1n_trace1. trivial. trivial.
   - intros. destruct h. unfold nwState in *. unfold update in *. repeat break_match.

  *   unfold input_handlers in *. unfold Checker_MultiParams in *. concludes.  unfold InputHandler in *.
  repeat break_match. 
  find_inversion. simpl in *. discriminate.
  find_inversion. apply IHrefl_trans_1n_trace1  with (c:=c0). trivial.
   find_inversion. simpl in *. trivial.
  find_inversion. apply IHrefl_trans_1n_trace1  with (c:=c0). trivial.
  find_inversion. apply IHrefl_trans_1n_trace1  with (c:=c0). trivial.
 *  apply IHrefl_trans_1n_trace1. trivial. trivial.
Qed.

Lemma messages_received_not_empty_nethandler2:
forall  net tr,
step_async_star (params := Checker_MultiParams) step_async_init net tr ->
forall c, 
(nwState net (Checker c)).(initialized_localinput) = false -> 
(nwState net (Checker c)).(queue) = (nwState net (Checker c)).(control_neighbourlist).
Proof.
  intros net tr  H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind. intros. subst. reflexivity.
  invc H0. 
 - intros. destruct (pDst p) eqn:?. unfold nwState in *. unfold update in *. repeat break_match.
     unfold net_handlers in *. unfold Checker_MultiParams in *. assert (K:=H3). unfold NetHandler in H3. concludes.
     repeat break_match.
     apply inititialized_nethandler_2 in K. rewrite K in H0. discriminate. trivial.
     apply inititialized_nethandler_2 in K.  rewrite K in H0. discriminate. trivial.
         find_inversion. apply IHrefl_trans_1n_trace1.  trivial.
      apply IHrefl_trans_1n_trace1. trivial. trivial. 
 -  intros. destruct h. unfold nwState in *. unfold update in *. repeat break_match.
 * unfold input_handlers in *. unfold Checker_MultiParams in *. concludes. unfold InputHandler in *. repeat break_match. 
  find_inversion. simpl in *.  apply IHrefl_trans_1n_trace1 with (c:=c0); trivial.
  find_inversion. apply IHrefl_trans_1n_trace1  with (c:=c0). trivial.
  find_inversion.  simpl in *. apply IHrefl_trans_1n_trace1  with (c:=c0). apply eqb_prop in Heqb. discriminate.
  find_inversion. apply IHrefl_trans_1n_trace1  with (c:=c0). trivial.
 *  apply IHrefl_trans_1n_trace1. trivial. trivial.
Qed.



Lemma queue_message_received_equals_controllist:
forall  net tr,
step_async_star (params := Checker_MultiParams) step_async_init net tr ->
forall k c,
In k (nwState net (Checker c)).(control_neighbourlist) -> 
In k ( (nwState net (Checker c)).(queue) ++ (nwState net (Checker c)).(messages_received)). 
Proof.
intros net tr H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind. intros. subst. unfold step_async_init in *. unfold nwState in *. unfold init_handlers in *. unfold Checker_MultiParams in *. unfold init_Data in *. simpl in *. trivial. rewrite app_nil_r. trivial.
- invc H0.
+ destruct (pDst p) eqn:?.  unfold nwState in *. unfold update in *. intros. repeat break_match.
  unfold net_handlers in *. unfold Checker_MultiParams in *. concludes.
  apply allincontrol_queue_messagesreceived_nethandler with
  (st':=l)(u:=out) (k :=k)(me:= (pDst p)) (src:=(pSrc p)) (msg:= (pBody p) )(data:= (nwState (Checker c)) ) (dataout:=d) in H3.
  trivial.
  apply IHrefl_trans_1n_trace1 with (k:=k) (c:=c).
  simpl in *.
  trivial.
  apply IHrefl_trans_1n_trace1 with (k:=k) (c:=c0); trivial.
+ intros. destruct h. unfold nwState in *. unfold update in *. repeat break_match.
* 
  unfold input_handlers in *. unfold Checker_MultiParams in *. concludes.
  intros.
  unfold InputHandler in *.   repeat break_match.  find_inversion. intros. simpl in *. rewrite app_nil_r. 
  apply eqb_prop in Heqb.
  apply messages_received_not_empty_nethandler with (c:=c) in H. simpl in *. 
  rewrite <- e. rewrite H. rewrite <-  e in H0. trivial. simpl in *. rewrite  e. trivial. 
  intros. find_inversion. apply IHrefl_trans_1n_trace1 with (c:=c0). trivial.
  intros. find_inversion. simpl in *.  rewrite app_nil_r.   apply eqb_prop in Heqb. 
  apply messages_received_not_empty_nethandler2 with (c:=c0) in H. simpl in *. rewrite H. trivial. simpl in *. trivial.
  find_inversion.  apply IHrefl_trans_1n_trace1 with (c:=c0). trivial. (*apply IHrefl_trans_1n_trace1 with (c:=c0). trivial.*)
* intros.  apply IHrefl_trans_1n_trace1 . trivial. trivial. 
Qed.
    



Lemma queue_empty_message_received_equals_controllist:
forall  net tr,
step_async_star (params := Checker_MultiParams) step_async_init net tr ->
forall k c,
(nwState net (Checker c)).(queue) = [] -> 
In k (nwState net (Checker c)).(control_neighbourlist) ->
In k  (nwState net (Checker c)).(messages_received).
Proof.
intros.
apply queue_message_received_equals_controllist with (k:=k) (c:=c) in H.
rewrite  H0 in H.
auto.
trivial.
Qed.

(***************** ALL IN CONTROLL LIST ARE NEIGHBOURS *******************)


Lemma neighbours_controllist_nethandler:
forall me src msg data u dataout st' k, 
NetHandler me src msg data = (u, dataout, st') ->
(In k (neighbors g (name_component me) ) ->
In k (control_neighbourlist data))  -> 
( In k (neighbors g (name_component me)) ->
In k (control_neighbourlist dataout )).
Proof.
intros.
assert (K:=H).
unfold NetHandler in *.
repeat break_match.
unfold set_checkeroutput_queue in *.
inversion H.
simpl in *.
apply  andb_true_iff in Heqb.
destruct Heqb.
apply H0.
trivial.
inversion H.
simpl in *.
trivial.
unfold set_queue_consistent.
inversion H.
simpl in *.
apply H0.
trivial.
inversion H.
rewrite <- H4.
apply H0.
trivial.
Qed.


Lemma local_input_Inputhandler :
forall me  data u input dataout l, 
InputHandler me input data = (u, dataout, l) ->
forall k,
( In k (neighbors g  (name_component me)) ->
In k data.(control_neighbourlist)) ->
(In k (neighbors g  (name_component me)) ->
In k dataout.(control_neighbourlist)).
Proof.
intros.
unfold InputHandler in *.
repeat break_match.
find_inversion; simpl in *.
apply H0;trivial.
find_inversion; simpl in *.  apply H0;trivial.
find_inversion; simpl in *.  apply H0;trivial. 
find_inversion; simpl in *.  apply H0;trivial. 
Qed.


Lemma neighbours_in_controllist:
forall  net tr ,
step_async_star (params := Checker_MultiParams) step_async_init net tr ->
forall c k,
In k (neighbors g c) ->
In k (nwState net (Checker c)).(control_neighbourlist).
Proof. 
intros net tr H.
  remember step_async_init as y in *.
  induction H using refl_trans_1n_trace_n1_ind. intros. subst. unfold initialized in *. unfold step_async_init in *. unfold nwState in *. unfold init_handlers in *. unfold Checker_MultiParams in *. unfold init_Data in *. simpl in *. trivial.
  (*step*)
   invc H0.
  
  (*NetHandler*)
  +
  intros. destruct (pDst p) eqn:?. unfold nwState in *. unfold update in *. repeat break_match.
 -   unfold net_handlers in *. unfold Checker_MultiParams in *.
     apply neighbours_controllist_nethandler with (k:=k) in H3. trivial. intros. apply IHrefl_trans_1n_trace1. trivial. trivial. rewrite <- e.  unfold name_component. trivial.
  -   apply IHrefl_trans_1n_trace1; trivial. 
 (*InputHandler*)
  +   intros. destruct h. unfold nwState in *. unfold update in *. repeat break_match.
  *   unfold input_handlers in *. unfold Checker_MultiParams in *. concludes.   assert (G:=H2). unfold InputHandler in H2.  repeat break_match.

   apply local_input_Inputhandler with (k:=k) in G. trivial.  intros. apply IHrefl_trans_1n_trace1.  inversion e. rewrite <- H5. trivial. rewrite <- e.  unfold name_component. trivial.

    find_inversion.  simpl in *.  apply IHrefl_trans_1n_trace1 . trivial.  inversion e. rewrite <- H3. trivial.
       find_inversion.  simpl in *. inversion e. rewrite <- H3. apply IHrefl_trans_1n_trace1 . trivial.
    find_inversion. simpl in *. rewrite <- e. apply IHrefl_trans_1n_trace1. trivial. 
 *  concludes. apply IHrefl_trans_1n_trace1; trivial.
Qed.

(*********************** FINAL THEOREM ***********************************)

Axiom getCertificate_prop:
forall  net c, 
certificate (checkerinput (nwState net (Checker c))) =  (getCertificate (name_component (Checker c))).

Lemma Neighbourhood_Consistency_Ver:
forall  net tr,
step_async_star (params := Checker_MultiParams) step_async_init net tr ->
forall c,
(nwState net (Checker c)).(consistent) = true -> 
(nwState net (Checker c)).(initialized) = true -> 
(nwState net (Checker c)).(queue) = [] -> 
neighbourhood_consistent( name_component (Checker c)).
Proof.
intros.
unfold neighbourhood_consistent.
intros.
apply All_Fact_Check_Network  with (component := comp1) (c:=c) in H.
trivial.
rewrite <- getCertificate_prop with (net:=net).
apply H.
apply queue_empty_message_received_equals_controllist with (k:=comp1) (c:=c) in H.
trivial.
trivial.
unfold initialized in H1. 
apply  andb_true_iff in H1.
destruct H1. 
apply neighbours_in_controllist with (k:=comp1) (c:=c) (tr:=tr) (net:=net) in H3.
trivial.
trivial.
unfold name_component in H3; trivial.
trivial.
apply queue_empty_message_received_equals_controllist with (k:=comp1) (c:=c) (tr:=tr).
trivial.
trivial.
apply neighbours_in_controllist with (k:=comp1) (tr:=tr).
trivial.
trivial.
Qed.

Extraction "Checker_Consistent.ml"  Checker_BaseParams Checker_MultiParams.

