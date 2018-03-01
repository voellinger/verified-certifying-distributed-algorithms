Require Import PeanoNat.
Local Open Scope nat_scope.
Require Import Verdi.Verdi.

Load nw-model-version-consistency.
Load MA_Basics.

(*ZVA Interface*)


Inductive inp: Type.
Inductive outp: Type.

Definition Inpt := list inp.
Definition Out := list outp.

Inductive Predicate: Set:= 
|and : Predicate
|or : Predicate.

Definition Local_predicates:= list Predicate.


Inductive Key: Type.
Inductive Value: Type. 
Inductive Fact := fact_cons: Key ->  Value -> Fact.

Variable keynull: Key.
Variable valuenull: Value.

Definition Certificate:= list Fact.


Variable beqKey : Key -> Key -> bool.
Variable beqValue : option Value -> option Value -> bool.


Axiom beqKey_eq:
forall x y, beqKey x y = true -> x = y.

Axiom beqValue_eq:
forall x y, beqValue x y = true -> x = y.

Axiom fact_eq_dec:
forall (x y : Fact), {x=y} + {x<>y}.

Definition fact_key (fact:Fact) :  Key :=
match fact with
  | fact_cons key value => key
end. 

Definition fact_value (fact:Fact) : Value :=
match fact with
  | fact_cons key value => value
end.


(* get position of key in certificate c*)
Fixpoint get_pos_(pos:nat) (c : list Fact) (key: Key) : option nat := 
match c with 
      | f :: fs => if (beqKey (fact_key f) key) then Some (pos) else get_pos_ (pos + 1) fs  key
      | nil =>  None
end.

Definition get_pos:= get_pos_ 0.


Notation "a == b" := (beq_nat a b) (at level 70).


(* return fact in certificate on position pos*)
Fixpoint findInCert (init: nat) (c : list Fact) (pos : option nat) : option (Fact) :=
    match c, pos with
      | _ , None => None
      | nil, _ => None
      | f :: fs, Some x => if init == x then
                    Some f
                  else
                    if init <? x then
                      None
                    else
                      findInCert (init + 1) fs pos
end.

Definition findValue (c :list Fact) (pos: option nat) : option Value  := 
match findInCert 1 c pos with 
          | Some f => Some (fact_value f)
          | None => None
end.

(*get certificate of a component*)
Variable getCertificate: Component -> Certificate.

(* Overlap / Überlappung*)

(* get positions (x,y) of overlap in a variable*)
Definition overlap (c1 c2: list Fact) (key: Key): (option nat*option  nat) :=
match (get_pos c1 key), (get_pos c2 key) with 
      
      | None, None  => (None, None)
      | x, None => (None, None)
      | None, y  => (None, None)
      | x, y => (x,y)

      end.

Definition overlapping_in_var (c1 c2: Certificate) (k:Key):= 
exists (x y :nat), (Some x, Some y) = overlap c1 c2 k.

(* Connectivity / Zusammenhang*)

(* auf Pfad bezogen*)
Definition path_connected_in_var (comp1 comp2:Component) (vl : V_list) (el : E_list) (p : Path v a comp1 comp2  vl el) (k:Key) :=
forall (comp3 comp4:Component),In comp3 (comp1::vl) -> In comp4 (comp1::vl)
-> overlapping_in_var  (getCertificate comp3) (getCertificate comp4) k.

Definition all_fact_path_prop (comp1 comp2:Component) (vl : V_list) (el : E_list) (p : Path v a comp1 comp2  vl el):=
forall (k:Key), path_connected_in_var comp1 comp2 vl el p k .

Lemma pathprop_ind:
forall comp1 comp2 a0 vl el k x (p:Path v a comp1 comp2 (a0 :: vl) el) (p0:Path v a a0 comp2 vl x),
path_connected_in_var comp1 comp2 (a0 :: vl) el p k -> path_connected_in_var a0 comp2 vl x p0 k.
Proof.
intros.
unfold path_connected_in_var in *.
intros.
apply H .
unfold In.
right.
unfold In in H0.
trivial.
unfold In.
right.
unfold In in H1.
trivial.
Qed.

(* auf Netzwerk bezogen*)

Definition witness_connected_in_var (con : Connected v a) (k:Key):=
forall (comp1 comp2: Component), (v comp1) -> (v comp2) -> 
{vl : V_list &  {el : E_list & { p: Path v a comp1 comp2 vl el & 
path_connected_in_var comp1 comp2 vl el p k}}}.

Definition witness_connected (con : Connected v a):=
forall k, witness_connected_in_var con k.

(* Consistency / Konsistenz *)

Definition consistent_in_var (c1 c2: Certificate) (k:Key):= 
forall (x y :nat ), ((Some x, Some y) = overlap c1 c2 k -> 
eq (findValue c1 (Some x)) (findValue c2 (Some y))).

Definition consistent_in_all_var (c1 c2: Certificate) :=
forall (k:Key), consistent_in_var c1 c2 k. 

Definition consistent_alt (c1 c2: Certificate):= 
forall k, overlapping_in_var c1 c2 k -> 
eq (findValue c1 (get_pos c1 k)) (findValue c2 (get_pos c2 k)).
 

Theorem consistency_defs:
forall c1 c2,
 consistent_alt  c1 c2 <-> consistent_in_all_var c1 c2.
Proof.
intros.
split.
intros.
unfold consistent_alt  in *.
unfold consistent_in_all_var in *.
unfold consistent_in_var.
intros.
assert (G:=H0).
unfold overlap in G.
repeat break_match.
inversion G.
rewrite <- Heqo. rewrite <- Heqo0. apply H.
unfold overlapping_in_var.
exists x. exists y. trivial.
discriminate.
discriminate.
discriminate.
intros. 
unfold consistent_alt  in *.
unfold consistent_in_all_var in *.
unfold consistent_in_var in *.
intros.
unfold overlapping_in_var in *.
destruct H0.
destruct H0.
assert (G:=H0).
unfold overlap in H0.
repeat break_match.
inversion H0.
apply H with (k:=k) (x:=n) (y:=n0).
rewrite H2 in G. rewrite H3 in G; trivial.
discriminate.
discriminate.
discriminate.
Qed.


Definition one_neighbour_consistency (comp :Component)(comp1: Component) :=
In comp1 (neighbors g comp) -> consistent_in_all_var (getCertificate comp)(getCertificate comp1).

Definition all_neighbourhoods_consistent2 (comp :Component) :=
forall (comp1: Component), one_neighbour_consistency comp comp1.

Definition neighbourhood_consistent (comp :Component) :=
forall (comp1: Component), In comp1 (neighbors g comp) ->
consistent_in_all_var (getCertificate comp)(getCertificate comp1).

Lemma neighbourcon:
forall c, all_neighbourhoods_consistent2 c <-> neighbourhood_consistent c.
Proof.
intros.
split.
intros.
unfold all_neighbourhoods_consistent2 in *.
unfold neighbourhood_consistent.
unfold one_neighbour_consistency in H.
intros.
apply H.
trivial.
intros.
unfold all_neighbourhoods_consistent2 in *.
unfold neighbourhood_consistent in *.
unfold one_neighbour_consistency in *.
intros.
apply H.
trivial.
Qed.


Definition all_neighbourhoods_consistent :=
forall (comp:Component), (v comp) -> neighbourhood_consistent comp.


(** Network Consistency **) 

Definition witness_consistent (con: Connected v a):=
forall (comp1 comp2: Component), (v comp1) -> (v comp2) -> consistent_in_all_var (getCertificate comp1) (getCertificate comp2).


(** Proofs **)


(* helping propertiesof overlap function*)

Lemma overlap_injective_1:
forall x y comp1 comp2 k, 
(Some x, Some y) = overlap (getCertificate comp1) (getCertificate comp2) k <->
Some x = (get_pos (getCertificate comp1) k ) /\ 
Some y = (get_pos (getCertificate comp2) k).
Proof.
intros.
split.
intros.
unfold overlap in *.
repeat break_match.
inversion H.
auto.
inversion H.
inversion H.
inversion H.
(*2. implication *)
intros.
unfold overlap.
repeat break_match.
inversion H.
rewrite H0.
rewrite H1.
reflexivity.
inversion H.
inversion H1.
inversion H.
inversion H1.
inversion H.
inversion H2.
inversion H.
inversion H0.
Qed.

(* auf Pfad bezogen*)
Lemma overlap_injective:
forall x0 x1 x2 x3 comp1 comp2 comp3 k, 
   (Some x0, Some x1) = overlap (getCertificate comp1) (getCertificate comp2) k /\ 
   (Some x2, Some x3) = overlap (getCertificate comp2) (getCertificate comp3) k ->
   x1=x2 .
Proof.
intros.
destruct H.
unfold overlap in *.
repeat break_match.
inversion H.
inversion H0.
reflexivity.

inversion H.
inversion H0.
inversion H.
inversion H0.
inversion H.
inversion H0.
inversion H.
Qed.

Lemma overlap_interchangeable:
forall x y comp1 comp2 k, 
(Some x, Some y) = overlap (getCertificate comp1) (getCertificate comp2) k <->
(Some y, Some x) = overlap (getCertificate comp2) (getCertificate comp1) k.
Proof.
intros.
split.
intros.
unfold overlap in *.
repeat break_match.
inversion H.
trivial.
inversion H.
inversion H.
inversion H.
intros.
unfold overlap in *.
repeat break_match.
inversion H.
trivial.
inversion H.
inversion H.
inversion H.
Qed.


Lemma transitivity_of_consistent_in_var:
forall comp1 comp2 comp3 k x y vl el (p:Path v a x y vl el ),
v comp1 -> v comp2 -> v comp3 -> v x -> v y -> 
In comp1 (x::vl) -> In comp2 (x::vl) -> In comp3 (x::vl) ->
path_connected_in_var x y vl el p k
->
consistent_in_var (getCertificate comp1) (getCertificate comp2) k /\ 
consistent_in_var (getCertificate comp2) (getCertificate comp3) k ->
consistent_in_var (getCertificate comp1) (getCertificate comp3) k.
Proof.
intros.
unfold path_connected_in_var in *.
destruct H8.

unfold consistent_in_var  in *.
unfold overlapping_in_var in *.
destruct H7 with (comp3:=comp1) (comp4:=comp2);trivial.
destruct H10.
assert (J:=H10).
destruct H7 with (comp3:=comp2) (comp4:=comp3);trivial.
destruct H11.
assert (L:=H11).
assert ( (Some x0, Some x1) =
 overlap (getCertificate comp1) (getCertificate comp2) k /\ (Some x2, Some x3) =
 overlap (getCertificate comp2) (getCertificate comp3) k) .
split.
trivial.
trivial.
apply overlap_injective in H12.
rewrite <- H12 in H11.
apply H8 in J.
apply H9 in H11.
intros.
assert (B:=H13).
apply overlap_interchangeable in B.
assert ((Some y0, Some x4) =
    overlap (getCertificate comp3) (getCertificate comp1) k /\ 
      (Some x0, Some x1) =
      overlap (getCertificate comp1) (getCertificate comp2) k).
split.
trivial.
trivial.

apply overlap_injective in H14.
symmetry in H14.
rewrite H14 in J.
assert ( (Some x2, Some x3) =
    overlap (getCertificate comp2) (getCertificate comp3) k /\ (Some y0, Some x4) =
    overlap (getCertificate comp3) (getCertificate comp1) k).
split.
trivial.
trivial.
apply overlap_injective in H15.
rewrite H11 in J.
rewrite <- H15.

trivial.
Qed.

(* reflexivity for consistent_in_all_var *)
Lemma consistent_in_var_reflexive:
forall comp k, consistent_in_var comp comp k.
Proof.
intros.
unfold consistent_in_var.
intros.
unfold overlap in *.
break_match.
inversion H.
reflexivity.
inversion H.
Qed.


(* commutativity for consistent_in_all_var *) 
Lemma consistent_in_var_sym:
forall comp1 comp2 k,
consistent_in_var (getCertificate comp1) (getCertificate comp2) k <->  consistent_in_var (getCertificate comp2) (getCertificate comp1) k.
Proof.
intros.
split.
intros.
unfold consistent_in_var in *.
intros.
apply overlap_interchangeable in H0.
apply H in H0.
symmetry.
trivial.
intros.
unfold consistent_in_var in *.
intros.
apply overlap_interchangeable in H0.
apply H in H0.
symmetry.
trivial.
Qed.

Lemma path_one_var_consistency_ :
forall vl comp1 comp2 comp3 el k (p: Path v a comp1 comp2 vl el ), v comp1 -> 
v comp2 -> v comp3 -> 
path_connected_in_var comp1 comp2 vl el p k ->
all_neighbourhoods_consistent  -> 
In comp3 vl -> 
consistent_in_var (getCertificate comp3) (getCertificate comp1) k.
Proof.
intros  vl.
induction vl.
intros.
inversion H4.
intros.
destruct H4.

assert (Q:=p).
apply neighbourslist2 in Q.
unfold all_neighbourhoods_consistent in *.
unfold neighbourhood_consistent in *.
rewrite <- H4.

unfold consistent_in_all_var in *.
apply H3.
rewrite <- H4 in H1.
trivial.
trivial.

(*transitivität*)
assert (TRANS: consistent_in_var (getCertificate comp3) (getCertificate a0) k /\ consistent_in_var (getCertificate a0)(getCertificate comp1) k).

split.
(*1. fall : beide in vl, Anwendung der Hypothese*)
assert (Q:=p).
apply P_backstep in Q.
destruct Q.
apply IHvl with (comp2:=comp2)(el:=x)(p:=p0).
apply P_endx_inv in p0.
trivial.
trivial.
trivial.
apply pathprop_ind with (x:=x) (p0:=p0) in H2.
trivial.

trivial.
trivial.

assert (path:=p).
apply neighbourslist2 in path.
unfold all_neighbourhoods_consistent in *.
unfold neighbourhood_consistent in *.
unfold consistent_in_all_var in *.
apply H3.
assert (path':=p).
apply P_backstep in path'.
destruct path'.
apply P_endx_inv in p0.
trivial.
trivial.

apply transitivity_of_consistent_in_var  with (x:=comp1) (y:=comp2) (vl:=a0::vl) (el:=el) (p:=p) in TRANS.
trivial.

(*neu*)
trivial.
assert (G:=p).
apply P_backstep in G.
destruct G.
apply P_endx_inv in p0.
trivial.
trivial.
trivial.
trivial.
unfold In.
right.
right.
unfold In in H4.
trivial.
unfold In.
right.
auto.
unfold In.
auto.
trivial.
Qed.

(** Theorem **)



Theorem consistency_checkable:
witness_connected g -> all_neighbourhoods_consistent -> witness_consistent g.
Proof.
intros.
unfold witness_consistent .
intros.
case (C_eq_dec  comp1 comp2).
intros.
rewrite e.
unfold consistent_in_all_var.
intros.
apply consistent_in_var_reflexive.
intros.
apply Connected_path with (a:=a) (x:=comp1) in H2;trivial.
destruct H2.
destruct s.
unfold consistent_in_all_var.
intros.
apply consistent_in_var_sym.

unfold witness_connected in *.
unfold witness_connected_in_var in*.
destruct H with (k:=k) (comp1:=comp1) (comp2:=comp2).

trivial.
apply P_endy_inv in p.
trivial.
destruct s.
destruct s.

apply path_one_var_consistency_ with (comp3:=comp2) (comp1:=comp1) (comp2:=comp2) (vl:=x1) (el:=x2) (k:=k)(p:=x3).
trivial.
apply P_endy_inv in p.
trivial.
apply P_endy_inv in p.
trivial.
trivial.
trivial.
assert (lol:=x3).
apply P_iny_vl in lol.
trivial.
inversion lol.
contradiction.
unfold V_nil.
discriminate.
apply g.
Qed.
