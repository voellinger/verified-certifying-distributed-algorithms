
Require Import GraphBasics.Graphs.
Require Import Coq.Logic.Classical_Prop.
Require Import Verdi.Verdi.

Require Export StructTact.Fin.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Require Import Verdi.ExtrOcamlBasicExt.
Require Import Verdi.ExtrOcamlList.

Load NetworkModelCommunication.

Section CDAInterface.

Variable a : A_set.
Variable v : C_set.
Variable g : Connected v a.


Inductive inp: Type.
Inductive outp: Type.



Inductive Predicate_distribution: Set:= 
|and : Predicate_distribution
|or : Predicate_distribution.

Inductive Var: Type.
Inductive Value: Type. 
Inductive Assignment := fact_cons: Var ->  Value -> Assignment.

Definition init_neighbor_l (me : Name) := (neighbors v a g (name_component me)).
Variable init_inp_l : Name -> list inp.
Variable init_predicate_distribution_l : Name -> list Predicate_distribution.
Variable init_var_l : Name -> list Var.
Variable init_outp_l : Name -> list outp.
Variable init_certificate : Name -> list Assignment.


Record Checkerknowledge: Set := mk_Checkerknowledge {
  inp_l : list inp;
  Predicate_distribution_l: list Predicate_distribution;
  var_l: list Var;
  neighbor_l: list Component
}.

Definition init_Checkerknowledge (me : Name) :=
  mk_Checkerknowledge (init_inp_l me) (init_predicate_distribution_l me) (init_var_l me) (init_neighbor_l me).



Record Checkerinput  := mk_Checkerinput {
  outp_l : list outp;
  certificate : list Assignment
}.

Definition init_Checkerinput (me : Name) :=
  mk_Checkerinput (init_outp_l me) (init_certificate me).





Record Checkerstartstate := mkCheckerstartstate{
 checkerknowledge: Checkerknowledge; 
 checkerinput : Checkerinput ;
 }.

(* this is right when the algorithm terminates and sets the given/known variables of the checker*)
Definition set_checker_start_state (me: Name) := mkCheckerstartstate (init_Checkerknowledge me) (init_Checkerinput me).

(* 
(***************************************************************)
(* User has to define this part for their algorithm themselves *)
Record Data := mkData{
  checkerstartstate: Checkerstartstate;
  distance : nat;   (* change stuff here appropriately *)
  queue : list Component (* change stuff here appropriately *)
}.

Definition init_Data (me: Name) := mkData (set_checker_start_state me) 0 nil.

(***************************************************************) *)

End CDAInterface.