Require Import GraphBasics.Graphs.
Require Import Coq.Logic.Classical_Prop.
Require Import Verdi.Verdi.

Require Export StructTact.Fin.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Require Import Verdi.ExtrOcamlBasicExt.
Require Import Verdi.ExtrOcamlList.

Load NetworkModelCommunication.

(* The user has to change this file to make it fit to their specific CDA *)

(* We assume a fixed connected graph g=(v,a). *)
Variable a : A_set.
Variable v : C_set.
Variable g : Connected v a.

(* In the general case, input and output are just some types. *)
Inductive inp: Type.
Inductive outp: Type.

(* Gives the distribution of each distribution-predicate used in the witness predicate *)
Inductive Predicate_distribution: Set:= 
|and : Predicate_distribution
|or : Predicate_distribution.

(* A sub-certificate is an assigment of variables to values. *)
Inductive Var: Type.
Inductive Value: Type. 
Inductive Assignment := assign_cons: Var ->  Value -> Assignment.

(* These are two placeholders for actual Variables and Values *)
Variable varnull: Var.
Variable valuenull: Value.


(* Minimal input of a network is the network itself.
 * Hence, each component me knows its neighbors in the network graph
 *)
Definition init_neighbor_l (me : Name) := (neighbors v a g (name_component me)).

(* For each sub-checker of a component me, we have to define
 * a list of sub-inputs init_inp_l,
 * a list on how to the distribution predicates are distributable init_predicate_distribution_l,
 * a list of its variables init_var_l,
 * a list of sub-outputs init_outp_l,
 * and a sub-certificate init_certificate.
 *)
Variable init_inp_l : Name -> list inp.
Variable init_predicate_distribution_l : Name -> list Predicate_distribution.
Variable init_var_l : Name -> list Var.
Variable init_outp_l : Name -> list outp.
Variable init_certificate : Name -> list Assignment.

(* initialisation of a sub-checker;
 * knowledge a sub-checker has even befor the cda computed and terminated *)
Record Checkerknowledge: Set := mk_Checkerknowledge {
  inp_l : list inp;
  Predicate_distribution_l: list Predicate_distribution;
  var_l: list Var;
  neighbor_l: list Component
}.

Definition init_Checkerknowledge (me : Name) :=
  mk_Checkerknowledge (init_inp_l me) (init_predicate_distribution_l me) (init_var_l me) (init_neighbor_l me).

(* a sub-checker gets the sub-output and sub-certificate of its component after the cda computed and terminated *)
Record Checkerinput  := mk_Checkerinput {
  outp_l : list outp;
  certificate : list Assignment
}.

Definition init_Checkerinput (me : Name) :=
  mk_Checkerinput (init_outp_l me) (init_certificate me).


Record Checkerstartstate := mkCheckerstartstate{
 checkerknowledge: Checkerknowledge; 
 checkerinput : Checkerinput;
}.

(* the complete state of a sub-checker of component me after termination of the cda*)
Definition set_checker_start_state (me: Name) := mkCheckerstartstate (init_Checkerknowledge me) (init_Checkerinput me).

(* 
(***************************************************************)
(* User has to define this part for their algorithm themselves *)
Record Data := mkData{
  checkerstartstate: Checkerstartstate;
  distance : nat;   (* change stuff here appropriately *)
  queue : list Component (* change stuff here appropriately *)
}.

(* Verid initialization *)
Definition init_Data (me: Name) := mkData (set_checker_start_state me) 0 nil.

(***************************************************************) *)

