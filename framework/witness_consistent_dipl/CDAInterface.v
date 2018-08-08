Require Import GraphBasics.Graphs.
Require Import Coq.Logic.Classical_Prop.
Require Import Verdi.Verdi.

Require Export StructTact.Fin.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Require Import Verdi.ExtrOcamlBasicExt.
Require Import Verdi.ExtrOcamlList.

Require FunInd.

Load NetworkModelCommunication.

(* The user has to change this file to make it fit to their specific CDA *)

(* We assume a fixed connected graph g=(v,a). *)
Variable v : C_set.
Variable a : A_set.
Variable g : Connected v a.

(* Gives the distribution of each distribution-predicate used in the witness predicate *)
Inductive Predicate_distribution: Set:= 
|and : Predicate_distribution
|or : Predicate_distribution.

(* A sub-certificate is an assigment of variables to values. *)
Variable Var: Type.
(* Design choice: Var needs to be differentiable *)
Axiom var_eq_dec : forall x y : Var, {x = y} + {x <> y}.
Variable Value: Type.
(* Design choice: Value needs to be differentiable *)
Axiom val_eq_dec : forall x y : Value, {x = y} + {x <> y}.
Inductive Assignment := assign_cons: Var ->  Value -> Assignment.
(* Design choice: variable or value difference makes the whole assignment different. *)
Axiom asign_cons_eq_dec : forall (x y : Var) (a b : Value),
  {x <> y} + {a <> b} -> assign_cons x a <> assign_cons y b.

Lemma Assignment_eq_dec : forall x y : Assignment, {x = y} + {x <> y}.
Proof.
  intros.
  destruct x, y.
  assert ({v0 = v2} + {v0 <> v2}).
  apply var_eq_dec.
  assert ({v1 = v3} + {v1 <> v3}).
  apply val_eq_dec.
  destruct H.
    destruct H0.
      left. rewrite e. rewrite e0. auto.
      right. apply asign_cons_eq_dec ; auto.
    right. apply asign_cons_eq_dec.
    left. auto.
Qed.

Lemma asign_cons_eq_dec2 : forall (x y : Var) (a b : Value),
  (x = y /\ a = b) <-> (assign_cons x a = assign_cons y b).
Proof.
  split ; intros.
    destruct H.
    subst.
    auto.
  assert (x = y \/ x <> y).
  apply classic. destruct H0. intuition.
  assert (a0 = b \/ a0 <> b).
  apply classic. destruct H0. intuition.
  assert ({x <> x} + {a0 <> b}).
  right. auto. apply asign_cons_eq_dec in H1. intuition.
  assert ({x <> y} + {a0 <> b}).
  left. auto. apply asign_cons_eq_dec in H1. intuition.
Qed.

Definition Certificate := list Assignment.

Definition val_beq (x y : Value) : bool :=
  if val_eq_dec x y then true else false.

Definition var_beq (x y : Var) : bool :=
  if var_eq_dec x y then true else false.


Definition assignment_var (assi: Assignment) :  Var :=
match assi with
  | assign_cons var value => var
end.

Definition assignment_value (assi: Assignment) :  Value :=
match assi with
  | assign_cons var value => value
end.



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

Variable init_inp : Name -> Certificate.
Variable init_predicate_distribution_l : Name -> list Predicate_distribution.
Variable init_outp : Name -> Certificate.
Variable init_witness : Name -> Certificate.

Function init_combined (n : Name) : Certificate :=
  (init_inp n) ++ (init_outp n) ++ (init_witness n).

Definition is_consistent (cert : Certificate) : Prop :=
  forall (assign1 assign2 : Assignment), 
    let (var1, val1) := assign1 in
      let (var2, val2) := assign2 in
        In assign1 cert -> In assign2 cert ->
          var1 = var2 -> val1 = val2.


(* initialisation of a sub-checker;
 * knowledge a sub-checker has even before the cda computed and terminated *)
Record Checkerknowledge : Type := mk_Checkerknowledge {
  inp : Certificate;
  Predicate_distribution_l: list Predicate_distribution;
  neighbor_l: list Component
}.

Definition init_Checkerknowledge (me : Name) :=
  mk_Checkerknowledge (init_inp me) (init_predicate_distribution_l me) (init_neighbor_l me).

(* a sub-checker gets the sub-output and sub-certificate of its component after the cda computed and terminated *)
Record Checkerinput : Type := mk_Checkerinput{
  outp : Certificate;
  witness : Certificate;
  combined : Certificate
}.

Definition init_Checkerinput (me : Name) : Checkerinput :=
  mk_Checkerinput (init_outp me) (init_witness me) (init_combined me).