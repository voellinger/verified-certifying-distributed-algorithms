Require Import Verdi.Verdi.

Require Export StructTact.Fin.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Require Import Verdi.ExtrOcamlBasicExt.
Require Import Verdi.ExtrOcamlList. 

Load NetworkModelTopology.

Section Communication.

(* We assume a fixed connected graph g=(v,a). *)
Variable a : A_set.
Variable v : C_set.
Variable g : Connected v a.

Inductive Name := Checker : Component  -> Name.

Definition Name_eq_dec : forall x y : Name, {x = y} + {x <> y}.
Proof.
  decide equality.
  destruct c. destruct c0. 
  case (eq_nat_dec n n0); intros H.
  left; rewrite H; trivial.
  right; injection; trivial.
Qed.

(* get component from name*)
Definition name_component (n: Name): Component :=
match n with 
  | Checker x => x
end.

Definition component_name (c: Component): Name :=
match c with 
  | x => Checker x
end.

Definition Nodes : list Name := (map Checker (CV_list v a g)).

(* all components that exist are actually part of our graph *)
Axiom Component_prop_1: forall (v: V_set) (a: A_set) (g: Connected v a)(c: Component),
v c.

Lemma Component_prop_2: forall (c: Component),
In c (CV_list v a g).
Proof.
  intros.
  assert (H:= Component_prop_1).
  specialize (H v a g c).
  induction g.
   -simpl.
    inversion H.
    auto.
   -simpl.
    inversion H.
    inversion H0.
    auto.
    right. apply (IHc0 c0 H0).
   -simpl.
    apply (IHc0 c0 H).
   -simpl.
    rewrite <- e in H.
    apply (IHc0 c0 H).
Qed.

(* this needs the Axiom Component_prop_1: but is it really necessary? What does this actually mean? *)
Lemma all_Names_Nodes : forall n: Name, In n Nodes.
Proof.
  unfold Nodes.
  intros.
  destruct n.
  assert (H:= Component_prop_2).
  destruct (CV_list v a g).
  unfold map.
  apply H. trivial.

  apply (in_map Checker (v0 :: v1) c) in H.
  apply H.
Qed.

Lemma L1: forall (v0 : V_set) y a0 c, ~ v0 y -> ~ In y (CV_list v0 a0 c).
Proof.
  intros.
  induction c.
  simpl.
  intuition.
  rewrite H1 in H.
  apply H.
  apply V_in_single.

  simpl.
  intuition.
  rewrite H1 in H.
  apply H.
  apply In_left.
  apply V_in_single.
  apply IHc in H1.
  apply H1.
  intros.
  apply H.
  apply In_right.
  apply H0.

  simpl.
  apply IHc. apply H.

  simpl.
  apply IHc. rewrite e. apply H.
Qed.

Lemma NoDup_Nodes : NoDup Nodes.
Proof.
  unfold Nodes.
  intros.
  apply NoDup_map_injective.
  congruence.
  induction (g).
  simpl.
  apply NoDup_cons.
  auto.
  apply NoDup_nil.
  
  simpl.
  apply NoDup_cons.

  apply L1.
  apply n.
  apply IHc.

  simpl.
  apply c.
  apply IHc.
  apply c.

  simpl.
  apply (IHc c).
Qed.


End Communication.