Require Import Verdi.Verdi.

Require Export StructTact.Fin.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Require Import Verdi.ExtrOcamlBasicExt.
Require Import Verdi.ExtrOcamlList. 

Load NetworkModelTopology.

(* we use the framework Verdi to model the communication in Coq *)
Section Communication.

(* the sub-checker of a component is a logical component building a physical component together with its component
 * a physical component has a unique name 
 *)
Inductive Name := Checker : Component  -> Name.

(* it is decidable wheter to physical components are the same or different *)
Definition Name_eq_dec : forall x y : Name, {x = y} + {x <> y}.
Proof.
  decide equality.
  destruct c. destruct c0. 
  case (eq_nat_dec n n0); intros H.
  left; rewrite H; trivial.
  right; injection; trivial.
Qed.

(* get component of a the sub-checker *)
Definition name_component (n: Name): Component :=
match n with 
  | Checker x => x
end.

(* get sub-checker of a component *)
Definition component_name (c: Component): Name :=
match c with 
  | x => Checker x
end.

(* Since Verdi does not have a modeling option for the topology of a network,
 * we combine GraphBasics for the topology with Verdi for the communication 
 *)
(* our physical components in Verdi are the vertices of our graph modelling the network topology *)
Definition Nodes (v: V_set) (a: A_set) (g: Connected v a): list Name := (map Checker (CV_list v a g)).

(* modelling: all components that exist are part of our network graph *)
(* Necessary since GraphBasics defines the type vertex independent of a graph.
 * A component is of type vertex. We want to speak only about components that are part of the graph. *)
Axiom Component_prop_1: forall (v: V_set) (a: A_set) (g: Connected v a)(c: Component),
v c.

(* it follows that all components are in the vertex list *)
Lemma Component_prop_2: forall (v: V_set) (a: A_set) (g: Connected v a)(c: Component),
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
    right. apply (IHg H0).
   -simpl.
    apply (IHg H).
   -simpl.
    rewrite <- e in H.
    apply (IHg H).
Qed.

(* it follows that all physical components modelled by Verdi are part of the network induced by the graph *)
Lemma all_Names_Nodes (v: V_set) (a: A_set) (g: Connected v a): forall n: Name, In n (Nodes v a g).
Proof.
  unfold Nodes.
  intros.
  destruct n.
  assert (H:= Component_prop_2 v a g).
  destruct (CV_list v a g).
  unfold map.
  apply H. trivial.

  apply (in_map Checker (v0 :: v1) c) in H.
  apply H.
Qed.

(* if a vertex y is not in the set of vertices, then y is also not in vertex list *)
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

(* no physical component in Verdi is mapped to the same vertex of network graph g *)
Lemma NoDup_Nodes : forall (v: V_set) (a: A_set) (g: Connected v a), NoDup (Nodes v a g).
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