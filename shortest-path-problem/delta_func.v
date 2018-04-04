Require Import Coq.Logic.ClassicalUniqueChoice.
Require Import Coq.Logic.Epsilon.


Load graph.
Load minimal_existence.

Definition path_existence (g : graph) :=
  forall v, exists p d, path g p v g.(s) d. 

Definition delta_prop (g : graph) (v : set g.(V)) (d : nat) : Prop :=  
  exists p, shortest_path g p v g.(s) d.

Lemma shortest_path_existence : forall g v,
  (exists p d, path g p v g.(s) d) -> 
  exists p d, shortest_path g p v g.(s) d.
Proof.
  intros.
  assert (A: exists d p, path g p v (s g) d).
  destruct H as [p [d H]].
  exists d.
  exists p.
  assumption.
  clear H.
  apply minimal_exists in A.
  destruct A as [m [[p A] B]].
  exists p.
  exists m.
  unfold shortest_path.
  split.
  assumption.
  intros.
  destruct (classic(m <= d')) as [I|I]. 
  apply I.
  exfalso.
  apply not_ge in I.
  apply B in I.
  apply not_ex_all_not with (n := p') in I.
  tauto.
Qed. 

Lemma delta_prop_functional : forall g, 
  path_existence g ->
    forall v, exists ! d, delta_prop g v d.
Proof.
  intros g path_existence v.
  assert (exists p d, path g p v g.(s) d).
  apply path_existence.
  apply shortest_path_existence in H.
  destruct H as [p [d Hsp]].
  exists d.
  unfold unique.
  split.
  unfold delta_prop.
  exists p.
  apply Hsp.
  intros d' Hd.
  unfold delta_prop in Hd.
  destruct Hd as [p' Hsp'].
  unfold shortest_path in Hsp.
  destruct Hsp as [Hp Hsp].
  unfold shortest_path in Hsp'.
  destruct Hsp' as [Hp' Hsp'].
  destruct (classic (d = d')).
  apply H.
  destruct (not_eq d d').
  apply H.
  apply Hsp' in Hp. omega.
  apply Hsp in Hp'. omega.
Qed.

Lemma delta_existence : forall g, 
  path_existence g ->
    { f | forall v, delta_prop g v (f v) }.
Proof.
  intros.
  apply constructive_indefinite_description.
  apply unique_choice.
  apply delta_prop_functional.
  assumption.
Qed.
