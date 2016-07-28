Section GLOBAL_WITNESS_PROP.

Require Import List.
Require Import Arith Omega.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Le.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Logic.Classical_Prop.
Require Import Bool.

Add LoadPath "/home/dash/Documents/diplom/coq/".
Load arg_min_inequ.
Load delta_func.

Variable g : graph.
Variable dist : set g.(V) -> nat.

Hypothesis Hpath_existence : path_existence g.

Definition delta := 
  proj1_sig (delta_existence g Hpath_existence).
Definition delta_ok := 
  proj2_sig (delta_existence g Hpath_existence).

Definition start_prop :=
  dist g.(s) = 0.
Definition trian_prop := forall u v, 
  g.(E) u v > 0 -> dist v <= dist u + g.(E) u v.
Definition justf_prop := forall v,
  v <> g.(s) -> exists u, g.(E) u v > 0 /\ dist v = dist u + g.(E) u v.

Hypothesis Hstart_prop : start_prop.
Hypothesis Htrian_prop : trian_prop.
Hypothesis Hjustf_prop : justf_prop.

Lemma dist_leq_delta : forall v, 
  dist v <= delta v.
Proof.
  intros v.
  assert (Hdelta : delta_prop g v (delta v)) by apply delta_ok.
  unfold delta_prop in Hdelta.
  destruct Hdelta as [p HSP_v].
  unfold shortest_path in HSP_v.
  destruct HSP_v as [HP_v HSP_v].
  set (tmp_s := g.(s)) in *.
  assert (H_s : tmp_s = g.(s)) by reflexivity.
  induction HP_v.
  rewrite H_s.
  rewrite Hstart_prop.
  auto.
  assert (HE := H).
  apply shortest_path_opt_substructure 
    with (p := p) (d := d) in H.
  subst.
  unfold shortest_path in H.
  destruct H as [HP_up HSP_up].
  apply IHHP_v in HSP_up.
  apply Htrian_prop in HE.
  omega.
  reflexivity.
  unfold shortest_path.
  split.
  apply consp.
  assumption.
  rewrite <- H_s.
  assumption.
  rewrite <- H_s.
  assumption.
Qed.

Lemma dist_geq_delta : forall v,
  dist v >= delta v.
Proof.
  intros v.
     
  (** assume that dists v < delta v for some v **)
  destruct (classic (dist v >= delta v)) as [B|B].
  apply B.
  exfalso.
  apply not_ge in B.

  (** among all v with dists v < delta v, there
    * must be a v' s.t. the inequality is fulfilled
    * and dists(v) is minimal **)
  apply arg_min_inequality in B.

  (** instantiate v' and the shortest path p to v' **)
  destruct B as [v' [B C]].
  assert (D : delta_prop g v' (delta v')).
  apply delta_ok.
  unfold delta_prop in D.
  destruct D as [p D].
  
  (** from the assumption v' = sv derive a contradiction
    * so that we know that v' <> sv **)     
  destruct (classic (v' = g.(s))) as [E|E].
  exfalso.
  subst.
  rewrite Hstart_prop in B.
  assert (E : delta g.(s) = 0).
  assert (F : shortest_path g (g.(s)::nil) g.(s) g.(s) 0).
  split.
  apply zerop.
  intros.
  omega.
  destruct F as [G H].
  destruct D as [I J].
  destruct I.
  reflexivity.
  apply J in G.
  omega.
  omega.

  (** now that we know that v' <> startv we can use the
    * justification property to get an justifying edge 
    * (u, v) to v **)
  apply Hjustf_prop in E.
  destruct E as [u [E G]].

  (** dists u < dists v' since edge weights are positive **)
  assert (H : dist u < dist v').
  omega.

  (** with dists u < dists v' and the choice of v' we 
    * know that dists u >= delta u **)
  apply C in H.

  (** further we know from the lemma above that
    * dist u <= delta u **)
  assert (I : dist u <= delta u).
  apply dist_leq_delta.
  
  (** together dists u = delta u **)
  assert (J : dist u = delta u).
  omega.
  
  (** with the justifying edge (u, v') we can construct
   * a path to v' of cost dist u + c(u, v') **)
  assert (K : delta_prop g u (delta u)).
  apply delta_ok.
  unfold delta_prop in K.
  destruct K as [p' K].
  destruct K as [K L].
  assert (P := E).
  apply lastv_auxilary in K.
  destruct K as [p'' K].
  apply consp with (p := p'') (sv := g.(s)) (d := (dist u)) in E.
  destruct D as [M N]. 
  apply N in E.
  subst. 
  rewrite G in B.
  rewrite J in G.

  (** with this above constructed path we can derive a 
    * contradiction **)
  assert (E' := E).
  clear E.
  rewrite <- J in G.
  rewrite <- G in B.
  omega.
  rewrite J.
  apply K.
Qed.

Theorem dist_eq_delta : forall v,
  dist v = delta v.
Proof.
  intro v.
  apply le_antisym.
  apply dist_leq_delta.
  apply dist_geq_delta.
Qed.

End GLOBAL_WITNESS_PROP.