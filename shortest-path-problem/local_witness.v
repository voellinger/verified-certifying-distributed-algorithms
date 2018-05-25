Section LOCAL_WITNESS.


Load witness_prop.

Variable n : nat.

Record component : Set := mk_component {
  is_s  : bool;
  i     : (set n);
  E_i   : (set n) -> nat
}.

Variable dist : set n -> nat.

Definition local_start_prop (c : component) : Prop :=
  dist c.(i) = 0.

Definition local_trian_prop (c : component) : Prop :=
  forall j, c.(E_i) j > 0 -> dist c.(i) <= dist j + c.(E_i) j.

Definition local_justf_prop (c : component) : Prop :=
  exists j, c.(E_i) j > 0 /\ dist c.(i) = dist j + c.(E_i) j.

Definition local_wtnss_prop (c : component) : Prop :=
  (c.(is_s) = true -> local_start_prop c /\ local_trian_prop c) /\ 
  (c.(is_s) = false -> local_trian_prop c /\ local_justf_prop c).


Variable start_i : 
  (set n).

Variable E_dists : (set n) -> (set n) -> nat.

Definition select (S : set n) : component :=
  if (proj1_sig S =? proj1_sig start_i) then
    {| is_s := true ; i := S ; E_i := E_dists S |} else
    {| is_s := false ; i := S ; E_i := E_dists S|}.

Lemma select_ok : forall i' : set n, (select i').(i) = i'.
Proof.
  intros.
  unfold select.
  assert ((proj1_sig i' = proj1_sig start_i) \/ ~ (proj1_sig i' = proj1_sig start_i)).
  apply classic.
  destruct H.
  apply Nat.eqb_eq in H. rewrite H. simpl. auto.
  apply Nat.eqb_neq in H. rewrite H. simpl. auto.
Qed.

Hypothesis Hstart_component_existence:
  (select start_i).(is_s) = true.
Hypothesis Hstart_component_unique:
  forall c, c <> (select start_i) -> c.(is_s) = false.
Hypothesis Hlw_conjunction : forall (c : set n), local_wtnss_prop (select c).


Definition network_E (i : (set n))(j : (set n)) : nat :=
  (select j).(E_i) i.

Definition network_g : graph := mk_graph n network_E (select start_i).(i).

Lemma global_start_prop : dist network_g.(s) = 0.
Proof.
  assert (A : local_wtnss_prop (select start_i)).
  apply Hlw_conjunction.
  unfold local_wtnss_prop in A.
  destruct A as [A _].
  assert (B := Hstart_component_existence).
  apply A in B.
  destruct B as [B _].
  unfold local_start_prop in B.
  assert (D : network_g.(s) = (select start_i).(i)).
  auto.
  rewrite D.
  auto.
Qed.

Lemma global_trian_prop : forall u v, 
  network_g.(E) u v > 0 -> dist v <= dist u + network_g.(E) u v.
Proof.
  intros.
  assert (A : local_wtnss_prop (select v)).
  apply Hlw_conjunction.
  unfold local_wtnss_prop in A.
  destruct (classic (is_s (select v) = true)) as [B|B].
  destruct A as [A _].
  apply A in B.
  destruct B as [_ B].
  unfold local_trian_prop in B.
  simpl in H.
  unfold network_E in H.
  apply B in H.
  simpl.
  unfold network_E.
  assert (C : (select v).(i) = v).
  apply select_ok.
  rewrite C in H.
  apply H.
  destruct A as [_ A].
  apply not_true_is_false in B.
  apply A in B.
  destruct B as [B _].
  unfold local_trian_prop in B.
  simpl in H.
  unfold network_E in H.
  apply B in H.
  simpl.
  assert (C : (select v).(i) = v).
  apply select_ok.
  rewrite C in H.
  apply H.
Qed.

Lemma distinct : forall c_i c_j, 
  c_i <> c_j -> select c_i <> select c_j.
Proof.
  intros c_i c_j A.
  assert (B : (select c_i).(i) = c_i).
  apply select_ok.
  assert (C : (select c_j).(i) = c_j).
  apply select_ok.
  rewrite <- B in A.
  rewrite <- C in A.
  destruct (classic (select c_i = select c_j)) as [D|D].
  assert (E : (select c_i).(i) = (select c_j).(i)).
  f_equal.
  apply D.
  tauto.
  apply D.
Qed.

Lemma global_justf_prop : forall v, 
  v <> network_g.(s) ->
    exists u, network_g.(E) u v > 0 /\ dist v = dist u + network_g.(E) u v.
Proof.
  intros.
  assert (A : local_wtnss_prop (select v)).
  apply Hlw_conjunction.
  unfold local_wtnss_prop in A.
  destruct A as [_ A].
  assert (B : is_s (select v) = false).
  apply Hstart_component_unique.
  simpl in H.
  apply distinct.
  rewrite select_ok in H.
  apply H.
  apply A in B.
  destruct B as [_ B].
  unfold local_justf_prop in B.
  rewrite select_ok in B.
  apply B.
Qed.

Hypothesis Hpath_existence : path_existence network_g.
Definition delta_network_g := 
  proj1_sig (delta_existence network_g Hpath_existence).
Definition delta_network_ok := 
  proj2_sig (delta_existence network_g Hpath_existence).

Theorem dist_eq_network_delta : forall (v : set network_g.(V)),
  dist v = delta_network_g v.
Proof.
  apply dist_eq_delta.
  apply global_start_prop.
  unfold trian_prop.
  apply global_trian_prop.
  unfold justf_prop.
  apply global_justf_prop.
Qed.

Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Open Scope nat_scope.


Definition start_check (c : component) := 
  if eq_nat_dec (dist c.(i)) 0 then true else false.

Lemma start_check_ok : forall c, 
  local_start_prop c <-> start_check c = true.
Proof.
  intros.
  unfold start_check.
  intros.
  split.
  intros.
  unfold local_start_prop in H.
  destruct eq_nat_dec.
  reflexivity.
  tauto.
  destruct eq_nat_dec.
  intros.
  unfold local_start_prop.
  assumption.
  intros.
  inversion H.
Qed.


End LOCAL_WITNESS.

Extraction start_check.