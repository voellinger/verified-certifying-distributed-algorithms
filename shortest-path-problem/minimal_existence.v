Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.Classical_Prop.
Section MINIMAL_EXISTENCE.

Variable P : nat -> Prop.

Lemma P_upto_n_dec:
  forall n, (exists m, m < n /\ P m) \/ (forall m, m < n -> ~ P m).
Proof.
  intros.
  destruct (classic(exists m, m < n /\ P m)).
  tauto.
  firstorder.
Qed.

Lemma minimal_exists_aux: 
  forall n, P n -> exists m, P m /\ forall p, p < m -> ~ P p.
Proof.
  intro n.
  induction n as [n IH] using lt_wf_ind.
  destruct (P_upto_n_dec n) as [[m [A B]] | C].
  apply IH in A.
  intro.
  assumption.
  assumption.
  intro.
  exists n.
  tauto.
Qed.

Lemma minimal_exists:
  (exists n, P n) -> exists m, P m /\ forall p, p < m -> ~ P p.
Proof.
  intros.
  destruct H as [n].
  apply minimal_exists_aux in H.
  assumption.
Qed.


End MINIMAL_EXISTENCE.