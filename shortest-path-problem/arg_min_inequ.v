Section ARG_MIN_INEQUALITY.
Require FunInd.
Require Export List.
Require Export Nat.


Require Import Coq.Logic.Classical_Prop.
Require Import ZArith.


(* Intuition: there exists an element for which P holds.
              thus there exists an element for which P holds, that has the minimum f-value
                of all elements where P holds

    - {m : nat | m < n} is a finite set
    - you take all elements from this where P holds (at least one) -- still finite
    - you map f onto all elements                                  -- finite set of nat
    - you take the minimum (maybe not unique)                      -- finite sets of nat must have a minimum
 *)



Variable n : nat.
Definition mnnat := { m : nat | m < n }.
Variable f : mnnat -> nat.
Variable g : mnnat -> nat.



Definition P x : Prop := f x < g x.
Definition ltn (n m : nat) : Prop :=  m < n.
Definition minimal_Pholder x : Prop := P x /\ (forall y, P y -> f x <= f y).
Definition exists_Px : Prop := exists x, P x.

Fixpoint nat_lessthan_n (n : nat) : list nat :=
  match n with
  | 0 => nil
  | S(x) => x :: (nat_lessthan_n x)
  end.

Lemma nat_lessthan_n_lessthan_n : forall n x,
  In x (nat_lessthan_n n) <-> x < n.
Proof.
  split ; intros ; induction n0 ; simpl in * ; subst ; intuition ; subst ; intuition.
  inversion H ; intuition.
Qed.

Lemma exists_mnnat_exists_nat_lessthan_n : forall (P : mnnat -> Prop),
  (exists (y : nat) (H0 : ltn n y),
  (In y (nat_lessthan_n n) -> P (exist (ltn n) y H0))) -> 
    exists x : mnnat, P x.
Proof.
  intros.
  unfold ltn in H.
  destruct H. destruct H.
  assert (H0' := x0).
  apply <- nat_lessthan_n_lessthan_n in H0'.
  intuition.
  exists (exist (ltn n) x x0). auto.
Qed.

Lemma exists_mnnat_exists_nat_lessthan_n' : forall P,
(exists (y : nat) (H0 : ltn n y), P (exist (ltn n) y H0) /\ forall (y0 : nat) (H1 : ltn n y0),
                   P (exist (ltn n) y0 H1) -> f (exist (ltn n) y H0) <= f (exist (ltn n) y0 H1)) ->
exists (y : nat) (H1 : ltn n y),
  In y (nat_lessthan_n n) ->
  P (exist (ltn n) y H1) /\ (forall y0 : mnnat, P y0 -> f (exist (ltn n) y H1) <= f y0).
Proof.
  intros.
  repeat destruct H.
  exists x. exists x0.
  split ; intros ; auto.
  assert (ltn n (proj1_sig y0)).
  destruct y0.
  auto.
  destruct y0.
  simpl in *.
  specialize (H0 x1 l).
  auto.
Qed.


Lemma exists_f'_implies : forall P,
(exists f' : nat -> nat,
      (forall (x : nat) (H0 : x < n), f (exist (fun m : nat => m < n) x H0) = f' x) /\
(exists (y : nat) (H0 : y < n), P (exist (fun m : nat => m < n) y H0) /\
  forall (y0 : nat) (H1 : y0 < n), P (exist (fun m : nat => m < n) y0 H1) ->
  f' y <= f' y0)) ->
(exists (y : nat) (H0 : y < n), P (exist (fun m : nat => m < n) y H0) /\
  forall (y0 : nat) (H1 : y0 < n), P (exist (fun m : nat => m < n) y0 H1) ->
  f (exist (fun m : nat => m < n) y H0) <= f (exist (fun m : nat => m < n) y0 H1)).
Proof.
  intros.
  destruct H as [f' H]. destruct H.
  repeat destruct H0.
  exists x. exists x0. intros.
  assert (H' := H).
  specialize (H x x0).
  rewrite H.
  split ; auto. intros.
  specialize (H' y0 H2).
  rewrite H'.
  apply (H1 y0 H2) ; auto.
Qed.


Lemma mod_mnnat : forall m,
  n > 0 -> m mod n < n.
Proof.
  intros.
  apply PeanoNat.Nat.mod_upper_bound.
  intuition.
Qed.

Lemma mod_mnnat' : forall m,
  m < n -> m mod n = m.
Proof.
  intros.
  apply PeanoNat.Nat.mod_small.
  auto.
Qed.

(* One main point: because of proof_irrelevance, the intuition holds, that 
  the proof (proj2_sig) doesn't change the element, as long as it is there. *)
Lemma proj1_sig_eq : forall (x y : mnnat),
  proj1_sig x = proj1_sig y -> x = y.
Proof.
  intros.
  rewrite (sig_eta x).
  rewrite (sig_eta y).
  destruct x. destruct y as [y H0].
  simpl in *.
  subst.
  assert (l = H0).
  apply proof_irrelevance.
  subst.
  intuition.
Qed.

(* Second main point: we constructed a transformation for Functions and properties,
  with `mod`. After `mod n` we alwayy get a number smaller than n, apart from the
  case n = 0. The transformation needs a proof itself, which was tricky. *)
Lemma Pf'exists : forall A (a : A) (Pf : mnnat -> A), exists Pf' : nat -> A,
  (forall (x0 : nat) (H1 : x0 < n), Pf' x0 = Pf (exist (ltn n) x0 H1)).
Proof.
  intros.
  assert (n = 0 \/ n > 0).
  induction n.
  auto.
  intuition.
  destruct H.
  exists (fun n => a).
  intuition. assert (l' := H1). rewrite H in l'. inversion l'.
  unfold mnnat in *.


  exists (fun m : nat => Pf (exist (ltn n) (m mod n) (mod_mnnat m H))).
  intros.
  unfold ltn.
  assert (l' := H1).
  apply mod_mnnat' in l'.

  assert (proj1_sig (exist (fun m : nat => m < n) x0 H1) = 
          proj1_sig (exist (fun m : nat => m < n) (x0 mod n) (mod_mnnat x0 H))).
  simpl. rewrite l'.
  auto.
  apply proj1_sig_eq in H0.
  rewrite H0.
  auto.
Qed.

Lemma P'exists_implies : forall f',
(exists (P' : nat -> Prop), (forall (x : nat) (H0 : x < n), P' x = P (exist (ltn n) x H0)) /\
(exists (y : nat) (H1 : y < n),
  P' y /\
  (forall (y0 : nat) (H2 : y0 < n),
   P' y0 -> f' y <= f' y0))) ->
(exists (y : nat) (H1 : y < n),
  P (exist (fun m : nat => m < n) y H1) /\
  (forall (y0 : nat) (H2 : y0 < n),
   P (exist (fun m : nat => m < n) y0 H2) -> f' y <= f' y0)).
Proof.
  intros.
  destruct H as [P' H].
  destruct H.
  repeat destruct H0.
  exists x. exists x0.
  split ; intros ; intuition.
  unfold ltn in *.
  rewrite <- (H x x0) ; auto.
  apply (H1 y0) ; auto.
  rewrite (H y0 H2) ; auto.
Qed.

(* The actual induction proof, after all transformations took place. *)
Lemma induction_proof : forall n (f' : nat -> nat) (P' : nat -> Prop) x,
 x < n -> P' x ->
(exists (y : nat) (_ : y < n),
  P' y /\ (forall y0 : nat, y0 < n -> P' y0 -> f' y <= f' y0)).
Proof.
  clear n f g.
  intros n0.
  induction n0 ; intros f'0 ; intros ; intuition.
  inversion H.

  inversion H ; subst ; intuition.
  + specialize (IHn0 f'0 P').
    assert ((exists x : nat, x < n0 /\ P' x) \/ ~(exists x : nat, x < n0 /\ P' x)).
    apply classic. destruct H1.
    - destruct H1. destruct H1.
      specialize (IHn0 x). intuition.
      destruct H4. destruct H3.
      assert (f'0 x0 <= f'0 n0 \/ ~ f'0 x0 <= f'0 n0). apply classic. destruct H4.
      exists x0. assert (x0 < S n0). auto. exists H5. intuition.
      inversion H3 ; subst ; intuition.
      exists n0. exists H. intuition.
      inversion H3 ; subst ; intuition.
      specialize (H6 y0) ; intuition.
    - exists n0. exists H.
      intuition.
      inversion H2 ; subst ; intuition.
      assert (y0 < n0). auto.
      exfalso. apply H1. exists y0 ; auto.
  + specialize (IHn0 f'0 P' x). intuition.
    clear H2.
    destruct H3. destruct H1. destruct H1.
    assert (f'0 x0 <= f'0 n0 \/ ~ f'0 x0 <= f'0 n0). apply classic. destruct H3.
    exists x0. assert (x0 < S n0). auto. exists H4.
    intuition.
    inversion H5 ; subst ; intuition.
    assert (P' n0 \/ ~ P' n0). apply classic. destruct H4.
    exists n0. assert (n0 < S n0). auto. exists H5.
    intuition.
    inversion H6 ; subst ; intuition.
    specialize (H2 y0) ; intuition.
    exists x0. assert (x0 < S n0). auto. exists H5.
    intuition.
    inversion H6 ; subst ; intuition.
Qed.


Lemma exists_Px_minimal_Pholder :
  (exists x, P x) -> exists x, (P x /\ (forall y, P y -> f x <= f y)).
Proof.
  intros.

  auto.
  destruct H. destruct x.
  assert (H' := l). rename l into x1. rename H into H0.
  apply <- nat_lessthan_n_lessthan_n in H'.
  apply exists_mnnat_exists_nat_lessthan_n.
  apply exists_mnnat_exists_nat_lessthan_n'.
  unfold ltn.
  apply (exists_f'_implies P).
  assert (exists (f' : nat -> nat), 
    forall (x : nat) (H0: x < n), f' x = f (exist (fun m : nat => m < n) x H0)).
  intros.
  apply (Pf'exists nat 0 f).
  destruct H as [f' Hf'].
  exists f'. split ; auto ; intros.



  clear H'.
  apply P'exists_implies.
  assert (exists P' : nat -> Prop,
    (forall (x0 : nat) (H1 : x0 < n), P' x0 = P (exist (ltn n) x0 H1))).
  apply (Pf'exists Prop False P).
  destruct H as [P' H].
  exists P'.
  split ; intros.
  auto.
  unfold ltn in *.
  rewrite <- (H x x1) in H0.
  apply (induction_proof n _ _ x) ; auto.
Qed.


Definition exists_P_x : Prop := exists x, P x.
Definition minimal_P_holder x : Prop := P x /\ (forall y, P y -> f x <= f y).

Lemma exists_minimal_P_holder : 
  exists_P_x -> exists x, minimal_P_holder x.
Proof.
  intros.
  unfold exists_P_x in *. unfold minimal_P_holder.
  apply (exists_Px_minimal_Pholder) ; auto.
Qed.

(* Main Lemma of this file. *)
Lemma arg_min_inequality : forall x,
  (f x < g x) -> (exists x, f x < g x /\
                            forall y, f y < f x -> f y >= g y).
Proof.
  intros.
  assert (exists x, minimal_P_holder x).
  apply exists_minimal_P_holder.
  unfold exists_P_x.
  unfold P.
  exists x ; auto.
  destruct H0. exists x0.
  unfold minimal_P_holder in H0.
  destruct H0.
  unfold P in *.
  split ; intros.
  + auto.
  + specialize (H1 y) ; intuition.
Qed.


End ARG_MIN_INEQUALITY.
