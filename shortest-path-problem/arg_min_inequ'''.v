Section ARG_MIN_INEQUALITY.
Require FunInd.
Require Export List.
Require Export Nat.


Require Import Coq.Logic.Classical_Prop.
Require Import ZArith.


Variable n : nat.
Variable f : { m : nat | m < n } -> nat.
Variable g : { m : nat | m < n } -> nat.
Definition mnnat := { m : nat | m < n }.


Definition ltn (n m : nat) : Prop :=  m < n.
Definition minimal_Pholder P x : Prop := P x /\ (forall y, P y -> f x <= f y).
Definition exists_Px (P : mnnat -> Prop) : Prop := exists x, P x.

Definition P x : Prop := f x < g x.

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

Lemma nat_lessthan_is_mnnat :
  (forall x : nat, In x (nat_lessthan_n n) <-> exists y : mnnat, proj1_sig y = x).
Proof.
  intros.
  unfold mnnat in *.
  split ; intros.
  apply nat_lessthan_n_lessthan_n in H.
  assert (ltn n x).
  unfold ltn ; auto.
  exists (exist (ltn n) x H0) ; auto.

  destruct H.
  destruct x0.
  simpl in *.
  subst.
  unfold ltn in l.
  apply <- nat_lessthan_n_lessthan_n in l.
  auto.
Qed.

Lemma mnnat_is_natlessthan :
  forall x : mnnat, In (proj1_sig x) (nat_lessthan_n n).
Proof.
  intros.
  apply <- nat_lessthan_is_mnnat.
  exists x. auto.
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




Lemma without_P' : forall P,
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

Lemma f_proj1_sig : forall (f : mnnat -> nat) x y,
  proj1_sig x = proj1_sig y -> f x = f y.
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


Lemma f'exists : forall (f : mnnat -> nat),
  exists (ff : nat -> nat), forall x : mnnat, f x = ff (proj1_sig x).
Proof.
  intros.
  assert (n = 0 \/ n > 0).
  induction n.
  auto.
  intuition.
  destruct H.
  exists (fun m : nat => m).
  intuition. destruct x. assert (l' := l). rewrite H in l'. inversion l'.
  unfold mnnat in *.


  exists (fun m : nat => f0 (exist (ltn n) (m mod n) (mod_mnnat m H))).
  intros.
  destruct x.
  simpl.
  unfold ltn.
  assert (l' := l).
  apply mod_mnnat' in l'.

  assert (proj1_sig (exist (fun m : nat => m < n) x l) = proj1_sig (exist (fun m : nat => m < n) (x mod n) (mod_mnnat x H))).
  simpl. rewrite l'.
  auto.
  apply (f_proj1_sig f0) in H0.
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

Lemma P_proj1_sig : forall (P : mnnat -> Prop) x y,
  proj1_sig x = proj1_sig y -> P x = P y.
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

Lemma P'exists : exists P' : nat -> Prop,
  (forall (x0 : nat) (H1 : x0 < n), P' x0 = P (exist (ltn n) x0 H1)).
Proof.
  intros.
  assert (n = 0 \/ n > 0).
  induction n.
  auto.
  intuition.
  destruct H.
  exists (fun n => False).
  intuition. assert (l' := H1). rewrite H in l'. inversion l'.
  unfold mnnat in *.


  exists (fun m : nat => P (exist (ltn n) (m mod n) (mod_mnnat m H))).
  intros.
  unfold ltn.
  assert (l' := H1).
  apply mod_mnnat' in l'.

  assert (proj1_sig (exist (fun m : nat => m < n) x0 H1) = proj1_sig (exist (fun m : nat => m < n) (x0 mod n) (mod_mnnat x0 H))).
  simpl. rewrite l'.
  auto.
  apply (P_proj1_sig P) in H0.
  auto.
Qed.


Lemma inductino : forall n (f' : nat -> nat) (P' : nat -> Prop) x,
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
  destruct H.
  assert (exists (y : nat) (H0 : y < n), P (exist (ltn n) y H0)).
  exists (proj1_sig x).
  destruct x. simpl in *. exists l. auto.
  destruct H0. destruct H0.
  assert (H' := x1).
  apply <- nat_lessthan_n_lessthan_n in H'.
  apply (exists_mnnat_exists_nat_lessthan_n).
  apply exists_mnnat_exists_nat_lessthan_n'.
  clear H x.
  rename x0 into x. unfold ltn.
  apply (without_P' P).
  assert (forall (f : mnnat -> nat), exists (f' : nat -> nat), forall (x : nat) (H0: x < n), f (exist (fun m : nat => m < n) x H0) = f' x).
  intros.
  assert (exists (f' : nat -> nat), forall x : mnnat, f0 x = f' (proj1_sig x)).
  apply f'exists.
  destruct H as [f' H].
  exists f'.
  intros. apply (H (exist (ltn n) x0 H1)).
  assert (HH := H).
  destruct (H f) as [f' Hf'].
  destruct (HH g) as [g' Hg'].
  exists f'. split ; auto ; intros. clear H HH.



  assert (n = 0 \/ n <> 0).
  apply classic.
  destruct H. assert (x1' := x1). rewrite H in x1'.
  inversion x1'.
  clear H'.
  apply P'exists_implies.
  assert (exists P' : nat -> Prop,
  (forall (x0 : nat) (H1 : x0 < n), P' x0 = P (exist (ltn n) x0 H1))).
  apply P'exists.
  destruct H1 as [P' H1].
  exists P'.
  split ; intros.
  auto.
  rewrite <- (H1 x x1) in H0.
  clear H1 Hg' Hf'.


  clear H.
  apply (inductino n _ _ x) ; auto.

(* Intuition: there exists an element for which P holds.
              thus there exists an element for which P holds, that has the minimum f-value
                of all elements where P holds

    - {m : nat | m < n} is a finite set
    - you take all elements from this where P holds (at least one) -- still finite
    - you map f onto all elements                                  -- finite set of nat
    - you take the minimum (maybe not unique)                      -- finite sets of nat must have a minimum

 -1. Solve this "directly"
  0. Built-in library lemmata that solve this in a couple steps.
  1. induction over Cardinality of exists in H:
    - if there is only one, take this one
    - if you have the minimal of n, look whether the n+1 is even less, then
  2. minimum-function, as described before

  - Problems -1: if induction over n: f and P become a mess
  - Problems 2: what to recurse over? is there a "proj1_sig"-reverse function?

recursing over an element of {m : nat | m < n}
  3. minimum-function, recursing over a nat, but needs a "siggify"-function *)
Qed.


Definition minimal_argprop_holder x : Prop := P x /\ (forall y, P y -> f x <= f y).
Definition exists_argprop_x : Prop := exists x, P x.

Lemma exists_minimal_argprop_holder : 
  exists_argprop_x -> exists x, minimal_argprop_holder x.
Proof.
  intros.
  apply (exists_Px_minimal_Pholder) ; auto.
Qed.

Lemma arg_min_inequality : forall x,
  (f x < g x) -> (exists x, f x < g x /\
                            forall y, f y < f x -> f y >= g y).
Proof.
  intros.
  assert (exists x, minimal_argprop_holder x).
  apply exists_minimal_argprop_holder.
  unfold exists_argprop_x.
  unfold P.
  exists x ; auto.
  destruct H0. exists x0.
  unfold minimal_argprop_holder in H0.
  destruct H0.
  unfold P in *.
  destruct x0.
  split ; intros.
  + auto.
  + specialize (H1 y) ; intuition.
Qed.


End ARG_MIN_INEQUALITY.