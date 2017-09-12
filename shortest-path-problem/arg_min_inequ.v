Section ARG_MIN_INEQUALITY.

Variable n : nat.
Variable f : { m : nat | m < n } -> nat.
Variable g : { m : nat | m < n } -> nat.

Axiom arg_min_inequality : forall x,
  (f x < g x) -> (exists x, f x < g x /\ 
                            forall y, f y < f x -> f y >= g y).


End ARG_MIN_INEQUALITY.
(*
Print nat.
Print list.
Print le.


Section AA.

Variable n : nat.
Variable f : nat -> nat.
Variable g : nat -> nat.

Open Scope list_scope.

Fixpoint eval (f g : nat -> nat) (n : nat) : list (nat * nat * nat) :=
match n with
| O    => nil
| S n' => (n', f n', g n') :: (eval f g n') 
end.

Require Import Coq.Lists.List.

Fixpoint beq_nat (n m : nat) : bool :=
match n with
| O    => match m with
          | O => true
          | S m' => false
          end
| S n' => match m with
          | O => false
          | S m' => beq_nat n' m'
          end
end.

Fixpoint ble_nat (n m : nat) : bool :=
match n with
| O    => true
| S n' => match m with
          | O => false
          | S m' => ble_nat n' m'
          end
end.

Definition blt_nat (n m : nat) : bool :=
  andb (ble_nat n m) (negb (beq_nat n m)).

Definition filter_lt (e : nat * nat * nat) : bool :=
match e with
| (_, f, g) => {f < g}+{f>=g}(*blt_nat f g*)
end.
  
Definition fold_min (e : nat * nat * nat) (acc : nat * nat) :=
match e with
| (x, fv, _) => match acc with
                | (x_min, f_min) => if blt_nat fv f_min then (x, fv)
                                                        else (x_min, f_min)
                end
end.

Definition project_1st (e : nat * nat) : nat :=
match e with
| (a, _) => a
end.

Definition get_min_inequality (f g : nat -> nat) (n : nat) :=
  fold_right fold_min (n, f n) (filter filter_lt (eval f g n)).

Lemma filter_lt_ok : forall x fv gv, 
  In (x, fv, gv) (filter filter_lt (eval f g n)) -> blt_nat fv gv = true.
Proof.
  intros.
  simpl in H.
  set (l := eval f g n) in H.
  apply filter_In in H.
  destruct H as [A B].
  unfold filter_lt in B.
  assumption.
Qed. 

Definition F (x : nat) := x.
Definition G (x : nat) := x+1.

Lemma blt_lt : forall a b, blt_nat a b = true <-> a < b.
Proof.
Admitted.
 

Eval compute in get_min_inequality F G 7.

Lemma fold_min_aux : forall x  t xh fh gh, 
  x < n ->
    f x < fh ->
    fold_right fold_min (x, f x) ((xh, fh, gh) :: t) = 
    fold_right fold_min (xh, fh) t.
Proof.
 intros.
 unfold fold_min.
 induction t as [| a b].
 unfold fold_right.
 remember (blt_nat fh (f x)) as e.
 destruct e.
 reflexivity.
 apply blt_lt in H0.
 symmetry in Heqe.
-

Lemma arg_min_inequ :
  forall x, x < n /\
    (f x < g x) -> 
      (exists x, x < n /\ 
       f x < g x /\
       forall y, f y < f x -> f y >= g y).
Proof.
  intros.
  exists (project_1st (get_min_inequality f g x)).
  split.
  unfold get_min_inequality.
  set (l := filter filter_lt (eval f g x)).
  induction l as [|h t].
  simpl.
  apply H.
  set (m := fold_min h (x, f x)).
  unfold fold_min.
  compute.
  simpl. 

 decompose.
intuition.
  simpl.
*)