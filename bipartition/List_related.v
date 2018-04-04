Require Import Coq.Logic.Classical_Prop.

Load "Help_Lemmata".




Section List_related.

(* Same definition as in graphbasics, but for all types: 
   Remove the first element of the list*)
Definition cdr (X: Type) (vl : list X) : list X :=
  match vl with
  | nil => nil
  | x :: vl' => vl'
  end.

(* A sublist is right at the start of another list -- or not. *)
Fixpoint sub_starts_in_list (X : Type) (sublist superlist : list X) : Prop :=
  match sublist with
  |nil => True
  |a::tla => match superlist with
    |nil => False
    |b::tlb => (a = b) /\ (sub_starts_in_list X tla tlb)
    end
  end.

(* A sublist is somewhere in another list -- or not. *)
Fixpoint sub_in_list (X: Type) (sublist superlist : list X) : Set :=
  match sublist with
  |nil => True
  |a::tla => match superlist with
    |nil => False  
    |b::tlb => (sub_starts_in_list X sublist superlist) + (sub_in_list X sublist tlb)
    end
  end.

(* A list is only empty, iff the reversed list is empty. *)
Lemma rev_nil: forall (X: Type) (l : list X),
  rev l = nil <-> l = nil.
Proof.
  intros X l.
  split.
  induction l.
  reflexivity.
  intros.
  simpl in H.
  symmetry in H.
  apply app_cons_not_nil in H.
  inversion H.

  induction l.
  reflexivity.
  intros.
  rewrite H.
  reflexivity.
Qed.

(* You can just remove the first element of the first list, if the first list isn't empty. *)
Lemma cdr_app : forall (X: Type),
 forall vl vl' : list X, vl <> nil -> cdr X (vl ++ vl') = cdr X vl ++ vl'.
Proof.
        simple induction vl; simpl; intros.
        absurd (V_nil = V_nil); auto.

        trivial.
Qed.

(* If some element is in the list without its last element, it definitely is in the list itself. *)
Lemma cdr_rev: forall (X: Type) (x:X) (vl:list X),
  In x (cdr X (rev vl)) -> In x vl.
Proof.
  intros X x vl i.
  induction vl.
  simpl in i.
  inversion i.
  unfold In.
  simpl in i.
  destruct vl.
  simpl in i.
  inversion i.
  rewrite cdr_app in i.
  apply in_app_or in i.
  destruct i.
  right.
  apply IHvl.
  apply H.
  left.
  inversion H.
  apply H0.
  inversion H0.
  apply neq_symm.
  apply app_cons_not_nil.
Qed.

(* Like "cdr_rev": some element is in the list, it definitely is in the list with an added element. *)
Lemma cdr_rev2: forall (X: Type) (vl : list X) (x y : X),
  In x (cdr X (rev vl)) -> In x (cdr X (rev (y :: vl))).
Proof.
  intros X vl x y i.
  simpl.
  rewrite cdr_app.
  apply in_or_app.
  left.
  apply i.
  assert (vl = nil \/ vl <> nil).
  apply classic.
  destruct H.
  rewrite H in i.
  intuition.
  unfold not. intros. apply H.
  apply (rev_nil X).
  unfold V_nil in H0.
  apply H0.
Qed.

(* If you add an element y to a list with no x, and y is different from x,
   x won't be part of it now. *)
Lemma cdr_rev3: forall (X: Type) (vl : list X) (x y : X),
  ~ In x (cdr X (rev vl)) -> x <> y -> ~ In x (cdr X (rev (y::vl))).
Proof.
  intros X vl x y i xy.
  unfold not. intros.

  assert (vl = nil \/ vl <> nil).
  apply classic.
  destruct H0.
  rewrite H0 in H.
  inversion H.
  
  simpl in H.
  rewrite cdr_app in H.
  apply in_app_or in H.
  destruct H.
  apply i in H.
  inversion H.
  inversion H.
  intuition.
  intuition.
  unfold not.
  intros.
  unfold V_nil in H1.
  assert (rev vl = nil -> vl = nil).
  intros.
  induction vl.
  reflexivity.
  inversion H1.
  symmetry in H4.
  apply app_cons_not_nil in H4.
  inversion H4.
  apply H2 in H1.
  apply H0 in H1.
  inversion H1.
Qed.

(* An element is harder to find in a shorter list. *)
Lemma cdr_rev4: forall (X: Type) (vl : list X) (x y : X),
  ~ In x (cdr X (rev (y::vl))) -> ~ In x (cdr X (rev vl)).
Proof.
  intros X vl x y i.
  unfold not. intros.
  apply (cdr_rev2 X vl x y) in H.
  intuition.
Qed.

(* Can't be explained easier than with symbols in the next line. *)
Lemma cdr_rev5: forall (X: Type) (vl : list X) (x : X),
  cdr X (rev vl ++ x :: nil) = nil -> vl = nil.
Proof.
  intros X vl x cdrX.
  induction vl using rev_ind.
  reflexivity.
  rewrite rev_app_distr in cdrX.
  simpl in cdrX.
  apply app_eq_nil in cdrX.
  destruct cdrX.
  inversion H0.
Qed.

(* A sublist is still sublist when the superlist is appended. *)
Lemma sub_one_more: forall (X: Type) (sub super : list X) (a : X),
  sub_in_list X sub super -> sub_in_list X sub (a::super).
Proof.
  intros X sub super a sinl.
  destruct sub.
  reflexivity.
  unfold sub_in_list.
  right.
  apply sinl.
Qed.

(* If a sublist starts right away (subs) in a superlist, it's a sublist indeed. *)
Lemma subs_means_sub : forall (X: Type) (sub super : list X),
  sub_starts_in_list X sub super -> sub_in_list X sub super.
Proof.
  intros X sub super sinl.
  destruct sub. destruct super.
  reflexivity. reflexivity.
  destruct super. inversion sinl.
  unfold sub_in_list.
  left.
  inversion sinl.
  split.
  apply H.
  apply H0.
Qed.

(* A shorter sublist is still sublist. *)
Lemma sub_one_less: forall (X: Type) (sub super : list X) (a : X),
  sub_in_list X (a :: sub) super -> sub_in_list X sub super.
Proof.
  intros X sub super a sinl.
  induction super.
  inversion sinl.
  simpl in sinl.
  destruct sinl.
  destruct a1.
  apply subs_means_sub in H0.
  apply (sub_one_more X sub super a0) in H0.
  apply H0.
  apply IHsuper in s.
  apply (sub_one_more X sub super a0) in s.
  apply s.
Qed.

(* The empty list is always sublist. *)
Lemma sub_nil_super: forall (X: Type) (superlist : list X),
  sub_in_list X nil superlist.
Proof.
  intros X superlist.
  induction superlist.
  reflexivity.
  reflexivity.
Qed.

(* Sublists of empty superlist must be empty themselves. *)
Lemma sub_sub_nil: forall (X: Type) (sublist : list X),
  sub_in_list X sublist nil -> sublist = nil.
Proof.
  intros X sublist sinl.
  unfold sub_in_list in sinl.
  destruct sublist.
  reflexivity.
  inversion sinl.
Qed.

(* Sublists starting at the "beginning" of empty superlist must be empty themselves. *)
Lemma subs_sub_nil: forall (X: Type) (sublist : list X),
  sub_starts_in_list X sublist nil -> sublist = nil.
Proof.
  intros X sublist sinl.
  unfold sub_in_list in sinl.
  destruct sublist.
  reflexivity.
  inversion sinl.
Qed.

(* If x is in list l, there exist some pre-list and post-list, that together with x they form l
   and vice versa. *)
Lemma in_means_embedded : forall (X: Type)  (l : list X) (x : X),
  In x l <-> (exists (l1 l2 : list X), l = l1 ++ (x :: l2)).
Proof.
  intros X l.
  split.

  intros.
  induction l.
  inversion H.
  unfold In in H.
  destruct H.
  exists nil. exists l. rewrite H. reflexivity.
  apply IHl in H.
  destruct H. destruct H.
  exists (a :: x0). exists x1. rewrite H. reflexivity.

  intros.
  destruct H. destruct H.
  rewrite H.
  apply in_or_app.
  right.
  simpl.
  left.
  reflexivity.
Qed.

(* A sublist starts at itself appended by other lists. *)
Lemma subs_app3: forall (X: Type) (sub super : list X),
  sub_starts_in_list X sub (sub ++ super).
Proof.
  intros X sub super.
  induction sub.
  reflexivity.
  simpl.
  split.
  reflexivity.
  apply IHsub.
Qed.

(* Cut the first n elements off of a list. *)
Fixpoint cut (X: Type) (n : nat) (l : list X) : list X :=
  match n with
  |0 => l
  |S(x) => match l with
    |nil => nil
    |hd::tl => cut X x tl
    end
  end.

(* If you cut (length of list) elements off of a list, it becomes empty. *)
Lemma cut_1 : forall (X: Type) (sub : list X),
  cut X (length sub) sub = nil.
Proof.
  intros X sub.
  induction sub.
  reflexivity.
  simpl.
  apply IHsub.
Qed.

(* If you cut the first (length sub) elements of (sub ++ super), the list becomes only super *)
Lemma cut_3 : forall (X: Type) (sub super : list X),
  cut X (length sub) (sub ++ super) = super.
Proof.
  intros X sub super.
  induction sub.
  simpl. reflexivity.
  simpl. apply IHsub.
Qed.

(* If you cut any amount of elements off of an empty list, it remains empty. *)
Lemma cut_nil : forall (X: Type) (k :nat),
  cut X k nil = nil.
Proof.
  intros X k.
  induction k.
  reflexivity.
  simpl. reflexivity.
Qed.

(* If you cut less than some sublist, you can cut only from the sublist and "cut+append" becomes distributive. *)
Lemma cut_7 : forall (X: Type) (super rest rest2 : list X) (k : nat),
  k <= length super -> (cut X k (super ++ rest) = cut X k super ++ rest) -> (cut X k (super ++ rest2) = cut X k super ++ rest2).
Proof.
  intros X super.
  induction super.
  intros rest rest2 k kls cutk.
  inversion kls.
  reflexivity.
  intros rest rest2 k kls cutk.
  induction k.
  reflexivity.
  simpl in cutk.
  simpl in kls.
  assert (k <= length super).
  intuition.
  clear kls.
  apply (IHsuper rest rest2) in H.
  simpl.
  apply H.
  apply cutk.
Qed.

(* If you cut less than some sublist, you can cut only from the sublist and "cut+append" becomes distributive. *)
Lemma cut_4 : forall (X: Type) (k : nat) (super rest : list X),
  k <= length super -> cut X k (super ++ rest) = cut X k super ++ rest.
Proof.
  intros X k.
  induction k.
  intros super rest lek. reflexivity.
  intros super rest lek.
  inversion lek.
  rewrite H0. rewrite cut_3. rewrite cut_1. reflexivity.
  assert (k <= length super).
  intuition.
  clear H. clear H0. clear m.
  induction rest.

  rewrite app_nil_r. rewrite app_nil_r. reflexivity.
  apply (cut_7 X super rest (a::rest)) in IHrest.
  apply IHrest.
  apply lek.
Qed.

(* A superlist is longer than any starting sublist. *)
Lemma super_longer : forall (X: Type) (sub super rest : list X),
  super = sub ++ rest -> length sub <= length super.
Proof.
  intros X sub super rest ssr.
  rewrite ssr.
  rewrite app_length.
  intuition.
Qed.

(* A starting sublist is either the complete list or starting in the list without its last element. *)
Lemma subs_cons : forall (X: Type) (super sub :list X) (r : X),
  sub_starts_in_list X sub (super ++ r :: nil) -> (sub = super ++ r :: nil \/ sub_starts_in_list X sub super).
Proof.
  intros X super.
  induction super.
  intros sub r ssil.
  simpl.
  destruct sub. right. reflexivity.

  inversion ssil.
  apply subs_sub_nil in H0. rewrite H0. left. rewrite H. reflexivity.
  
  intros sub r ssil.
  destruct sub. right. reflexivity.

  inversion ssil.
  rewrite H. simpl.
  apply IHsuper in H0.
  destruct H0.
  rewrite H0.
  left. reflexivity.
  right.
  split. reflexivity. apply H0.
Qed.

(* There is always an ending sublist after the starting sublist, so that both sublists form the superlist. *)
Lemma subs_app : forall (X: Type) (sub super : list X),
  sub_starts_in_list X sub super -> {super2 : list X & super = sub ++ super2}.
Proof.
  intros X sub super sinl.
  exists (cut X (length sub) super).

  induction super using rev_ind.
  apply subs_sub_nil in sinl. rewrite sinl.
  reflexivity.
  apply subs_cons in sinl.
  destruct sinl.
  rewrite <- H.
  rewrite cut_1.
  rewrite app_nil_r. reflexivity.
  apply IHsuper in H.
  assert (H' := H).
  apply super_longer in H'.
  rewrite cut_4.
  rewrite app_assoc.
  rewrite <- H.
  reflexivity.
  apply H'.
Qed.

(* For all parts of a starting sublist, there is an ending list, so that both sublists form the superlist together. *)
Lemma subs_app2 : forall (X: Type) (sub1 sub2 super : list X),
  sub_starts_in_list X (sub1 ++ sub2) super -> {super2 : list X & super = sub1 ++ super2}.
Proof.
  intros X s1 s2 super sinl.
  apply subs_app in sinl.
  destruct sinl.
  exists (s2 ++ x). rewrite <- app_assoc in e. apply e.
Qed.

(* If some sublist has the length of the superlist, they are the same. *)
Lemma subs_lengths_eq: forall (X: Type) (superlist sublist : list X),
  length sublist = length superlist -> sub_starts_in_list X sublist superlist -> sublist = superlist.
Proof.
  intros X super.
  induction super using rev_ind.
  intros sub lengths sssil.
  apply subs_sub_nil in sssil. apply sssil.
  intros sub lengths sssil.
  apply subs_app in sssil.
  destruct sssil.
  rewrite e.
  destruct x0.
  rewrite app_nil_r. reflexivity.

  rewrite e in lengths.
  rewrite app_length in lengths. simpl in lengths.
  rewrite plus_comm in lengths. simpl in lengths.
  assert (forall n m:nat, n <> S(m + n)).
  intros.
  induction n.
  intuition.
  intuition.
  apply (H (length sub)) in lengths.
  intuition.
Qed.

(* If you append a starting sublist and superlist at the beginning, 
   the newly formed lists are still starting sublist and superlists and vice versa. *)
Lemma subs_minus : forall (X: Type) (s1 s2 s3 : list X),
  sub_starts_in_list X s2 s3 <-> sub_starts_in_list X (s1 ++ s2) (s1 ++ s3).
Proof.
  intros X s1 s2 s3.
  split.

  intros.
  induction s1.
  simpl. apply H.
  simpl.
  split.
  reflexivity.
  apply IHs1.

  intros.
  induction s1.
  simpl. apply H.
  simpl in H.
  destruct H.
  apply IHs1.
  apply H0.
Qed.

(* Elements of sublists are in the superlist as well. *)
Lemma subs_for_all : forall (X: Type) (sub super : list X),
  sub_starts_in_list X sub super -> (forall x : X, In x sub -> In x super).
Proof.
  intros X sub super sss x i.
  apply in_means_embedded in i.
  destruct i.
  destruct H.
  rewrite H in sss. assert (sss' := sss). apply subs_app2 in sss.
  destruct sss.
  rewrite e in sss'.
  rewrite e.
  apply <- subs_minus in sss'.
  destruct x2.
  inversion sss'.
  inversion sss'.
  apply in_or_app.
  right.
  unfold In.
  left.
  symmetry.
  apply H0.
Qed.

(* Somewhere in the superlist, the sublist must actually start. *)
Theorem sub_means_exists_subs : forall (X: Type) (sub super : list X),
  sub_in_list X sub super -> (exists (s1 s2 : list X), super = s1 ++ s2 /\ sub_starts_in_list X sub s2).
Proof.
  intros X sub super sinl.
  induction super.
  exists nil. exists nil. split. reflexivity. apply sub_sub_nil in sinl. rewrite sinl. reflexivity.

  destruct sub.
  exists nil. exists (a :: super). split. reflexivity. reflexivity.

  unfold sub_in_list in sinl.
  destruct sinl.
  destruct s.
  rewrite H. exists nil. exists (a :: super). split. reflexivity. 
  apply (subs_minus X (a :: nil) sub super) in H0. rewrite <- app_comm_cons in H0. rewrite <- app_comm_cons in H0.
  rewrite app_nil_l in H0. rewrite app_nil_l in H0. apply H0.

  apply IHsuper in s.
  destruct s.
  destruct H.
  exists (a :: x0). exists x1. destruct H. split. rewrite H. reflexivity. apply H0.
Qed.

(* Elements of sublists are in the superlist as well. *)
Lemma sub_for_all : forall (X: Type) (sub super : list X),
  sub_in_list X sub super -> (forall x : X, In x sub -> In x super).
Proof.
  intros X sub super sss x i.
  apply sub_means_exists_subs in sss.
  destruct sss.
  destruct H.
  destruct H.
  rewrite H.
  apply (subs_for_all X sub x1 H0 x) in i.
  apply in_or_app.
  right.
  apply i.
Qed.

(* If there is one element in a sublist, that is not in the superlist, it cannot be a sublist. *)
Lemma sub_exists_one : forall (X: Type) (sub super : list X),
  (exists x : X, In x sub /\ ~ In x super) -> sub_in_list X sub super -> False.
Proof.
  intros X sub super ex.
  destruct ex.
  destruct H.
  unfold not.
  intros.
  apply (sub_for_all X sub super H1 x) in H.
  apply H0 in H.
  inversion H.
Qed.

(* Either the sublist starts right away or it is in there somewhere later. *)
Lemma sub_starts_or_in_rest : forall (X: Type) (sublist superlist : list X) (a : X),
  sub_in_list X sublist (a :: superlist) -> (sub_starts_in_list X sublist (a :: superlist)) + sub_in_list X sublist superlist.
Proof.
  intros X sublist superlist a sinl.
  destruct sublist.
  left.
  reflexivity.
  unfold sub_in_list in sinl.
  destruct sinl.
  destruct s.
  left.
  simpl.
  split.
  apply H.
  apply H0.
  right.
  apply s.
Qed.

(* Main Lemma: there must be a sublist preceding and a sublist following the actual sublist in the superlist. *)
Lemma sub_exists_embedding: forall (X: Type) (sublist superlist : list X),
  sub_in_list X sublist superlist -> (exists (l1 l3 : list X), superlist = l1 ++ sublist ++ l3).
Proof.
  intros X sublist superlist sinl.
  induction superlist.
  destruct sublist.
  exists nil. exists nil. reflexivity.
  inversion sinl.

  apply sub_starts_or_in_rest in sinl.
  destruct sinl.
  apply subs_app in s.
  destruct s.
  rewrite e. exists nil. exists x. reflexivity.
  apply IHsuperlist in s.
  destruct s. destruct H.
  rewrite H. exists (a :: x). exists x0. reflexivity.
Qed.

(* As the function "last" gets a dummy return for empty lists - if the list is not empty
   the dummy doesnt matter. *)
Lemma last_is_last: forall (T: Type) (l : list T) (x y : T),
  l <> nil -> last (l) x = last (l) y.
Proof.
  intros T l x y lnil.
  induction l.
  intuition.

  destruct l.
  reflexivity.

  simpl. simpl in IHl. apply IHl.
  intuition. inversion H.
Qed.

End List_related.