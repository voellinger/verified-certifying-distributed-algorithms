Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.Even.

(* Load "/home/lanpirot/Uni/COQ/verified-certifying-distributed-algorithms/leader-election/composition_witness_prop_leader_election". *)


Section Help.

Definition Component := Vertex.





Lemma Path_isa_walk: 
  forall (v: V_set) (a: A_set) (x y : Vertex) (vl : V_list) (el : E_list),
  Path v a x y vl el -> Walk v a x y vl el.
Proof.
  intros.
  apply Path_isa_trail in H.
  apply Trail_isa_walk in H.
  apply H.
Qed.

Lemma Path_appended_isa_walk :
 forall (v: V_set) (a: A_set) (x y z : Vertex) (vl vl' : V_list) (el el' : E_list),
 Path v a x y vl el ->
 Path v a y z vl' el' -> Walk v a x z (vl ++ vl') (el ++ el').
Proof.
        intros v a x0 y0 z0 vl vl' el el' Hw; elim Hw; simpl; intros.
        apply Path_isa_walk in H.
        trivial.

        apply W_step.
        apply H.
        apply H0.
        apply v0.
        apply a0.
Qed.



Definition append_w (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (x y z:Vertex) (w1: Walk v a x y vl el) (w2: Walk v a y z vl' el') :=
  Walk v a x z (vl ++ vl') (el ++ el').

Definition append_p (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (x y z:Vertex) (p1: Path v a x y vl el) (p2: Path v a y z vl' el') :=
  Walk v a x z (vl ++ vl') (el ++ el').

Lemma Path_append (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (x y z:Vertex) (p1: Path v a x y vl el) (p2: Path v a y z vl' el'):
 Walk v a x z (vl ++ vl') (el ++ el') = append_p v a vl vl' el el' x y z p1 p2.
Proof.
  intros.
  unfold append_p.
  reflexivity.
Qed.

Function length_w {v: V_set} {a: A_set} {vl : V_list} {el: E_list} {c1 c2: Component} (p: Walk v a c1 c2 vl el) := length vl.
Function length_p {v: V_set} {a: A_set} {vl : V_list} {el: E_list} {c1 c2: Component} (p: Path v a c1 c2 vl el) := length vl.

Lemma Path_append_lengthsum (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (x y z:Vertex) (p1: Path v a x y vl el) (p2: Path v a y z vl' el') (p3: append_p v a vl vl' el el' x y z p1 p2):
  length_p p1 + length_p p2 = length_w p3.
Proof.
  intros.
  unfold length_p.
  unfold length_w.
  symmetry.
  rewrite app_length.
  reflexivity.
Qed.

Lemma W_inel_ina :
 forall (v: V_set) (a: A_set) (x y : Component) (vl : V_list) (el : E_list),
 Walk v a x y vl el ->
 forall x' y' : Component, In (E_ends x' y') el -> a (A_ends x' y').
Proof.
  intros v a x0 y0 vv e w; elim w; intros.
  inversion H.

  inversion H0.
  inversion H1.
  rewrite <- H3; rewrite <- H4; trivial.

  auto.
Qed.

Lemma W_endx_inv :
 forall (v: V_set) (a: A_set) (x y : Component) (vl : V_list) (el : E_list), Walk v a x y vl el -> v x.
Proof.
        intros. inversion H. apply H0. apply H1.
Qed.

Lemma W_endy_inv :
 forall (v: V_set) (a: A_set) (x y : Component) (vl : V_list) (el : E_list), Walk v a x y vl el -> v y.
Proof.
        intros. elim H. intros. apply v0. intros. apply H0.
Qed.

Lemma S_even : forall n: nat, odd (S n) -> even n.
Proof.
  intros.
  inversion H.
  apply H1.
Qed.

Lemma S_odd : forall n: nat, even (S n) -> odd n.
Proof.
  intros.
  inversion H.
  apply H1.
Qed.

Lemma tree_walk : forall (v: V_set) (a : A_set) (t : Tree v a) (x y: Component),
  v x -> v y -> {vl : V_list & {el : E_list & Walk v a x y vl el}}.
Proof.
  intros.
  apply Tree_isa_connected in t.
  apply Connected_walk.
  apply t.
  apply H.
  apply H0.
Qed.


Lemma v_not_empty : forall (v:V_set) (a:A_set) (c:Connected v a),
  exists (x:Component), v x.
Proof.
  intros v a c.
  assert (c':=c).
  induction c.
  exists x.
  unfold V_single.
  intuition.

  exists x.
  apply V_in_right.
  apply v0.
  

  exists x.
  apply v0.
  
  rewrite <- e.
  apply IHc.
  apply c.
Qed.


Variable root : Component.
Axiom nearly_all_connected_rooted': forall (v:V_set) (a:A_set) (x : Component) (g:Connected v a),
  v x -> v root.
(* Axiom root_is_unique ?? *)

Lemma nearly_all_trees_rooted: forall (v:V_set) (a:A_set) (x:Component) (t: Tree v a),
  v x -> v root.
Proof.
  intros v a x0 t vx.
  apply Tree_isa_connected in t.
  apply (nearly_all_connected_rooted' v a) in vx.
  apply vx.
  apply t.
Qed.

Lemma all_trees_rooted: forall (v:V_set) (a:A_set) (t: Tree v a),
  v root.
Proof.
  intros v a t.
  assert (exists (x : Component), v x).
  apply (v_not_empty v a).
  apply Tree_isa_connected in t.
  apply t.
  destruct H.
  apply (nearly_all_trees_rooted v a x t).
  apply H.
Qed.

Lemma E_eq2 : forall (e1 e2 : Edge),
  E_eq e1 e2 -> E_eq e2 e1.
Proof.
  intros e1 e2 eq.
  inversion eq.
  apply E_refl.
  apply E_rev.
Qed.

Lemma neq_symm: forall (X : Type) {p q: list X}, p <> q -> q <> p.
Proof.
  intros X p q pq.
  unfold not.
  intros.
  apply pq.
  symmetry.
  apply H.
Qed.

Lemma E_rev_cons: forall(u:Edge)(el:E_list),
  E_reverse (u :: el) = (E_reverse el) ++ (E_reverse (u :: nil)).
Proof.
  intros u el.
  induction el.
  simpl.
  reflexivity.
  destruct u.
  destruct a.
  unfold E_reverse.
  reflexivity.
Qed.


Lemma E_rev_in2: forall (x y : Vertex) (el : E_list),
  In (E_ends x y) (E_reverse el) -> In (E_ends y x) el.
Proof.
  intros x y el i.
  induction el.
  simpl in i.
  inversion i.

  destruct a.
  simpl.
  simpl in i.
  apply in_app_or in i.
  destruct i.
  right.
  apply IHel.
  apply H.
  left.
  unfold In in H.
  destruct H.
  inversion H.
  reflexivity.
  inversion H.
Qed.

Lemma E_rev_in: forall (u: Edge) (x y : Vertex) (el : E_list),
(forall v:Edge, In v el -> ~ E_eq v (E_ends x y)) -> In u (E_reverse el) -> ~ E_eq u (E_ends y x).
Proof.
  intros u x y el vv uu.
  unfold not.
  intros.
  destruct u.
  apply E_rev_in2 in uu.
  apply vv in uu.
  inversion H.
  rewrite H2 in uu.
  rewrite H3 in uu.
  assert (E_eq (E_ends x y) (E_ends x y)).
  apply E_refl.
  apply uu in H1.
  inversion H1.
  rewrite H3 in uu.
  rewrite H4 in uu.
  assert (E_eq (E_ends y x) (E_ends x y)).
  apply E_rev.
  apply uu in H0.
  inversion H0.
Qed.

Lemma E_rev_len: forall(el:E_list),
  length (E_reverse el) = length el.
Proof.
  intros el.
  induction el.
  reflexivity.
  destruct a.
  simpl.
  rewrite app_length.
  simpl.
  rewrite IHel.
  apply plus_comm.
Qed.

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

Definition cdr (X: Type) (vl : list X) : list X :=
  match vl with
  | nil => nil
  | x :: vl' => vl'
  end.

Lemma cdr_app : forall (X: Type),
 forall vl vl' : list X, vl <> nil -> cdr X (vl ++ vl') = cdr X vl ++ vl'.
Proof.
        simple induction vl; simpl; intros.
        absurd (V_nil = V_nil); auto.

        trivial.
Qed.

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


Lemma cdr_rev4: forall (X: Type) (vl : list X) (x y : X),
  ~ In x (cdr X (rev (y::vl))) -> ~ In x (cdr X (rev vl)).
Proof.
  intros X vl x y i.
  unfold not. intros.
  apply (cdr_rev2 X vl x y) in H.
  intuition.
Qed.

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

Fixpoint sub_starts_in_list (X : Type) (sublist superlist : list X) : Prop :=
  match sublist with
  |nil => True
  |a::tla => match superlist with
    |nil => False
    |b::tlb => (a = b) /\ (sub_starts_in_list X tla tlb)
    end
  end.

Fixpoint sub_in_list (X: Type) (sublist superlist : list X) : Set :=
  match sublist with
  |nil => True
  |a::tla => match superlist with
    |nil => False  
    |b::tlb => (sub_starts_in_list X sublist superlist) + (sub_in_list X sublist tlb)
    end
  end.

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

Lemma sub_nil_super: forall (X: Type) (superlist : list X),
  sub_in_list X nil superlist.
Proof.
  intros X superlist.
  induction superlist.
  reflexivity.
  reflexivity.
Qed.

Lemma sub_sub_nil: forall (X: Type) (sublist : list X),
  sub_in_list X sublist nil -> sublist = nil.
Proof.
  intros X sublist sinl.
  unfold sub_in_list in sinl.
  destruct sublist.
  reflexivity.
  inversion sinl.
Qed.

Lemma subs_sub_nil: forall (X: Type) (sublist : list X),
  sub_starts_in_list X sublist nil -> sublist = nil.
Proof.
  intros X sublist sinl.
  unfold sub_in_list in sinl.
  destruct sublist.
  reflexivity.
  inversion sinl.
Qed.

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

Fixpoint cut (X: Type) (n : nat) (l : list X) : list X :=
  match n with
  |0 => l
  |S(x) => match l with
    |nil => nil
    |hd::tl => cut X x tl
    end
  end.

Lemma cut_1 : forall (X: Type) (sub : list X),
  cut X (length sub) sub = nil.
Proof.
  intros X sub.
  induction sub.
  reflexivity.
  simpl.
  apply IHsub.
Qed.

Lemma cut_3 : forall (X: Type) (sub super : list X),
  cut X (length sub) (sub ++ super) = super.
Proof.
  intros X sub super.
  induction sub.
  simpl. reflexivity.
  simpl. apply IHsub.
Qed.

Lemma cut_nil : forall (X: Type) (k :nat),
  cut X k nil = nil.
Proof.
  intros X k.
  induction k.
  reflexivity.
  simpl. reflexivity.
Qed.


Lemma cut_7 : forall (X: Type) (super rest fest : list X) (k : nat),
  k <= length super -> (cut X k (super ++ rest) = cut X k super ++ rest) -> (cut X k (super ++ fest) = cut X k super ++ fest).
Proof.
  intros X super.
  induction super.
  intros rest fest k kls cutk.
  inversion kls.
  reflexivity.
  intros rest fest k kls cutk.
  induction k.
  reflexivity.
  simpl in cutk.
  simpl in kls.
  assert (k <= length super).
  intuition.
  clear kls.
  apply (IHsuper rest fest) in H.
  simpl.
  apply H.
  apply cutk.
Qed.


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

Lemma aux : forall (X: Type) (sub super rest : list X),
  super = sub ++ rest -> length sub <= length super.
Proof.
  intros X sub super rest ssr.
  rewrite ssr.
  rewrite app_length.
  intuition.
Qed.

Lemma aux2 : forall (X: Type) (super sub :list X) (r : X),
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

Lemma subs_app : forall (X: Type) (sub super : list X),
  sub_starts_in_list X sub super -> (exists (super2 : list X), super = sub ++ super2).
Proof.
  intros X sub super sinl.
  exists (cut X (length sub) super).

  induction super using rev_ind.
  apply subs_sub_nil in sinl. rewrite sinl.
  reflexivity.
  apply aux2 in sinl.
  destruct sinl.
  rewrite <- H.
  rewrite cut_1.
  rewrite app_nil_r. reflexivity.
  apply IHsuper in H.
  assert (H' := H).
  apply aux in H'.
  rewrite cut_4.
  rewrite app_assoc.
  rewrite <- H.
  reflexivity.
  apply H'.
Qed.



Lemma subs_app2 : forall (X: Type) (sub1 sub2 super : list X),
  sub_starts_in_list X (sub1 ++ sub2) super -> (exists (super2 : list X), super = sub1 ++ super2).
Proof.
  intros X s1 s2 super sinl.
  apply subs_app in sinl.
  destruct sinl.
  exists (s2 ++ x). rewrite H. rewrite <- app_assoc. reflexivity.
Qed.


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



Lemma subs_for_all : forall (X: Type) (sub super : list X),
  sub_starts_in_list X sub super -> (forall x : X, In x sub -> In x super).
Proof.
  intros X sub super sss x i.
  apply in_means_embedded in i.
  destruct i.
  destruct H.
  rewrite H in sss. assert (sss' := sss). apply subs_app2 in sss.
  destruct sss.
  rewrite H0 in sss'.
  rewrite H0.
  apply <- subs_minus in sss'.
  destruct x2.
  inversion sss'.
  inversion sss'.
  apply in_or_app.
  right.
  unfold In.
  left.
  symmetry.
  apply H1.
Qed.

Lemma sub_means_exists_subs : forall (X: Type) (sub super : list X),
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
  rewrite H. exists nil. exists x. reflexivity.
  apply IHsuperlist in s.
  destruct s. destruct H.
  rewrite H. exists (a :: x). exists x0. reflexivity.
Qed.

Lemma Path_cons : forall (v: V_set) (a: A_set) (x y z: Vertex) (vl : V_list) (el : E_list),
  v z -> a (A_ends y z) -> (x = y -> vl = V_nil) -> y <> z -> ~ In z vl -> (forall u : Edge, In u el -> ~ E_eq u (E_ends y z)) ->
  Path v a x y vl el -> Path v a x z (vl ++ z :: nil) (el ++ (E_ends y z) :: nil).
Proof.
  intros v a x y z vl el vz ayz xy yz zvl uu p.

  induction p.
  simpl.
  apply P_step.
  apply P_null.
  apply vz.
  apply v0.
  apply ayz.
  apply yz.
  unfold not.
  intros.
  inversion H.
  intros.
  inversion H.
  apply uu.

  simpl.
  apply P_step.
  apply IHp.
  apply ayz.
  intros.
  rewrite <- H in p.
  inversion p.
  reflexivity.
  apply P_iny_vl in p.
  apply n0 in p.
  inversion p.
  symmetry in H9.
  unfold not.
  intros.
  rewrite H11 in H9.
  inversion H9.
  apply yz.
  unfold not.
  intros.
  apply zvl.
  unfold In.
  right.
  apply H.
  intros.
  apply uu.
  unfold In.
  right.
  apply H.
  apply v0.
  apply a0.
  apply n.
  unfold not.
  intros.
  apply in_app_or in H.
  destruct H.
  apply n0 in H.
  inversion H.
  inversion H.
  rewrite H0 in zvl.
  apply zvl.
  simpl.
  left.
  reflexivity.
  inversion H0.
  intros.
  apply in_app_or in H.
  destruct H.
  apply e in H.
  apply xy in H.
  inversion H.
  inversion H.
  symmetry.
  apply H0.
  inversion H0.
  intros.
  apply in_app_or in H.
  destruct H.
  apply n1 in H.
  apply H.
  destruct H.
  unfold not.
  intros.
  rewrite <- H in H0.
  apply E_eq2 in H0.
  apply uu in H0.
  inversion H0.
  unfold In.
  left.
  reflexivity.
  inversion H.
Qed.

Lemma Path_append2 : forall (v: V_set) (a: A_set) (x y z : Vertex) (vl vl' : V_list) (el el' : E_list),
  (forall (c: Component), In c vl -> ~ In c vl') -> (forall u u': Edge, In u el -> In u' el' -> ~ E_eq u' u) ->
  (x = y -> vl = V_nil \/ vl' = V_nil) -> 
  Path v a x y vl el ->  Path v a y z vl' el' -> (In x vl' -> x = z) ->
  Path v a x z (vl ++ vl') (el ++ el').
Proof.
  intros v a x y z vl vl' el el' H0 H3 c1 p1 p2 lasso.



  induction p1.
  simpl.
  apply p2.


  simpl.
  apply P_step.
  apply IHp1.
  intros.
  apply H0.
  unfold In.
  right.
  apply H.


  intros.
  apply H3.
  unfold In.
  right.
  apply H.
  apply H1.

  intros.
  rewrite <- H in p1.
  destruct vl.
  left.
  reflexivity.

  apply P_iny_vl in p1.
  intuition.
  unfold not.
  intros.
  inversion H1.

  apply p2.


  intros.
  apply (H0 y) in H.
  inversion H.
  unfold In.
  left.
  reflexivity.




  apply v0.
  apply a0.
  apply n.
  unfold not.
  intros.
  apply in_app_or in H.
  destruct H.
  intuition.
  unfold not in H0.
  apply (H0 y).
  simpl.
  left.
  reflexivity.
  apply H.

  intros.
  apply in_app_or in H.
  destruct H.
  apply e in H.
  assert (H10 := H).
  apply c1 in H.
  destruct H.
  inversion H.
  rewrite <- H10 in p2.
  rewrite H in p2.
  inversion p2.
  reflexivity.

  
  apply lasso in H.
  inversion H.
  reflexivity.
  
  intros.
  apply in_app_or in H.
  destruct H.
  assert (In u (E_ends x y :: el)).
  unfold In.
  right.
  apply H.
  apply n1.
  apply H.

  apply (H3 (E_ends x y) u).
  unfold In.
  left.
  reflexivity.
  apply H.
Qed.

Lemma P_y_not_in_cdrrevvl : forall (v: V_set) (a:A_set) (x y : Vertex) (vl : V_list) (el : E_list),
  Path v a x y vl el -> ~ In y (cdr Vertex (rev vl)).
Proof.
  intros v a x y vl el p.

  unfold not.
  intros.
  induction p.
  simpl in H.
  inversion H.
  apply IHp.

  apply (cdr_rev3 Vertex vl z y) in IHp.
  apply IHp in H.
  inversion H.
  unfold not.
  intros.
  rewrite H0 in p. rewrite H0 in e. rewrite H0 in IHp. rewrite H0 in H. clear H0. clear z.
  inversion p.
  rewrite <- H3 in H.
  simpl in H.
  inversion H.
  apply P_iny_vl in p.
  apply n0 in p.
  inversion p.
  rewrite <- H9.
  apply neq_symm.
  apply nil_cons.
Qed.


Lemma P_x_not_in_cdrrevvl : forall (v: V_set) (a:A_set) (x y : Vertex) (vl : V_list) (el : E_list),
  Path v a x y vl el -> ~ In x (cdr Vertex (rev vl)).
Proof.
  intros v a x y vl el p.
  assert (x = y \/ x <> y).
  apply classic.
  destruct H.
  rewrite H.
  apply (P_y_not_in_cdrrevvl v a x y vl el p).
  unfold not. intros.
  induction p.
  inversion H0.
  apply cdr_rev in H0.
  unfold In in H0.
  destruct H0.
  intuition.
  apply e in H0.
  intuition.
Qed.

Lemma Path_reverse :
 forall (v: V_set) (a: A_set) (x y : Vertex) (vl : V_list) (el : E_list) (g: Graph v a),
 Path v a x y vl el -> Path v a y x (cdr Vertex (rev (x :: vl))) (E_reverse el).
Proof.
  intros v a x y vl el g p.

  induction p.
  simpl.
  apply P_null.
  apply v0.
  

  simpl.
  rewrite cdr_app.
  apply (Path_cons).
  apply v0.
  apply (G_non_directed v a g) in a0.
  apply a0.
  intros.
  rewrite H in p.
  inversion p.
  reflexivity.
  apply P_iny_vl in p.
  apply n0 in p.
  inversion p.
  unfold not.
  intros.
  rewrite H11 in H9.
  inversion H9.
  auto.

  unfold not.
  intros.
  rewrite cdr_app in H.
  apply in_app_or in H.
  destruct H.
  assert (Path v a x z (y :: vl) ((E_ends x y)::el)).
  apply P_step.
  apply p.
  apply v0.
  apply a0.
  apply n.
  apply n0.
  apply e.
  apply n1.
  apply (P_x_not_in_cdrrevvl v a x z) in H0.
  apply H0.
  simpl.
  rewrite cdr_app.
  apply in_or_app.
  left.
  apply H.
  unfold not.
  intros.
  rewrite H1 in H.
  simpl in H.
  inversion H.


  inversion H.
  symmetry in H0.
  apply n in H0.
  inversion H0.
  inversion H0.
  destruct vl.
  simpl in H.
  inversion H.
  apply neq_symm.
  apply app_cons_not_nil.
  intros.
  apply (E_rev_in u x y el).
  apply n1.
  apply H.
  apply IHp.
  apply neq_symm.
  apply app_cons_not_nil.
Qed.

(*

if two paths a and b both from x to y are different, then there exist two completely different sub_paths from x' to y':
a = x...x'...y'...y = vlax vla vlay
b = x...x'...y'...y = vlbx vlb vlby
and vla completely different from vlb. 

vla (rev vlb) make a closed_path/cycle, therefore vla and vlb = nil. This holds for all vla, vlb. Therefore a = b.

*)
Definition E_ends_at_y (v: Vertex) (e: Edge) :=
  match e with
  (E_ends x y) =>  y = v
  end.

Locate "{".

(* Definition subpath (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (x y x' y':Vertex) (p: Path v a x y vl el) :=
  
  sub_in_list Vertex vl' vl + sub_in_list Edge el' el + {vl = vl'}. *)



Definition subpath (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (x y x' y':Vertex) (p: Path v a x y vl el) :=
  {vl' = nil /\ el' = nil /\ x' = y' /\ In x' (x :: vl)}
  +
  {vl' <> nil /\ el' <> nil /\ hd (E_ends x x) el' = E_ends x' (hd x vl') /\ y' = last vl' x /\ E_ends_at_y y' (last el' (E_ends x x))}.

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


(* Definition subpath (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (x y x' y':Vertex) (p: Path v a x y vl el) :=
  
  (vl' = nil /\ el' = nil /\ x' = y' /\ In x' (x :: vl)) \/ 
  (sub_in_list Vertex vl' vl /\ sub_in_list Edge el' el /\ vl' <> nil /\
   hd (E_ends x x) el' = E_ends x' (hd x vl') /\ y' = last vl' x /\ E_ends_at_y y' (last el' (E_ends x x))).
 *)
Lemma subpath_is_a_path : forall (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (x y x' y':Vertex) (p: Path v a x y vl el),
  forall (s1 : sub_in_list Vertex vl' vl) (s2 : sub_in_list Edge el' el),
  subpath v a vl vl' el el' x y x' y' p -> Path v a x' y' vl' el'.
Proof.
  intros v a vl vl' el el' x y x' y' p s1 s2 sp.
  assert (pp := p).
  induction p.
  apply sub_sub_nil in s1.
  unfold subpath in sp.

  destruct sp.
  destruct a0.
  destruct H0.
  destruct H1.
  rewrite H1. rewrite H. rewrite H0.
  apply P_null.
  inversion H2.
  rewrite <- H1. rewrite <- H3. apply v0.
  inversion H3.

  intuition.


  unfold subpath in sp.
  intuition.
  rewrite H1. rewrite H. rewrite H0.
  apply P_null.
  rewrite <- H0.
  inversion H3. 
  rewrite <- H2. apply v0.
  inversion H2.
  rewrite <- H4. 
  assert (ppp := p). apply (P_endx_inv) in ppp. apply ppp.
  assert (ppp := p). apply (P_invl_inv v a y z vl el ppp) in H4. apply H4.


  apply IHp.
  admit. admit.
  unfold subpath.
  destruct vl'. intuition.
  destruct el'. intuition.
  right. intuition.
  rewrite (last_is_last Vertex (v1 :: vl') y x).
  apply H2. intuition.
  rewrite (last_is_last Edge (e0 :: el') (E_ends y y) (E_ends x x)).
  apply H4. intuition.
  apply p.
Qed.
  







  intros v a vl vl' el el' x y x' y' p s1 s2 sp.
  unfold subpath in sp.
  destruct sp.
  destruct a0.
  destruct H0.
  destruct H1.
  rewrite H1. rewrite H. rewrite H0.
  apply P_null.
  assert (pp := p).
  apply P_endx_inv in p.
  rewrite <- H1. inversion H2. rewrite <- H3.
  apply p.
  apply (P_invl_inv v a x y vl el pp) in H3.
  apply H3.


  intuition.
  (* assert (el' <> nil).
  destruct vl'.
  intuition.
  destruct el'.
  simpl in H1.
  inversion H1.
  simpl in H3.
  inversion p.
  unfold V_nil in H8.
  rewrite <- H8 in s1.
  inversion s1.
  rewrite <- H5 in s1.
  rewrite <- H4 in s1.
  specialize (sub_for_all Vertex (x :: vl') vl s1).
  intros.
  specialize (H16 x).
  assert (In x (x :: vl')).
  simpl. left. reflexivity.
  apply H16 in H17.
  apply (P_when_cycle v a x y vl el p) in H17.
  rewrite H17 in p.
  assert (Cycle v a y y vl el p).
  reflexivity. *)
  


  induction p.
  apply sub_sub_nil in s1.
  apply H in s1.
  intuition.

  destruct vl'.
  intuition.
  destruct el'.
  intuition.
  simpl in H0.
  destruct e0.

  clear H1. clear H.
  apply IHp.
  simpl in s1. destruct s1.
  destruct a1.
  rewrite H in H0. rewrite H in H2. rewrite H in IHp. rewrite H. clear H. clear v1.
  inversion H0. clear H0. rewrite H3 in s2. rewrite H3 in H4. rewrite H3 in IHp. 
  rewrite H5 in s2. rewrite H5 in H4. rewrite H5 in IHp. clear H3. clear H5. clear v2. clear v3.
  
  admit.
  apply s.
  simpl in s2. destruct s2.
  admit.
  apply s.
  simpl. apply H0.
  rewrite (last_is_last Vertex (v1 :: vl') x y) in H2.
  apply H2.
  intuition. inversion H.
  rewrite (last_is_last Edge (E_ends v2 v3 :: el') (E_ends x x) (E_ends y y)) in H4.
  apply H4.
  intuition. inversion H.
Qed.




(* two paths from x1 to y1 that don't share any inner nodes (one path might be from y1 to x1) *)
Definition path_different1 (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (x1 x2 y1 y2:Vertex) (p1: Path v a x1 y1 vl el) (p2: Path v a x2 y2 vl' el') :=
  x1 <> y1 /\ x1 = x2 /\ y1 = y2 /\ (forall (vv : Vertex), In vv vl -> ~ In vv (rev (cdr Vertex (rev (x2 :: vl'))))) /\
  (forall u u' : Edge, In u el -> In u' (E_reverse el') -> ~ E_eq u' u).

Definition path_different2 (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (x1 x2 y1 y2:Vertex) (p1: Path v a x1 y1 vl el) (p2: Path v a x2 y2 vl' el') :=
  x1 <> y1 /\ x1 = y2 /\ y1 = x2 /\ (forall (vv : Vertex), In vv vl -> ~ In vv vl') /\
  (forall u u' : Edge, In u el -> In u' el' -> ~ E_eq u' u).

(* Definition path_different2 (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (x y:Vertex) (p1: Path v a x y vl el) (p2: Path v a x y vl' el') :=
  forall u u' : Edge, In u el -> In u' (E_reverse el') -> ~ E_eq u' u.

Lemma path_different_is_path_different2 : forall (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (x y:Vertex) (p1: Path v a x y vl el) (p2: Path v a x y vl' el'),
  path_different v a vl vl' el el' x y p1 p2 (* < *)-> path_different2 v a vl vl' el el' x y p1 p2.
Proof.
  intros v a vl vl' el el' x y p1 p2 pdiff.
  unfold path_different2.
  unfold path_different in pdiff.
  destruct pdiff.
  unfold not.
  intros.
  destruct u. destruct u'.
  apply E_rev_in2 in H2.
  assert (H1' := H1).
  apply (P_inxyel_inxvl v a x y vl) in H1'.
  simpl in H1'.
  destruct H1'. *)

Lemma path_diff_cycle_is_path : forall (v: V_set) (a: A_set) (vl vl' vll: V_list) (el el' ell: E_list) (x1 x2 y1 y2:Vertex) (p1: Path v a x1 y1 vl el) (p2: Path v a x2 y2 vl' el')  (g : Graph v a),
  {path_different1 v a vl vl' el el' x1 x2 y1 y2 p1 p2 /\ vll = (vl ++ (cdr Vertex (rev (x2 :: vl')))) /\ ell = (el ++ (E_reverse el'))} +
  {path_different2 v a vl vl' el el' x1 x2 y1 y2 p1 p2 /\ vll = (vl ++ vl') /\ ell = (el ++ el')} -> Path v a x1 x1 vll ell.
Proof.
  intros v a vl vl' vll el el' ell x1 x2 y1 y2 p1 p2 g pdiff.
  destruct pdiff.
  assert (H := p2).
  apply Path_reverse in H.
  destruct a0.
  destruct H1.
  rewrite H1.
  rewrite H2.
  apply (Path_append2 v a x1 y1 x1 vl (cdr Vertex (rev (x2 :: vl'))) el (E_reverse el')).
  intros.
  unfold not.
  intros.
  unfold path_different1 in H0.
  intuition.
  apply H7 in H3.
  inversion H3.

  apply -> in_rev.
  apply H4.
  unfold path_different1 in H0.
  destruct H0.
  destruct H3.
  destruct H4.
  destruct H5.
  apply H6.

  unfold path_different1 in H0.
  intuition.
  apply p1.
  unfold path_different1 in H0.
  intuition.
  rewrite H0. rewrite H4.
  apply H.

  reflexivity.
  apply g.

  assert (H := p1).
  destruct a0.
  destruct H1.
  rewrite H1. rewrite H2.
  unfold path_different2 in H0.
  intuition.
  apply (Path_append2 v a x1 y1 x1 vl vl' el el').
  unfold not.
  intros.
  apply H5 in H6.
  inversion H6.
  apply H8. 
  unfold not. apply H7.
  intros.
  apply H3 in H6. inversion H6.
  apply p1.
  rewrite H0. rewrite H4.
  apply p2.
  reflexivity.
Qed.



Definition path_same (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (x y:Vertex) (p1: Path v a x y vl el) (p2: Path v a x y vl' el') :=
  vl = vl' /\ el = el'.

(* Lemma all_subpaths_in_tree_same: forall (v:V_set) (a:A_set) (x y x' y': Component) (vl vl' vl'' : V_list) (el el' el'': E_list) (t : Tree v a) (p: Path v a x y vl el)
  (sp1 : Path v a x' y' vl' el') (sp2 : Path v a x' y' vl'' el''),
  subpath v a vl vl' el el' x y x' y' p -> subpath v a vl vl'' el el'' x y x' y' p -> path_same v a vl' vl'' el' el'' x' y' sp1 sp2.
Admitted.

Lemma all_subpaths_same_paths_same: forall (v:V_set) (a:A_set) (x y x' y': Component) 
  (vla vlb vl' vl'' : V_list) (ela elb el' el'': E_list) (t : Tree v a) (pa: Path v a x y vla ela) (pb: Path v a x y vlb elb)
  (sp1 : Path v a x' y' vl' el') (sp2 : Path v a x' y' vl'' el''),
  subpath v a vla vl' ela el' x y x' y' pa -> subpath v a vlb vl'' elb el'' x y x' y' pb -> path_same v a vla vlb ela elb x y pa pb.
Admitted. *)

Lemma different_subpaths_in_tree_are_nil: forall (v:V_set) (a:A_set) (x y x1 x2 y1 y2: Component) (vla vl' vlb vl'' : V_list) (ela el' elb el'': E_list) (t : Tree v a) (pa: Path v a x y vla ela) (pb: Path v a x y vlb elb)
  (sp1 : Path v a x1 y1 vl' el') (sp2 : Path v a x2 y2 vl'' el''),
  subpath v a vla vl' ela el' x y x1 y1 pa -> subpath v a vlb vl'' elb el'' x y x2 y2 pb -> 
  {path_different1 v a vl' vl'' el' el'' x1 x2 y1 y2 sp1 sp2} + {path_different2 v a vl' vl'' el' el'' x1 x2 y1 y2 sp1 sp2} ->
  (vl' = nil /\ vl'' = nil).
Proof.
  intros v a x y x1 x2 y1 y2 vl vl' vlb vl'' el el' elb el'' t pa pb sp1 sp2 subp1 subp2 pdiff.
  assert (H := pdiff).
  unfold path_different1 in pdiff.
  unfold path_different2 in pdiff.
  assert (tt := t).
  apply Tree_isa_graph in t.

  destruct H.
  assert (Path v a x1 x1 (vl' ++ (cdr Vertex (rev (x2 :: vl'')))) (el' ++ E_reverse (el''))).
  apply (path_diff_cycle_is_path v a vl' vl'' (vl' ++ (cdr Vertex (rev (x2 :: vl'')))) el' el'' (el' ++ E_reverse (el'')) x1 x2 y1 y2 sp1 sp2 t).
  left.
  split.
  apply p.
  split.
  reflexivity.
  reflexivity.
  assert (Cycle v a x1 x1 (vl' ++ (cdr Vertex (rev (x2 :: vl'')))) (el' ++ E_reverse (el'')) H).
  unfold Cycle.
  reflexivity.
  apply Acyclic_no_cycle in H0.
  simpl in H0.
  unfold V_nil in H0.
  apply app_eq_nil in H0.
  destruct H0.
  split.
  apply H0.
  apply cdr_rev5 in H1.
  apply H1.
  apply Tree_isa_acyclic in tt.
  apply tt.

  assert (Path v a x1 x1 (vl' ++ vl'') (el' ++ el'')).
  apply (path_diff_cycle_is_path v a vl' vl'' (vl' ++ vl'') el' el'' ((el' ++ el'')) x1 x2 y1 y2 sp1 sp2 t).
  right.
  split.
  apply p.
  split.
  reflexivity.
  reflexivity.
  assert (Cycle v a x1 x1 (vl' ++ vl'') (el' ++ el'') H).
  unfold Cycle.
  reflexivity.
  apply Acyclic_no_cycle in H0.
  simpl in H0.
  unfold V_nil in H0.
  apply app_eq_nil in H0.
  destruct H0.
  split.
  apply H0.
  apply H1.
  apply Tree_isa_acyclic in tt.
  apply tt.
Qed.

Definition same_diff_list

Fixpoint same_diff_list_to_path1 Path v a x y vl el
  match element with
  | path_diff v a x1 x2 y1 y2 vl' vl'' el' el'' :: tl => same_diff_list_to_path1 tl (Path v a x x2 (vl ++ vl') (el ++ el'))
  | path_same v a x1 x2 y1 y2 vl' vl'' el' el'' :: tl => same_diff_list_to_path1 tl (Path v a x x2 (vl ++ vl') (el ++ el'))
  end.

Lemma exists_same_diff_list_of_pa_pb_sdltp1ispa_sdltp2ispb
Lemma diff_lists_are_nil_so_only_same_lists
Lemma only_same_lists->pa=pb
Lemma pa=pb

Lemma different_subpaths_are_nil_paths_same: forall (v:V_set) (a:A_set) (x y x1 x2 y1 y2: Component) 
  (vla vlb vl' vl'' : V_list) (ela elb el' el'': E_list) (t : Tree v a) (pa: Path v a x y vla ela) (pb: Path v a x y vlb elb)
  (spa : Path v a x1 y1 vl' el') (spb : Path v a x2 y2 vl'' el''),
  subpath v a vla vl' ela el' x y x1 y1 pa -> subpath v a vlb vl'' elb el'' x y x2 y2 pb ->
  {path_different1 v a vl' vl'' el' el'' x1 x2 y1 y2 spa spb} + {path_different2 v a vl' vl'' el' el'' x1 x2 y1 y2 spa spb} ->
  path_same v a vla vlb ela elb x y pa pb.
Proof.
  intros v a x y x1 x2 y1 y2 vla vlb vl' vl'' ela elb el' el'' t pa pb spa spb suba subb pdiff.
  assert (H := pdiff).

  apply (different_subpaths_in_tree_are_nil v a x y x1 x2 y1 y2 vla vl' vlb vl'' ela el' elb el'' t pa pb spa spb suba subb) in pdiff.
  destruct pdiff as [vlnil vl'nil].
  unfold path_same.
  destruct H.
  
Admitted.

Lemma Tree_only_one_path : forall (v:V_set) (a:A_set) (x y : Component) (t : Tree v a) (vl vl' : V_list) (el el' : E_list)
  (p1 : Path v a x y vl el) (p2 : Path v a x y vl' el'),
  path_same v a vl vl' el el' x y p1 p2.
Proof.
  intros v a x y t vl vl' el el' p1 p2.
  apply different_subpaths_are_nil_paths_same.
  unfold path_same.
Admitted.





(* Definition path_different2 (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (x y x' y':Vertex) (w1: Path v a x y vl el) (w2: Path v a x' y' vl' el') :=
  (forall (vv : Vertex), In vv (middle vl) -> ~ In vv (middle vl')) /\ (forall (e : Edge), In e (middle el) -> ~ In e (middle el')). *)

(* Axiom Paths_into_parts' : forall (v:V_set) (a:A_set) (x y : Component) (vla vlb : V_list) (ela elb : E_list)
  (pa : Path v a x y vlpa elpa) (pb : Path v a x y vlpb elpb),
  vlpa != vlpb \/ elpa != elpb ->
  exists (x' y' : Vertex) (vlax vlay vlbx vlby vla vlb : V_list) (elax elay elbx elby ela elb : E_list),
  Path v a x x' vlax elax /\ Path v a x' y' vla ela /\ Path v a y' y vlay elay /\
  Path v a x x' vlbx elbx /\ Path v a x' y' vlb elb /\ Path v a y' y vlby elby /\
  pa = p1p2p3
  pb = p4p5p6 *)

(* There can only be one path in a tree t, ending in vertices x and y.

Suppose there are two paths from x to y: a and b. a = s1 :: d1 :: s2 :: d2 .... dn :: sn
                                                  b = s1 :: e1 :: s2 :: e2 .... en :: sn
  forall 1<=k<=n: dk != ek.
d1 (rev e1) makes a cycle. This cycle must be of length 0, because t is acyclic as it is a tree. therefore el_p1 = el_p2.

I Suppose we only have a root. There is only the path from root to root and that is equivalent to all other such paths.
II Suppose we add v as a leaf to t. For all paths not containing v we use IS. If v is contained in a path, then at its start
or at its end, otherwise it is no path, as v is a leaf and only has degree 1. Let v = y. All paths from x to the neighbor of
y are the same. As y has degree of 1, there is only one possible extension to those paths. Therefore all paths from x to y
are the same.
 *)


Lemma connected_path :
 forall (v : V_set) (a : A_set) (g : Connected v a) (x y : Vertex),
 v x -> v y -> {vl : V_list &  {el : E_list &  Path v a x y vl el}}.
Proof.
        intros; elim (Connected_walk v a g x y H H0); intros.
        elim p; intros.
        apply (Walk_to_path v a x y x0 x1 p0).
Qed.

Definition shortest_path2 (v : V_set) (a : A_set) (vl : V_list) (el : E_list) (c0 c1 : Component) (p: Path v a c0 c1 vl el) := 
  forall (vl': V_list) (el' : E_list), Path v a c0 c1 vl' el' -> length el <= length el'.

Lemma shortest_path2_rev: forall (v : V_set) (a : A_set) (vl : V_list) (el : E_list) (c0 c1 : Component)
  (p0 : (Path v a c0 c1 vl el)) (p1 : (Path v a c1 c0 (cdr Vertex (rev (c0 :: vl))) (E_reverse el))) (g : Graph v a),
  shortest_path2 v a vl el c0 c1 p0 -> 
  shortest_path2 v a (cdr Vertex (rev (c0 :: vl))) (E_reverse el) c1 c0 p1.
Proof.
  intros v a vl el c0 c1 p0 p1 g s.
  unfold shortest_path2. unfold shortest_path2 in s.
  intros.
  rewrite E_rev_len.
  apply Path_reverse in H.
  apply s in H.
  rewrite E_rev_len in H.
  apply H.
  apply g.
Qed.

Definition distance2 (v: V_set) (a: A_set) (c0 c1 : Component) (n : nat) :=
  exists (vl : V_list) (el : E_list) (p: Path v a c0 c1 vl el), shortest_path2 v a vl el c0 c1 p /\ length el = n.

Definition distance (v: V_set) (a: A_set) (c0 : Component) (n : nat) :=
  distance2 v a root c0 n.

Lemma connected_min_path: forall (v: V_set) (a: A_set) (x : Component) (t : Tree v a),
 v x -> {vl : V_list &  {el : E_list &  {p : Path v a root x vl el & distance2 v a root x (length el)}}}.
Proof.
  intros v a xx t vxx.
  assert (v root) as vroot.
  apply (all_trees_rooted v a).
  apply t.
  assert (t2 := t).
  apply Tree_isa_connected in t.
  apply (connected_path v a t root xx vroot) in vxx.
  destruct vxx.
  destruct s.
  exists x.
  exists x0.
  exists p.
  unfold distance2.
  exists x. exists x0. exists p.
  split.
  unfold shortest_path2.
  intros vl el p2.
  assert (vl = x /\ el = x0).
  apply (Tree_only_one_path v a root xx t2).
  apply p2.
  apply p.
  destruct H.
  rewrite H0.
  reflexivity.
  reflexivity.
Qed.


Lemma connected_min_path2: forall (v: V_set) (a: A_set) (x : Component) (t : Tree v a),
 v x -> {vl : V_list &  {el : E_list &  {p : Path v a x root vl el & distance2 v a root x (length el)}}}.
Proof.
  intros v a x t vx.
  apply (connected_min_path v a x t) in vx.
  destruct vx.
  destruct s.
  destruct s.
  rename x0 into vl. rename x1 into el.
  exists (cdr Vertex(rev(root::vl))).
  exists (E_reverse el).
  assert (Path v a x root (cdr Vertex (rev (root :: vl))) (E_reverse el)).
  apply Path_reverse in x2.
  apply x2.
  apply Tree_isa_graph in t.
  apply t.
  exists H.
  unfold distance2.
  exists vl. exists el. exists x2.
  split.
  unfold shortest_path2.
  intros vl0 el0 p2.
  assert (vl = vl0 /\ el = el0).
  apply (Tree_only_one_path v a root x t).
  apply x2.
  apply p2.
  destruct H0.
  rewrite H1.
  reflexivity.
  rewrite E_rev_len.
  reflexivity.
Qed.

Lemma path_length_geq_0: forall (v: V_set) (a: A_set) (vl:V_list) (el:E_list) (x y : Component),
  Walk v a x y vl el -> length el >= 0.
Proof.
  intros v a vl el x y w.
  inversion w.
  simpl.
  intuition.
  simpl.
  intuition.
Qed.


Lemma distance_root_0: forall (v: V_set) (a: A_set), v root -> distance v a root 0.
Proof.
  intros v0 a0.
  unfold distance.
  unfold distance2.
  intros.
  assert (Path v0 a0 root root V_nil E_nil).
  apply P_null.
  apply H.
  exists V_nil. exists E_nil. exists H0.
  split.
  unfold shortest_path2.
  intros.
  simpl.
  intuition.
  reflexivity.
Qed.

Lemma distance_refl: forall (v:V_set) (a:A_set) (c0 c1 : Component) (n:nat) (g: Graph v a),
  distance2 v a c0 c1 n -> distance2 v a c1 c0 n.
Proof.
  intros v a c0 c1 n g dis.
  unfold distance2 in dis.
  unfold distance2.
  intros.
  destruct dis.
  destruct H. destruct H. destruct H.
  assert (p := x1).
  apply Path_reverse in p.
  exists (cdr Vertex (rev (c0 :: x))).
  exists (E_reverse x0).
  exists p.
  split.

  apply (shortest_path2_rev v a x x0 c0 c1 x1 p g) in H.
  apply H.
  rewrite E_rev_len.
  apply H0.
  apply g.
Qed.

Lemma distance_no_dup: forall (v:V_set) (a:A_set) (c0 c1 : Component) (n m:nat),
  distance2 v a c0 c1 n -> distance2 v a c0 c1 m -> n = m.
Proof.
  intros v a c0 c1 n m dis1 dis2.
  unfold distance2 in dis1. unfold distance2 in dis2.
  destruct dis1. destruct H. destruct H. destruct H.
  destruct dis2. destruct H1. destruct H1. destruct H1.
  unfold shortest_path2 in H. unfold shortest_path2 in H1.
  apply H in x4.
  apply H1 in x1.
  rewrite <- H2.
  rewrite <- H0.
  intuition.
Qed.

End Help.