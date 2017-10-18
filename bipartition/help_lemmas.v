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

Definition shortest_path2 {v: V_set} {a:A_set} {vl : V_list} {el : E_list} (c0 c1 : Component) {p: Path v a c0 c1 vl el} := 
  forall (vl': V_list) (el' : E_list), Path v a c0 c1 vl' el' -> length vl <= length vl'.



Definition distance2 (v: V_set) (a: A_set) (c0 c1 : Component) (n : nat) :=
  forall (vl : V_list) (el : E_list) (p: Path v a c0 c1 vl el), n <= length el.

Definition distance (v: V_set) (a: A_set) (c0 : Component) (n : nat) :=
  forall (vl : V_list) (el : E_list) (p: Path v a root c0 vl el), n <= length el.

Lemma E_eq2 : forall (e1 e2 : Edge),
  E_eq e1 e2 -> E_eq e2 e1.
Proof.
  intros e1 e2 eq.
  inversion eq.
  apply E_refl.
  apply E_rev.
Qed.

Lemma neq_symm: forall {p q: V_list}, p <> q -> q <> p.
Proof.
  intros p q pq.
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

Lemma rev_nil: forall (l : list Vertex),
  rev l = nil <-> l = nil.
Proof.
  intros l.
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

Lemma cdr_rev: forall (x:Vertex) (vl:V_list),
  In x (cdr (rev vl)) -> In x vl.
Proof.
  intros x vl i.
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

Lemma cdr_rev2: forall (vl : V_list) (x y : Vertex),
  In x (cdr (rev vl)) -> In x (cdr (rev (y :: vl))).
Proof.
  intros vl x y i.
  simpl.
  rewrite cdr_app.
  apply in_or_app.
  left.
  apply i.
  assert (vl = V_nil \/ vl <> V_nil).
  apply classic.
  destruct H.
  rewrite H in i.
  intuition.
  unfold not. intros. apply H.
  apply rev_nil.
  unfold V_nil in H0.
  apply H0.
Qed.

Lemma cdr_rev3: forall (vl : V_list) (x y : Vertex),
  ~ In x (cdr (rev vl)) -> x <> y -> ~ In x (cdr (rev (y::vl))).
Proof.
  intros vl x y i xy.
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


Lemma cdr_rev4: forall (vl : V_list) (x y : Vertex),
  ~ In x (cdr (rev (y::vl))) -> ~ In x (cdr (rev vl)).
Proof.
  intros vl x y i.
  unfold not. intros.
  apply (cdr_rev2 vl x y) in H.
  intuition.
Qed.

Fixpoint sub_starts_in_list (sublist superlist : list Vertex) : Prop :=
  match sublist with
  |nil => True
  |a::tla => match superlist with
    |nil => False
    |b::tlb => (a = b) /\ (sub_starts_in_list tla tlb)
    end
  end.

Fixpoint sub_in_list (sublist superlist : list Vertex) : Prop :=
  match sublist with
  |nil => True
  |a::tla => match superlist with
    |nil => False
    |b::tlb => ((a = b) /\ (sub_starts_in_list tla tlb)) \/ (sub_in_list sublist tlb)
    end
  end.

Lemma sub_one_more: forall (sub super : list Vertex) (a : Vertex),
  sub_in_list sub super -> sub_in_list sub (a::super).
Proof.
  intros sub super a sinl.
  destruct sub.
  reflexivity.
  unfold sub_in_list.
  right.
  apply sinl.
Qed.

Lemma subs_means_sub : forall (sub super : list Vertex),
  sub_starts_in_list sub super -> sub_in_list sub super.
Proof.
  intros sub super sinl.
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

Lemma sub_one_less: forall (sub super : list Vertex) (a : Vertex),
  sub_in_list (a :: sub) super -> sub_in_list sub super.
Proof.
  intros sub super a sinl.
  induction super.
  inversion sinl.
  simpl in sinl.
  destruct sinl.
  destruct H.
  apply subs_means_sub in H0.
  apply (sub_one_more sub super a0) in H0.
  apply H0.
  apply IHsuper in H.
  apply (sub_one_more sub super a0) in H.
  apply H.
Qed.





Lemma sub_nil_super: forall(superlist : list Vertex),
  sub_in_list nil superlist.
Proof.
  intros superlist.
  induction superlist.
  reflexivity.
  reflexivity.
Qed.

Lemma sub_sub_nil: forall (sublist : list Vertex),
  sub_in_list sublist nil -> sublist = nil.
Proof.
  intros sublist sinl.
  unfold sub_in_list in sinl.
  destruct sublist.
  reflexivity.
  inversion sinl.
Qed.

Lemma subs_sub_nil: forall (sublist : list Vertex),
  sub_starts_in_list sublist nil -> sublist = nil.
Proof.
  intros sublist sinl.
  unfold sub_in_list in sinl.
  destruct sublist.
  reflexivity.
  inversion sinl.
Qed.

Lemma in_means_embedded : forall (l : list Vertex) (x : Vertex),
  In x l <-> (exists (l1 l2 : list Vertex), l = l1 ++ (x :: l2)).
Proof.
  intros l.
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

Axiom subs_app3 : forall (sub super1 super2 : list Vertex),
  sub_starts_in_list sub super1 -> sub_starts_in_list sub (super1 ++ super2).

Axiom subs_app : forall (sub super : list Vertex),
  sub_starts_in_list sub super -> (exists (super2 : list Vertex), super = sub ++ super2).

(* Lemma subs_app3 : forall (sub super1 super2 : list Vertex),
  sub_starts_in_list sub super1 -> sub_starts_in_list sub (super1 ++ super2).
Proof.
Admitted.



Lemma subs_app : forall (sub super : list Vertex),
  sub_starts_in_list sub super -> (exists (super2 : list Vertex), super = sub ++ super2).
Proof.
  intros sub super sinl.
  (* exists (cut length(sub) super) *)
(*   induction super.
  apply subs_sub_nil in sinl.
  exists nil. rewrite sinl. reflexivity.

  induction sub.
  exists (a :: super). reflexivity.
  inversion sinl. *)
  induction sub.
  exists super. reflexivity.
  


Admitted. *)



Lemma subs_app2 : forall (sub1 sub2 super : list Vertex),
  sub_starts_in_list (sub1 ++ sub2) super -> (exists (super2 : list Vertex), super = sub1 ++ super2).
Proof.
  intros s1 s2 super sinl.
  apply subs_app in sinl.
  destruct sinl.
  exists (s2 ++ x). rewrite H. rewrite <- app_assoc. reflexivity.
Qed.


Lemma subs_minus : forall (s1 s2 s3 : list Vertex),
  sub_starts_in_list s2 s3 <-> sub_starts_in_list (s1 ++ s2) (s1 ++ s3).
Proof.
  intros s1 s2 s3.
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



Lemma subs_for_all : forall (sub super : list Vertex),
  sub_starts_in_list sub super -> (forall x : Vertex, In x sub -> In x super).
Proof.
  intros sub super sss x i.
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

Lemma sub_means_exists_subs : forall (sub super : list Vertex),
  sub_in_list sub super -> (exists (s1 s2 : list Vertex), super = s1 ++ s2 /\ sub_starts_in_list sub s2).
Proof.
  intros sub super sinl.
  induction super.
  exists nil. exists nil. split. reflexivity. apply sub_sub_nil in sinl. rewrite sinl. reflexivity.

  destruct sub.
  exists nil. exists (a :: super). split. reflexivity. reflexivity.

  unfold sub_in_list in sinl.
  destruct sinl.
  destruct H.
  rewrite H. exists nil. exists (a :: super). split. reflexivity. 
  apply (subs_minus (a :: nil) sub super) in H0. rewrite <- app_comm_cons in H0. rewrite <- app_comm_cons in H0.
  rewrite app_nil_l in H0. rewrite app_nil_l in H0. apply H0.

  apply IHsuper in H.
  destruct H.
  destruct H.
  exists (a :: x). exists x0. destruct H. split. rewrite H. reflexivity. apply H0.
Qed.


Lemma sub_for_all : forall (sub super : list Vertex),
  sub_in_list sub super -> (forall x : Vertex, In x sub -> In x super).
Proof.
  intros sub super sss x i.
  apply sub_means_exists_subs in sss.
  destruct sss.
  destruct H.
  destruct H.
  rewrite H.
  apply (subs_for_all sub x1 H0 x) in i.
  apply in_or_app.
  right.
  apply i.
Qed.

Lemma sub_exists_one : forall (sub super : list Vertex),
  (exists x : Vertex, In x sub /\ ~ In x super) -> ~ sub_in_list sub super.
Proof.
  intros sub super ex.
  destruct ex.
  destruct H.
  unfold not.
  intros.
  apply (sub_for_all sub super H1 x) in H.
  apply H0 in H.
  inversion H.
Qed.

Lemma sub_starts_or_in_rest : forall (sublist superlist : list Vertex) (a : Vertex),
  sub_in_list sublist (a :: superlist) -> sub_starts_in_list sublist (a :: superlist) \/ sub_in_list sublist superlist.
Proof.
  intros sublist superlist a sinl.
  destruct sublist.
  left.
  reflexivity.
  unfold sub_in_list in sinl.
  destruct sinl.
  destruct H.
  left.
  simpl.
  split.
  apply H.
  apply H0.
  right.
  apply H.
Qed.

Lemma sub_exists_embedding: forall (sublist superlist : list Vertex),
  sub_in_list sublist superlist -> (exists (l1 l3 : V_list), superlist = l1 ++ sublist ++ l3).
Proof.
  intros sublist superlist sinl.
  induction superlist.
  destruct sublist.
  exists nil. exists nil. reflexivity.
  inversion sinl.

  apply sub_starts_or_in_rest in sinl.
  destruct sinl.
  apply subs_app in H.
  destruct H.
  rewrite H. exists nil. exists x. reflexivity.
  apply IHsuperlist in H.
  destruct H. destruct H.
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
  Path v a x y vl el -> ~ In y (cdr (rev vl)).
Proof.
  intros v a x y vl el p.

  unfold not.
  intros.
  induction p.
  simpl in H.
  inversion H.
  apply IHp.

  apply (cdr_rev3 vl z y) in IHp.
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
  Path v a x y vl el -> ~ In x (cdr (rev vl)).
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
 Path v a x y vl el -> Path v a y x (cdr (rev (x :: vl))) (E_reverse el).
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

(* There can only be one path in a tree t, ending in vertices x and y.

Suppose there are two paths from x to y: p1 and p2. p1 and p2 must be out of three parts: el_p1 = a b1 c, el_p2 = a b2 c.
With b1 completely different from b2.
b1 (rev b2) makes a cycle. This cycle must be of length 0, because t is acyclic as it is a tree. therefore el_p1 = el_p2.

I Suppose we only have a root. There is only the path from root to root and that is equivalent to all other such paths.
II Suppose we add v as a leaf to t. For all paths not containing v we use IS. If v is contained in a path, then at its start
or at its end, otherwise it is no path, as v is a leaf and only has degree 1. Let v = y. All paths from x to the neighbor of
y are the same. As y has degree of 1, there is only one possible extension to those paths. Therefore all paths from x to y
are the same.
 *)

Axiom Paths_into_parts : forall (v:V_set) (a:A_set) (x y : Component) (vla vlb : V_list) (ela elb : E_list)
  (pa : Path v a x y vla ela) (pb : Path v a x y vlb elb),
  exists (vl1 vl2a vl2b vl3 : V_list) (x1 x2 : Vertex) (el2a el2b : E_list)
  (p2a: Path v a x1 x2 vl2a el2a) (p2b: Path v a x1 x2 vl2b el2b), 
  vla = vl1 ++ vl2a ++ vl3 /\ vlb = vl1 ++ vl2b ++ vl3 /\ 
  (forall z: Vertex, In z vl2a -> ~ In z vl2b) /\ (forall z: Vertex, In z vl2b -> ~ In z vl2a).

(* Lemma Paths_into_parts : forall (v:V_set) (a:A_set) (x y : Component) (vla vlb : V_list) (ela elb : E_list)
  (pa : Path v a x y vla ela) (pb : Path v a x y vlb elb),
  exists (vl1 vl2a vl2b vl3 : V_list) (x1 x2 : Vertex) (el2a el2b : E_list)
  (p2a: Path v a x1 x2 vl2a el2a) (p2b: Path v a x1 x2 vl2b el2b), 
  vla = vl1 ++ vl2a ++ vl3 /\ vlb = vl1 ++ vl2b ++ vl3 /\ 
  (forall z: Vertex, In z vl2a -> ~ In z vl2b) /\ (forall z: Vertex, In z vl2b -> ~ In z vl2a).
Proof.
  intros.
  exists nil.
  exists nil.
  exists nil.
  exists vla.
  exists x.
  exists x.
  exists nil.
Admitted. *)

Axiom Tree_only_one_path : forall (v:V_set) (a:A_set) (x y : Component) (t : Tree v a) (vl vl' : V_list) (el el' : E_list)
  (p1 : Path v a x y vl el) (p2 : Path v a x y vl' el'),
  vl = vl' /\ el = el'.

(* Lemma Tree_only_one_path : forall (v:V_set) (a:A_set) (x y : Component) (t : Tree v a) (vl vl' : V_list) (el el' : E_list)
  (p1 : Path v a x y vl el) (p2 : Path v a x y vl' el'),
  vl = vl' /\ el = el'.
Proof.
  intros v a x y t vl vl' el el' p1 p2.
  assert (parts := p2).
  apply (Paths_into_parts v a x y vl vl' el el' p1) in parts.
  destruct parts.
  destruct H.
  destruct H.
  destruct H.
  destruct H.
  destruct H.
  destruct H.
  destruct H.
  destruct H.
  destruct H.
  destruct H.
  destruct H0.
  destruct H1.
  apply Path_reverse in x9.
  apply (Path_append2 v a x4 x5 x4 x1 (cdr (rev (x4 :: x2))) x6 (E_reverse x7)) in x9.
  assert (Cycle v a x4 x4 (x1 ++ cdr (rev (x4 :: x2))) (x6 ++ E_reverse x7) x9).
  unfold Cycle.
  reflexivity.
  apply (Acyclic_no_cycle ) in H3.
  apply app_eq_nil in H3.
  destruct H3.
  simpl in H4.
  assert(x2 = nil).
  admit.
  rewrite H3 in H.
  rewrite H5 in H0.
  rewrite <- H0 in H.
  split.
  apply H.
  admit. (* H, p1, p2 -> el = el'*)
  apply Tree_isa_acyclic in t.
  apply t.
  intros.
  apply H1 in H3.
  unfold not. intros. apply H3.
  apply cdr_rev in H4.
  unfold In in H4.
  destruct H4.
  admit.
  apply H3 in H4.
  inversion H4.
  admit.
  admit. (* Critical *)
  apply x8.
  reflexivity.
  apply Tree_isa_graph in t.
  apply t.
Admitted. *)

Lemma connected_path :
 forall (v : V_set) (a : A_set) (g : Connected v a) (x y : Vertex),
 v x -> v y -> {vl : V_list &  {el : E_list &  Path v a x y vl el}}.
Proof.
        intros; elim (Connected_walk v a g x y H H0); intros.
        elim p; intros.
        apply (Walk_to_path v a x y x0 x1 p0).
Qed.

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
  intros vl el p2.
  assert (vl = x /\ el = x0).
  apply (Tree_only_one_path v a root xx t2).
  apply p2.
  apply p.
  destruct H.
  rewrite H0.
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
  exists (cdr(rev(root::vl))).
  exists (E_reverse el).
  assert (Path v a x root (cdr (rev (root :: vl))) (E_reverse el)).
  apply Path_reverse in x2.
  apply x2.
  apply Tree_isa_graph in t.
  apply t.
  exists H.
  unfold distance2.
  intros vl0 el0 p2.
  assert (vl = vl0 /\ el = el0).
  apply (Tree_only_one_path v a root x t).
  apply x2.
  apply p2.
  destruct H0.
  rewrite H1.
  rewrite E_rev_len.
  reflexivity.
Qed.

Lemma distance_root_0: forall (v: V_set) (a: A_set) (root:Component), distance v a root 0.
Proof.
  intros v0 a0.
  unfold distance.
  intros.
  inversion p.
  simpl.
  reflexivity.
  simpl.
  intuition.
Qed.

Lemma distance_refl: forall (v:V_set) (a:A_set) (c0 c1 : Component) (n:nat) (g: Graph v a),
  distance2 v a c0 c1 n -> distance2 v a c1 c0 n.
Proof.
  intros v a c0 c1 n g dis.
  unfold distance2 in dis.
  unfold distance2.
  intros.
  apply Path_reverse in p.
  apply dis in p.
  rewrite E_rev_len in p.
  apply p.
  apply g.
Qed.

End Help.