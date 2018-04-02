Require Import GraphBasics.Graphs.
Require Import FunInd.

Load "Edge_related".
Load "List_related".


Section Path_Walk_related.


Definition path_same (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (x y:Component) (p1: Path v a x y vl el) (p2: Path v a x y vl' el') :=
  vl = vl' /\ el = el'.

Definition append_w (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (x y z:Component) (w1: Walk v a x y vl el) (w2: Walk v a y z vl' el') :=
  Walk v a x z (vl ++ vl') (el ++ el').

Definition append_p (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (x y z:Component) (p1: Path v a x y vl el) (p2: Path v a y z vl' el') :=
  Walk v a x z (vl ++ vl') (el ++ el').

Function length_w {v: V_set} {a: A_set} {vl : V_list} {el: E_list} {c1 c2: Component} (p: Walk v a c1 c2 vl el) := length el.
Function length_p {v: V_set} {a: A_set} {vl : V_list} {el: E_list} {c1 c2: Component} (p: Path v a c1 c2 vl el) := length el.

Definition shortest_path2 (v : V_set) (a : A_set) (vl : V_list) (el : E_list) (c0 c1 : Component) (p1: Path v a c0 c1 vl el) := 
  forall (vl': V_list) (el' : E_list) (p2: Path v a c0 c1 vl' el'), length_p p1 <= length_p p2.

Definition distance2 (v: V_set) (a: A_set) (c0 c1 : Component) (n : nat) :=
  exists (vl : V_list) (el : E_list) (p: Path v a c0 c1 vl el), shortest_path2 v a vl el c0 c1 p /\ length el = n.







Lemma Path_isa_walk: 
  forall (v: V_set) (a: A_set) (x y : Component) (vl : V_list) (el : E_list),
  Path v a x y vl el -> Walk v a x y vl el.
Proof.
  intros.
  apply Path_isa_trail in H.
  apply Trail_isa_walk in H.
  apply H.
Qed.

Lemma Path_appended_isa_walk :
 forall (v: V_set) (a: A_set) (x y z : Component) (vl vl' : V_list) (el el' : E_list),
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



Lemma Path_append (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (x y z:Component) (p1: Path v a x y vl el) (p2: Path v a y z vl' el'):
 Walk v a x z (vl ++ vl') (el ++ el') = append_p v a vl vl' el el' x y z p1 p2.
Proof.
  intros.
  unfold append_p.
  reflexivity.
Qed.

Lemma Path_vl_el_lengths_eq : forall (v: V_set) (a: A_set) (vl : V_list) (el : E_list) (x y : Component) (p : Path v a x y vl el),
  length vl = length el.
Proof.
  intros v a vl el x y p.
  induction p.
  reflexivity.
  simpl. rewrite IHp.
  reflexivity.
Qed.


Lemma Path_append_lengthsum (v: V_set) (a: A_set) (vl vl' : V_list) (el el' : E_list) (x y z:Component) (p1: Path v a x y vl el) (p2: Path v a y z vl' el') (p3: append_p v a vl vl' el el' x y z p1 p2):
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



Lemma Path_cons : forall (v: V_set) (a: A_set) (x y z: Component) (vl : V_list) (el : E_list),
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

Lemma Path_append2 : forall (v: V_set) (a: A_set) (x y z : Component) (vl vl' : V_list) (el el' : E_list),
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

Lemma P_y_not_in_cdrrevvl : forall (v: V_set) (a:A_set) (x y : Component) (vl : V_list) (el : E_list),
  Path v a x y vl el -> ~ In y (cdr Vertex (rev vl)).
Proof.
  intros v a x y vl el p.

  unfold not.
  intros.
  induction p.
  simpl in H.
  inversion H.
  apply IHp.

  apply (cdr_rev3 Component vl z y) in IHp.
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


Lemma P_x_not_in_cdrrevvl : forall (v: V_set) (a:A_set) (x y : Component) (vl : V_list) (el : E_list),
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

Lemma shortest_path2_rev: forall (v : V_set) (a : A_set) (vl : V_list) (el : E_list) (c0 c1 : Component)
  (p0 : (Path v a c0 c1 vl el)) (p1 : (Path v a c1 c0 (cdr Component (rev (c0 :: vl))) (E_reverse el))) (g : Graph v a),
  shortest_path2 v a vl el c0 c1 p0 -> 
  shortest_path2 v a (cdr Component (rev (c0 :: vl))) (E_reverse el) c1 c0 p1.
Proof.
  intros v a vl el c0 c1 p0 p1 g s.
  unfold shortest_path2. unfold shortest_path2 in s.
  intros. unfold length_p.
  rewrite E_rev_len.
  apply Path_reverse in p2.
  specialize (s (cdr Component (rev (c1 :: vl'))) (E_reverse el') p2). unfold length_p in s.
  rewrite E_rev_len in s.
  apply s.
  apply g.
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
  exists (cdr Component (rev (c0 :: x))).
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
  unfold length_p in H. unfold length_p in H1.
  apply H in x4.
  apply H1 in x1.
  rewrite <- H2.
  rewrite <- H0.
  intuition.
Qed.

End Path_Walk_related.