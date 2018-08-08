Require Import GraphBasics.Connected.
Require Import GraphBasics.Paths.

Load Help_Lemmata.


Section Adapted_from_Paths. (* This Section is adapted from GraphBasics.Paths *)

Lemma W_endx_inv :
 forall (v : V_set) (a : A_set) (x y : Vertex) (vl : V_list) (el : E_list), Walk v a x y vl el -> v x.
Proof.
        intros v a x y vl el w; elim w; auto.
Qed.

Lemma W_endy_inv :
 forall (v : V_set) (a : A_set) (x y : Vertex) (vl : V_list) (el : E_list), Walk v a x y vl el -> v y.
Proof.
        intros v a x y vl el w; elim w; auto.
Qed.

Lemma W_invl_inv :
 forall (v : V_set) (a : A_set) (x y : Vertex) (vl : V_list) (el : E_list),
 Walk v a x y vl el -> forall z : Vertex, In z vl -> v z.
Proof.
        intros v a x y vl el w; elim w; intros.
        inversion H.

        inversion H0.
        rewrite <- H1; apply (W_endx_inv _ _ _ _ _ _ w0).

        auto.
Qed.

Lemma W_iny_vl :
 forall (v : V_set) (a : A_set) (x y : Vertex) (vl : V_list) (el : E_list),
 Walk v a x y vl el -> vl <> V_nil -> In y vl.
Proof.
        intros v a x y vl el w; elim w; intros.
        absurd (V_nil = V_nil); auto.

        inversion w0.
        simpl; auto.

        rewrite H6; simpl; right.
        apply H; rewrite <- H6; discriminate.
Qed.

Lemma W_inxyel_inxvl :
 forall (v : V_set) (a : A_set) (x y : Vertex) (vl : V_list) (el : E_list),
 Walk v a x y vl el ->
 forall x' y' : Vertex, In (E_ends x' y') el -> In x' (x :: vl).
Proof.
        intros v a x y vl el p; elim p; intros.
        inversion H.

        inversion H0.
        inversion H1.
        simpl; auto.

        simpl; right.
        apply (H x' y'); auto.
Qed.

Lemma Walk_in_bigger_conn : forall (v vB : V_set) (a aB : A_set) (v1 v2 : Vertex) (vl : V_list) (el : E_list),
  V_included v vB -> A_included a aB -> Walk v a v1 v2 vl el -> Walk vB aB v1 v2 vl el.
Proof.
  intros v vB a aB v1 v2 vl el vI aI w.
  induction w.
  + apply W_null.
    unfold V_included in vI.
    unfold Included in vI.
    apply (vI x v0).
  + apply W_step.
    apply IHw.
    unfold V_included in vI.
    unfold Included in vI.
    apply (vI x v0).
    unfold A_included in aI.
    unfold Included in aI.
    apply (aI (A_ends x y) a0).
Qed.

End Adapted_from_Paths.

Section New_Spanning_Tree. 
(*  This section defines root, parent, children and treeify from a Connected
    treeify creates an arc list of a spanning tree of the Connected.
 *)

Fixpoint root' (v : V_set) (a : A_set) (c : Connected v a) : Name :=
  match c with
  | C_isolated x => component_name (x)
  | C_leaf v a co x y _ _ => root' v a co
  | C_edge v a co x y _ _ _ _ _ => root' v a co
  | C_eq v v' a a' _ _ co => root' v a co
  end.

Definition root : Name :=
  root' v a g.

Fixpoint parent' (v : V_set) (a : A_set) (c : Connected v a) (child : Name) : Name :=
  match c with
  | C_isolated x => (component_name x)
  | C_leaf v a co x y _ _ => if (Name_eq_dec child (component_name y)) then (component_name x) else parent' v a co child
  | C_edge v a co x y _ _ _ _ _ => parent' v a co child
  | C_eq v v' a a' _ _ co => parent' v a co child
  end.

Definition parent (child : Name) : Name :=
  parent' v a g child.

Fixpoint children' (v : V_set) (a : A_set) (c : Connected v a) (parent : Name) : list Name :=
  match c with
  | C_isolated _ => []
  | C_leaf v a co x y _ _ => if (Name_eq_dec parent (component_name x)) then (component_name y) :: (children' v a co parent) else children' v a co parent
  | C_edge v a co x y _ _ _ _ _ => children' v a co parent
  | C_eq v v' a a' _ _ co => children' v a co parent
  end.

Definition children (parent : Name) : list Name :=
  children' v a g parent.

Fixpoint treeify_a (v : V_set) (a : A_set) (c : Connected v a) : A_list :=
  match c with
  | C_isolated _ => []
  | C_leaf v a co x y _ _ => (A_ends x y) :: (A_ends y x) :: (treeify_a v a co)
  | C_edge v a co _ _ _ _ _ _ _ => treeify_a v a co
  | C_eq v _ a _ _ _ co => treeify_a v a co
  end.

Definition root_prop (root : Name) (v : V_set) : Prop :=
  v (name_component root).


Definition parent_prop (c : Name) : Prop :=
  (parent' v a g c <> c) \/ (c = (root' v a g)).

Definition parent_children (p c : Name) : Prop := 
  In c (children' v a g p) -> parent' v a g c = p.

Definition children_parent (c : Name) : Prop :=
  In c (children' v a g (parent' v a g c)) \/ c = root' v a g.

Definition parent_walk' (x y : Component) (vl : V_list) (el : E_list) v a g (w : Walk v a x y vl el) : Prop :=
  forall (c1 c2 : Name), In (E_ends (name_component c1) (name_component c2)) el -> parent' v a g c1 = c2.

Definition parent_walk x y vl el w : Prop :=
  parent_walk' x y vl el v a g w.

Function eqn n1 n2 : bool :=
  if (Name_eq_dec n1 n2) then true else false.

Fixpoint descendand' (v : V_set) (a : A_set) (c : Connected v a) (descendand ancestor : Name) : bool :=
  match c with
  | C_isolated x => (eqn ancestor (component_name x)) && eqn descendand ancestor
  | C_leaf v a co x y _ _ => 
      if (Name_eq_dec descendand (component_name y)) then
        ((eqn ancestor (component_name x)) || 
        (eqn ancestor (component_name y)) || 
        (descendand' v a co (component_name x) ancestor)) else
         descendand' v a co descendand ancestor
  | C_edge v a co x y _ _ _ _ _ => descendand' v a co descendand ancestor
  | C_eq v v' a a' _ _ co => descendand' v a co descendand ancestor
  end.

Definition descendand (descendand ancestor : Name) : bool :=
  descendand' v a g descendand ancestor.



Lemma parent_arcs : forall x y,
  x = parent y -> v (name_component y) -> y <> root -> (a (A_ends (name_component x) (name_component y)) /\ a (A_ends (name_component y) (name_component x))).
Proof.
  intros x y H yin ynotroot.
  unfold parent in *. unfold root in *. simpl in *.
  induction g ; simpl in * ; auto.
  + inversion yin.
    subst. rewrite cnnc in ynotroot. intuition.
  + break_match ; subst.
      simpl in *.
      split ; apply In_left.
      apply E_right.
      apply E_left.
      intuition.
      inversion yin.
      inversion H0.
      subst.
      rewrite cnnc in n0. intuition.
      subst. intuition.
      apply In_right. auto.
      inversion yin.
      inversion H0.
      subst.
      rewrite cnnc in n0. intuition.
      subst. intuition.
      apply In_right. auto.
  + intuition.
    apply In_right. auto.
    apply In_right. auto.
  + rewrite <- e in *.
    rewrite <- e0 in *.
    intuition.
Qed.

(* Lemma parent_same_root : forall p,
  parent p = p -> p = root. *)


Lemma root_prop_holds : forall v a g,
  root_prop (root' v a g) v.
Proof.
  induction g ; simpl ; auto.
  + apply Component_prop_1 ; auto.
Qed.

Lemma parent_root : forall v a g,
  parent' v a g (root' v a g) = root' v a g.
Proof.
  intros v a g.
  induction g ; simpl in * ; auto.
  break_match.
  assert (root_prop (root' v0 a0 g0) v0).
  apply root_prop_holds.
  unfold root_prop in H.
  rewrite e in H.
  simpl in H.
  intuition.
  auto.
Qed.

Lemma parent_prop_holds : forall (c : Name),
  parent_prop c.
Proof.
  intros c.
  unfold parent_prop.
  remember g as y in *.
  assert (v (name_component c)).
  apply Component_prop_1 ; auto.
  induction g.
  induction g ; simpl ; auto.
  + rewrite Heqy.
    simpl.
    right.
    inversion H.
    subst.
    unfold component_name.
    unfold name_component.
    break_match.
    auto.
  + subst ; simpl ; auto.
    inversion H.
    inversion H0.
    subst.
    break_match.
    left.
    assert (component_name x = c \/ component_name x <> c).
    apply classic.
    destruct H1.
    subst.
    simpl in n.
    intuition.
    auto.
    rewrite cnnc in n0.
    intuition.
    subst.
    assert (parent' v0 a0 c0 c <> c \/ c = root' v0 a0 c0).
    apply IHc0 ; auto.
    destruct H1.
    break_match.
    subst.
    assert (x = y0 \/ x <> y0).
    apply classic.
    destruct H2.
    subst.
    intuition.
    left.
    intuition.
    auto.
    auto.
  + subst ; simpl ; auto.
  + subst ; simpl ; auto.
Qed.

Lemma children_help : forall v0 a0 c0 c p,
  In c (children' v0 a0 c0 p) -> v0 (name_component p).
Proof.
  intros.
  induction c0 ; simpl in * ; auto.
  + inversion H.
  + break_match ; subst.
    simpl in *.
    destruct H ; subst.
    apply In_right. auto.
    apply In_right. auto.
    apply In_right. auto.
  + rewrite <- e in *.
    apply IHc0 ; auto.
Qed.

Lemma children_help2 : forall v0 a0 c0 c p,
  In c (children' v0 a0 c0 p) -> v0 (name_component c).
Proof.
  intros.
  induction c0 ; simpl in * ; auto.
  + intuition.
  + break_match.
    - subst.
      simpl in H.
      destruct H.
      subst.
      apply In_left.
      simpl.
      apply In_single.
      apply In_right.
      auto.
    - apply In_right.
      auto.
  + rewrite <- e.
    auto.
Qed.

Lemma children_not_reflexive : forall v a c p,
  ~ In p (children' v a c p).
Proof.
  intros.
  induction c ; simpl in * ; auto.
  intuition.
  break_match.
  subst.
  apply IHc.
  simpl in H.
  destruct H.
  inversion H.
  subst.
  intuition.
  auto.
  auto.
Qed.

Lemma parent_children_holds: forall (p c : Name),
  parent_children p c.
Proof.
  intros p c.
  unfold parent_children.
  intros.
  assert (v (name_component c)).
  apply Component_prop_1 ; auto.
  assert (v (name_component p)).
  apply Component_prop_1 ; auto.
  induction g.
  + simpl in *.
    inversion H.
  + simpl in *.
    inversion H1.
    inversion H2.
    subst.
    rewrite cnnc in *.
    repeat break_match ; subst ; auto.
    destruct p. simpl in *.
    apply children_not_reflexive in H.
    intuition.
    simpl in *.
    intuition.
    apply children_help in H.
    intuition.
    subst.
    repeat break_match ; subst ; simpl in * ; auto.
    apply children_help2 in H.
    simpl in H.
    intuition.
    destruct H.
    symmetry in H.
    intuition.
    inversion H0.
    inversion H3.
    subst.
    rewrite cnnc in n0.
    intuition.
    subst.
    apply IHc0 ; auto.
    assert (H' := H).
    apply children_help2 in H.
    apply IHc0 ; auto.
  + simpl in *.
    apply IHc0 ; auto.
  + rewrite <- e in *.
    rewrite <- e0 in *.
    apply IHc0 ; auto.
Qed.

Lemma parent_help2 : forall v0 a0 g0 c1 c2,
  parent' v0 a0 g0 c1 = c2 -> v0 (name_component c2).
Proof.
  intros.
  induction g0 ; simpl in * ; auto.
  + subst.
    simpl.
    apply In_single.
  + break_match.
    subst.
    apply In_right.
    simpl. auto.
    apply In_right.
    auto.
  + rewrite <- e in *.
    auto.
Qed.

Lemma parent_constant : forall (v0 : V_set) a0 g0 child paren x y (v0x : v0 x) (v0y : ~v0 y),
  parent' v0 a0 g0 child = paren -> 
  v0 (name_component child) ->
  parent'(V_union (V_single y) v0) (A_union (E_set x y) a0) (C_leaf v0 a0 g0 x y v0x v0y) child = paren.
Proof.
  intros v0 a0 g0 child paren x y v0x v0y H childisin.
  induction g0 ; simpl in * ; auto.
  + simpl in *.
    inversion v0x.
    subst.
    break_match ; auto.
  + assert (~v0 y).
    intuition.
    apply v0y.
    apply In_right. auto.

    assert (y0 <> y).
    intuition.
    apply v0y.
    rewrite H1.
    apply In_left. apply In_single.

    simpl in *.
    inversion v0x.
    inversion H2.
    repeat break_match ; subst ; simpl in * ; auto.
    inversion e.
    subst. intuition.
    inversion childisin ; intuition.
    intuition.
    intuition.
    subst.
    repeat break_match ; subst ; simpl in * ; auto.
    intuition.
    intuition.
  + rewrite <- e in *.
    auto.
Qed.

Lemma parent_walk_to_root : forall (v : V_set) a g c,
  v (name_component c) -> exists vl el w, parent_walk' (name_component c) (name_component (root' v a g)) vl el v a g w.
Proof.
  intros v0 a0 g0.
  induction g0 ; intros ; simpl in * ; auto.
  + inversion H.
    rewrite H0 in *.
    exists nil.
    exists nil.
    assert (Walk (V_single (name_component c)) A_empty (name_component c) (name_component c) [] []).
    apply W_null ; auto.
    exists H1.
    unfold parent_walk.
    unfold parent_walk'.
    intros.
    inversion H2.
  + inversion H.
    inversion H0.
    subst.
    assert (w := v1).
    apply (IHg0 (component_name x)) in w.
    clear IHg0.
    assert (Walk (V_union (V_single (name_component c)) v0) (A_union (E_set x (name_component c)) a0) (name_component c) x [x] [E_ends (name_component c) x]).
    apply W_step ; auto.
    apply W_null ; auto.
    apply In_right. auto.
    apply In_left. apply E_left.
    destruct w.
    repeat destruct H2.
    assert (Walk (V_union (V_single (name_component c)) v0)
                                     (A_union (E_set x (name_component c)) a0)
       (name_component (component_name x)) (name_component (root' v0 a0 g0)) x0 x1).
    apply (Walk_in_bigger_conn v0 (V_union (V_single (name_component c)) v0) a0) ; auto.
    unfold V_included.
    unfold Included.
    intros.
    apply In_right. auto.
    unfold A_included.
    unfold Included.
    intros.
    apply In_right. auto.
    apply (Walk_append _ _ _ _ _ _ _ _ _ H1) in H3.
    exists ([x] ++ x0). exists ([E_ends (name_component c) x] ++ x1).
    exists H3.
    simpl in *.
    assert (H2' := H2).
    unfold parent_walk.
    unfold parent_walk' in *.
    intros.

    destruct H4.
    inversion H4.
    assert (c = c1).
    unfold name_component in H6.
    break_match.
    break_match.
    rewrite H6. auto.
    subst.
    simpl in *.
    rewrite cnnc.
    break_match.
    rewrite cnnc. auto.
    intuition.

    simpl in *.
    repeat break_match ; subst ; simpl in * ; auto.
    
    apply (W_inxyel_inxvl v0 a0 x (name_component (root' v0 a0 g0)) x0 x1 x2 (name_component c) (name_component c2)) in H4 ; auto.
    simpl in H4. destruct H4 ; intuition.
    subst. intuition.
    apply (W_invl_inv v0 a0 x (name_component (root' v0 a0 g0)) x0 x1 x2) in H4.
    intuition.


    subst.
    assert (H0' := H0).
    apply IHg0 in H0.
    repeat destruct H0.
    assert (Walk (V_union (V_single y) v0) (A_union (E_set x y) a0) (name_component c) (name_component (root' v0 a0 g0)) x0 x1).
    apply (Walk_in_bigger_conn v0 _ a0) ; auto.
    unfold V_included.
    unfold Included.
    intros.
    apply In_right. auto.
    unfold A_included.
    unfold Included.
    intros.
    apply In_right. auto.
    exists x0.
    exists x1.
    exists H1.
    unfold parent_walk' in *.
    intros.
    assert (v0 (name_component c1)).
    apply (W_inxyel_inxvl v0 a0 (name_component c) (name_component (root' v0 a0 g0)) x0 x1) in H2 ; auto.
    inversion H2.
    rewrite <- H3.
    apply (W_endx_inv v0 a0 (name_component c) (name_component (root' v0 a0 g0)) x0 x1) ; auto.
    apply (W_invl_inv v0 a0 (name_component c) (name_component (root' v0 a0 g0)) x0 x1 x2 (name_component c1)) in H3 ; auto.
    apply (H0 c1 c2) in H2.
    apply (parent_constant v0 a0 g0 c1 c2 x y v1 n) in H2 ; auto.
  + apply IHg0 in H.
    repeat destruct H.
    exists x0.
    exists x1.
    assert (Walk v0 (A_union (E_set x y) a0) (name_component c) (name_component (root' v0 a0 g0)) x0 x1).
    apply (Walk_in_bigger_conn v0 _ a0) ; auto.
    unfold V_included.
    unfold Included. auto.
    unfold A_included.
    unfold Included.
    intros.
    apply In_right. auto.
    exists H0.
    unfold parent_walk' in *.
    intros.
    simpl in *.
    auto.
  + rewrite <- e in *.
    rewrite <- e0 in *.
    specialize (IHg0 c).
    auto.
Qed.

Definition eq_list_set (al : A_list) (a : A_set) : Prop :=
  forall e, In e al <-> a e.

Lemma A_list_A_set : forall (al : A_list),
  {a : A_set & eq_list_set al a}.
Proof.
  intros.
  unfold eq_list_set.
  induction al.
  
  + exists A_empty.
    split ; intros.
    inversion H.
    inversion H.
  + destruct IHal.
    destruct a0.
    exists (A_union (A_single (A_ends v0 v1)) x).
    split ; intros.
    simpl in *. destruct H.
    apply In_left. rewrite <- H.
    apply In_single.
    apply In_right.
    apply (i e) ; auto.
    simpl.
    inversion H.
    inversion H0.
    left. auto.
    right. apply (i e) ; auto.
Qed.


Lemma append_two : forall v0 a0 c a' a_old x y,
  eq_list_set (A_ends x y :: A_ends y x :: treeify_a v0 a0 c) a' ->
  eq_list_set (treeify_a v0 a0 c) a_old ->
  a' = A_union (E_set x y) a_old.
Proof.
  intros.
  apply U_set_eq.
  split ; intros ; unfold eq_list_set in * ; simpl in *.
  + specialize (H x0).
    specialize (H0 x0).
    apply <- H in H1.
    destruct H1.
    subst.
    apply In_left.
    apply E_right.
    destruct H1.
    subst.
    apply In_left.
    apply E_left.
    apply In_right.
    apply H0. auto.
  + specialize (H x0).
    specialize (H0 x0).
    inversion H1.
    subst.
    apply H.
    inversion H2.
    left.
    auto.
    right. left. auto.
    apply H.
    subst.
    apply <- H0 in H2.
    right. right. auto.
Qed.


Lemma treeify_creates_tree' : forall (v : V_set) (a : A_set) (c : Connected v a) (a' : A_set),
  eq_list_set (treeify_a v a c) a' -> Tree v a'.
Proof.
  intros v a c.
  induction c ; intros ; simpl in * ; auto.
  + assert (a' = A_empty).
    apply U_set_eq.
    unfold eq_list_set in H.
    split ; intros.
    apply H in H0.
    inversion H0.
    inversion H0.
    subst.
    apply T_root.
  + assert ({a_old : A_set & eq_list_set (treeify_a v0 a0 c) a_old}).
    apply A_list_A_set.
    destruct X as [a_old tree].
    assert (eq := tree).
    apply IHc in tree.
    assert (a' = A_union (E_set x y) a_old).
    apply (append_two v0 a0 c) ; auto.
    subst.
    apply (T_leaf v0 a_old tree y x) ; auto.
  + rewrite <- e in *.
    auto.
Qed.

Lemma treeify_creates_tree : forall (v : V_set) (a: A_set) (c : Connected v a),
  {a' : A_set & {t : Tree v a' & eq_list_set (treeify_a v a c) a'}}.
Proof.
  intros.
  assert ({a' : A_set & eq_list_set (treeify_a v0 a0 c) a'}).
  apply A_list_A_set.
  destruct X.
  exists x.
  assert (e' := e).
  apply treeify_creates_tree' in e.
  exists e.
  auto.
Qed.

Lemma treeify_in_conn : forall (v : V_set) (a : A_set) (c : Connected v a) (a' : A_set),
  eq_list_set (treeify_a v a c) a' -> A_included a' a.
Proof.
  intros v a c.
  unfold A_included.
  unfold Included.
  induction c ; intros ; unfold eq_list_set in H ; simpl in * ; auto.
  + specialize (H x0).
    intuition.
  + apply <- H in H0.
    repeat destruct H0.
    apply In_left. apply E_right.
    apply In_left. apply E_left.
    apply In_right.
    assert ({a_old : A_set & eq_list_set (treeify_a v0 a0 c) a_old}).
    apply A_list_A_set.
    destruct X.
    specialize (IHc x1).
    assert (forall x : Arc, x1 x -> a0 x).
    auto.
    apply H1.
    unfold eq_list_set in e.
    apply e.
    auto.
  + apply <- H in H0.
    specialize (IHc a').
    apply In_right.
    apply IHc ; auto.
    apply (H x0) ; auto.
  + rewrite <- e0 in *.
    apply (IHc a'0) ; auto.
Qed.

Lemma parent_isin_a : forall (v : V_set) a c pare chil,
  v (name_component pare) -> v (name_component chil) -> pare <> chil ->
  pare = parent' v a c chil -> a (A_ends (name_component chil) (name_component pare)).
Proof.
  intros v a c.
  induction c ; intros ; simpl in * ; subst ; auto ; intuition.
  + simpl in *.
    inversion H.
    inversion H0.
    subst. rewrite cnnc in *. intuition.
  + repeat break_match ; subst ; simpl in *.
    - apply In_left.
      apply E_left.
    - inversion H0.
      inversion H2.
      subst. rewrite cnnc in n0. intuition.
      inversion H.
      inversion H4.
      subst.
      rewrite cnnc in *.
      assert (v0 (name_component (parent' v0 a0 c chil))).
      apply (parent_help2 v0 a0 c chil) ; auto.
      intuition.
      subst.
      apply In_right.
      apply (IHc (parent' v0 a0 c chil) chil) ; auto.
  + simpl in *.
    apply In_right.
    apply IHc ; auto.
Qed.


Lemma descendand_inv1 : forall v a g c p,
  descendand' v a g c p = true ->
  v (name_component c).
Proof.
  intros.
  induction g0 ; simpl in * ; subst ; intuition.
  + unfold eqn in H. unfold component_name in H. unfold name_component.
    repeat break_match ; subst.
    inversion e0. apply In_single.
    simpl in H. inversion H.
    simpl in H. inversion H.
    simpl in H. inversion H.
  + unfold eqn in H. unfold component_name in H. unfold name_component.
    repeat break_match ; subst.
    inversion e. inversion e1. subst. intuition.
    inversion e. apply In_left. apply In_single.
    inversion e. apply In_left. apply In_single.
    inversion e. apply In_left. apply In_single.
    apply In_right. intuition.
Qed.


Lemma descendand_inv2 : forall (v : V_set) a g c p,
  descendand' v a g c p = true ->
  v (name_component p).
Proof.
  intros v a g.
  induction g ; simpl in * ; intuition.
  + subst. intuition.
    unfold eqn in H. unfold component_name in H. unfold name_component.
    repeat break_match ; subst.
    inversion e. apply In_single.
    simpl in H. inversion H.
    simpl in H. inversion H.
    simpl in H. inversion H.
  + intuition.
    unfold eqn in H. unfold component_name in H. unfold name_component.
    repeat break_match.
    subst. inversion e0. inversion e1. subst. intuition.
    subst. inversion e0. subst. apply In_right. auto.
    subst. inversion e0. apply In_left. apply In_single.
    inversion e. subst.
    simpl in *. apply In_right. subst.
    apply (IHg (Checker x) (Checker c0)) ; auto.
    apply In_right. unfold name_component in IHg. specialize (IHg c p). break_match. inversion Heqn0. subst. apply IHg ; intuition.
  + rewrite <- e in *.
    apply (IHg c p) ; auto.
Qed.

Lemma descendand_refl : forall (v : V_set) a g c,
  v c ->
  descendand' v a g (Checker c) (Checker c) = true.
Proof.
  intros c H.
  induction g0 ; simpl in * ; intuition.
  + inversion H. subst. unfold component_name.
    unfold eqn. break_match ; subst ; intuition.
  + inversion H. inversion H0. subst. unfold component_name.
    unfold eqn. break_match ; subst ; intuition.
    subst. unfold component_name.
    unfold eqn. break_match ; subst ; intuition.
  + rewrite <- e in *.
    intuition.
Qed.



Lemma descendand_par : forall (v : V_set) a g c,
  v (name_component c) ->
  descendand' v a g c (parent' v a g c) = true.
Proof.
  intros c H.
  induction g0 ; simpl in * ; intuition.
  + inversion H. subst. unfold component_name.
    unfold eqn. repeat break_match ; subst ; intuition.
    unfold name_component in n. break_match. intuition.
  + inversion H. inversion H0. subst. unfold component_name.
    unfold eqn. repeat break_match ; subst ; intuition.
    unfold name_component in n. break_match. intuition.
    subst. unfold component_name in *.
    unfold eqn. repeat break_match ; subst ; intuition.
  + rewrite <- e in *.
    intuition.
Qed.

Lemma descendandp1 : forall (v : V_set) a g pp p c,
  pp = parent' v a g p ->
  descendand' v a g c p = true ->
  descendand' v a g c pp = true.
Proof.
  intros v a g.
  unfold descendand in *. unfold parent.
  induction g ; simpl in * ; subst ; intuition.
  + unfold component_name in *.
    unfold eqn in *.
    repeat break_match ; subst ; intuition.
  + unfold component_name in *.
    unfold eqn in *.
    repeat break_match ; subst ; intuition ; simpl in *.
    apply (descendand_par _ _ _ (Checker x)) ; auto.
    apply (IHg (parent' v0 a0 g0 p) p (Checker x)) ; auto.
    apply descendand_inv2 in H0. simpl in H0. intuition.
    apply (IHg (parent' v0 a0 g0 p) p c) ; auto.
Qed.

Lemma parent_diff : forall c,
  c <> root' v a g ->
  parent' v a g c <> c.
Proof.
  intros.
  induction g ; subst ; simpl in * ; intuition.
  break_match.
  + subst.
    inversion H0.
    subst.
    intuition.
  + intuition.
Qed.

Lemma no_v_no_children : forall v0 a0 c y x,
  ~ v0 y ->
  ~ In (component_name y) (children' v0 a0 c (component_name x)).
Proof.
  intros.
  induction c ; intros ; simpl in *.
  + intuition.
  + assert (~ v0 y).
    intuition.
    apply H.
    apply In_right. auto. apply IHc in H0.
    assert (y <> y0).
    intuition. apply H.
    apply In_left. auto. subst. apply In_single.
    unfold not. intros.
    break_match.
      - simpl in H2.
        destruct H2. inversion e. inversion H2. subst. intuition.
        intuition.
      - intuition.
  + intuition.
  + rewrite <- e in *.
    intuition.
Qed.

Lemma NoDup_children: forall name,
  NoDup (children name).
Proof.
  intros.
  unfold children.
  induction g ; intros ; simpl in * ; intuition.
  + break_match ; subst.
    - assert (~ In (component_name y) (children' v0 a0 c (component_name x))).
      apply no_v_no_children ; auto.
      apply NoDup_cons ; auto.
    - auto.
Qed.

Lemma empty_subtree : forall v a g d h,
  descendand' v a g d h = true ->
  children' v a g h = [] ->
  d = h.
Proof.
  intros v a g.
  induction g ; unfold eqn in * ; repeat break_match ; subst ; simpl in * ; intuition.
    unfold eqn in H. apply andb_prop in H. destruct H. destruct (Name_eq_dec d h). intuition. inversion H0.
    repeat break_match ; subst ; simpl in * ; intuition ; unfold eqn in * ; repeat break_match ; subst ; simpl in * ; intuition.
    inversion H1.
    inversion H1.
    repeat break_match ; subst ; simpl in * ; intuition ; unfold eqn in * ; repeat break_match ; subst ; simpl in * ; intuition.
    inversion H0.
    inversion H0.
    assert (component_name x = h).
    apply (IHg (component_name x) h) ; auto.
    intuition.
Qed.

Lemma child_exists : forall v a g d p,
  descendand' v a g d p = true ->
  (d = p -> False) ->
  (exists child : Name, In child (children' v a g p) /\ descendand' v a g d child = true).
Proof.
  intros v a g.
  induction g ; unfold eqn in * ; repeat break_match ; subst ; simpl in * ; intuition.
  + unfold eqn in * ; repeat break_match ; subst ; simpl in * ; intuition.
    inversion H.
    inversion H.
  + unfold eqn in * ; repeat break_match ; subst ; unfold component_name in * ; simpl in * ; intuition.
    inversion e1. subst. intuition.
    exists (Checker y). repeat break_match ; subst ; intuition.
    specialize (IHg d (Checker x)). intuition. destruct H2. exists x0. split ; auto. destruct H1 ; auto. destruct H1 ; auto.
    specialize (IHg (Checker x) p). intuition. destruct H2. exists x0. split ; auto. destruct H1 ; auto. destruct H1 ; auto.
    repeat break_match ; subst ; intuition.
Qed.

Lemma descendand_trans : forall v a g c d (P : Name -> Prop),
  descendand' v a g d c = true ->
  P d ->
  (forall e d : Name,
    descendand' v a g e c = true ->
    In d (children' v a g e) ->
    P d -> P e) ->
  P c.
Proof.
  intros v a g.
  induction g ; simpl in * ; intuition ; unfold eqn in * ; unfold component_name in * ; repeat break_match ; subst ; intuition ; simpl in *.
  + inversion H.
  + inversion H.
  + inversion e0. subst. intuition.
  + inversion e0. subst. intuition.
  + assert (H1' := H1). apply (H1 (Checker x) (Checker y)) ; auto ; break_match ; subst ; intuition.
    apply descendand_refl ; auto.
  + apply (IHg (Checker x) d P) ; auto ; intros.
    assert (H1' := H1). apply (H1 e d0) ; auto ; break_match ; subst ; intuition.
  + apply descendand_inv2 in H. simpl in H. intuition.
  + assert (P (Checker x)).
    apply (H1 (Checker x) (Checker y)) ; auto. break_match ; subst ; intuition. break_match ; subst ; intuition.
    apply (IHg c (Checker x)) ; auto.
    intros. apply (H1 e d) ; auto. break_match ; subst ; intuition. break_match ; subst ; intuition.
  + apply (IHg c d P) ; auto ; intros.
    assert (H1' := H1). apply (H1 e d0) ; auto ; break_match ; subst ; intuition.
    apply descendand_inv1 in H2. simpl in H2. intuition.
Qed.

Lemma root_is_ancestor : forall (v : V_set) a g d,
  v (name_component d) ->
  descendand' v a g d (root' v a g) = true.
Proof.
  intros v a g.
  induction g ; simpl in * ; intuition.
  + inversion H. subst. rewrite cnnc. unfold eqn. break_match. auto. intuition.
  + inversion H. inversion H0. subst. rewrite cnnc in *. unfold eqn. repeat break_match ; intuition ; simpl in *.
    unfold eqn. repeat break_match ; intuition ; simpl in *.
  + rewrite <- e in *.
    intuition.
Qed.

End New_Spanning_Tree.