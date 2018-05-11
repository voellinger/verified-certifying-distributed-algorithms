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

Definition descendand' (v : V_set) (a : A_set) (c : Connected v a) (des ancestor : Name) : Prop :=
  exists vl el, exists (w : Walk v a (name_component des) (name_component ancestor) vl el), parent_walk' (name_component des) (name_component ancestor) vl el v a c w.

Definition descendand (des ancestor : Name) : Prop :=
  descendand' v a g des ancestor.

(* Function descendand2' (v : V_set) (a : A_set) (c : Connected v a) (des ancestor : Name) : bool :=
  if (Name_eq_dec des ancestor) then 
    true else 
    (eqb (Name_eqb des (parent des)) false) && descendand2' v a c (parent des) ancestor. *)

Function eqn n1 n2 : bool :=
  if (Name_eq_dec n1 n2) then true else false.

Fixpoint des' (v : V_set) (a : A_set) (c : Connected v a) (descendand ancestor : Name) : bool :=
  match c with
  | C_isolated x => (eqn ancestor (component_name x)) && eqn descendand ancestor
  | C_leaf v a co x y _ _ => 
      if (Name_eq_dec descendand (component_name y)) then
        (eqn ancestor (component_name x)) || 
        (eqn ancestor (component_name y)) || 
        (des' v a co (component_name x) ancestor) else
         des' v a co descendand ancestor
  | C_edge v a co x y _ _ _ _ _ => des' v a co descendand ancestor
  | C_eq v v' a a' _ _ co => des' v a co descendand ancestor
  end.

Definition des'' (descendand ancestor : Name) : bool :=
  des' v a g descendand ancestor.

Axiom finite_sets : forall (v : V_set) (y : Vertex), {v y} + {~ v y}.


Lemma W_backstep :
 forall v a (x y z : Vertex) (vl : V_list) (el : E_list),
 Walk v a x z (y :: vl) el -> {el' : E_list &  Walk v a y z vl el'}.
Proof.
        intros; inversion H.
        split with el0; trivial.
Qed.


Lemma Walk_in_smaller : forall v0 a0 (c0 : Connected v0 a0) x y des vl el,
  v0 x ->
  (v0 y -> False) ->
  v0 des ->
  Walk (V_union (V_single y) v0) (A_union (E_set x y) a0) des x vl el ->
  {vl : V_list & {el : E_list & Walk v0 a0 des x vl el}}.
Proof.
  intros v0 a0 c0.
(*   induction H2.
  + exists []. exists []. apply W_null. auto.
  + assert ({v0 y0} + {~ v0 y0}).
    apply finite_sets.
    destruct H3.
    intuition.
    admit.
    assert (y0 = y). admit. subst.
    assert (x0 = x). admit. subst. *)


  induction c0 ; simpl in * ; intuition.
  + inversion H. inversion H1. subst. exists []. exists []. apply W_null. apply In_single.
  + specialize (IHc0 x y des). 
    assert ({y = des} + {y <> des}).
    apply V_eq_dec.
    destruct H3.
    subst.
    admit.
    assert (v0 des).
    inversion H1. inversion H3. subst. intuition. auto.
    inversion H2.
    admit.
    subst.
    apply W_backstep in H2.
    

(* 
Lemma descendand_descendands : forall des anc : Name, v (name_component des) -> v (name_component anc) -> 
  (descendand des anc <-> (des'' des anc = true)).
Proof.
  intros.
  unfold descendand. unfold des''. unfold parent_walk'. split ; intros.
  repeat destruct H1.
  induction g ; intros ; simpl in * ; intuition.
  + inversion H. inversion H0.
    subst. apply name_comp_name in H3. subst. rewrite cnnc. unfold eqn. break_match. auto.
    intuition.
  + inversion H.
    inversion H2. subst.
    simpl in *.
    inversion H0. inversion H3. subst. simpl in *. rewrite cnnc in *.
    break_match.
      apply name_comp_name in H6.
      subst.
      unfold eqn. destruct (Name_eq_dec anc anc). intuition. intuition. intuition.
    subst. rewrite cnnc in *.
    break_match. 
      inversion H. inversion H4. subst.
       
      
  
  + subst.
    exists []. exists [].
    assert (Walk (V_single x) A_empty (name_component des) (name_component des) [] []).
    apply W_null ; auto.
    exists H1.
    unfold parent_walk'. intros. inversion H2. *)

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
      
      
      
     

(* Lemma parent_child_is_treeify : forall (v : V_set) (a : A_set) (c : Connected v a) (a' : A_set) (t : Tree v a'),
  eq_list_set (treeify_a v a c) a' ->
  (forall child p, v (name_component child) -> v (name_component p) -> ((In child (children' v a c p) \/ (p = parent' v a c (child) /\ child <> root' v a c)) <-> (a' (A_ends (name_component child) (name_component p))))).
Proof.
  intros v a c.
  induction c ; intros ; simpl in * ; subst ; auto ; intuition.
  + subst.
    simpl in *.
    inversion H0.
    subst.
    rewrite cnnc in H4.
    intuition.
  + unfold eq_list_set in H.
    apply <- H in H2.
    inversion H2.
  + simpl in *.
    break_match.
      - subst.
        simpl in *.
        destruct H3.
        subst. simpl.
        unfold eq_list_set in H.
        apply H ; auto.
        simpl ; auto.
        inversion H0.
          inversion H3.
          subst.
          unfold eq_list_set in H.
          apply H ; auto.
          simpl ; auto.

          subst.
          inversion H1.
          inversion H4.
          subst.
          assert (a' (A_ends x x)).
          unfold eq_list_set in H.
          apply H. simpl ; auto.
          assert (~ a' (A_ends x x)).
          induction t.
            inversion H5.
            intuition.
            rewrite <- e in *.
            rewrite <- e0 in *.
            intuition.
          intuition.
          subst.

          assert ({a' : A_set & {t : Tree v0 a' & eq_list_set (treeify_a v0 a0 c) a'}}).
          apply treeify_creates_tree.
          destruct X.
          destruct s.
          assert (x0 (A_ends (name_component child) x)).
          apply (IHc x0 x1 e child (Checker x)) ; auto.
          unfold eq_list_set in *.
          simpl in H. specialize (H (A_ends (name_component child) x)). destruct H.
          apply H.
          right. right.
          apply <- e ; auto.
      -
  +    
 *)

(* Definition xor (p1 p2 : Prop) : Prop :=
 (~p1 /\ p2) \/ (p1 /\ ~ p2). *)

(*  was danach noch kommen k\u00f6nnte:
    parent-child<->a'
    irgendwie zeigen, dass der treeify-baum dann nur aus eltern/kinder-kanten besteht
    also die \u00e4quivalenz der kanten
    danach \u00fcber den baum iterieren, der entstanden ist
*)

(**************************************************)    
(* alle Axiome nach-definieren und lemmatisieren
     *)
(**************************************************)

(* Axiom children_parent : forall (c : Name),
  {In c (children (parent c))} + {c = root}.

Axiom c_arcs : forall (p c : Name),
  In c (children p) -> a (A_ends (name_component p) (name_component c)).

Axiom p_arcs : forall (c : Name),
  {a (A_ends (name_component c) (name_component (parent c)))} + {c = root}. *)



Lemma descendandp1 : forall pp p c,
  pp = parent p ->
  descendand c p ->
  descendand c pp.
Proof.
  intros pp p c H H0.
  assert (p = root \/ p <> root) as pnoroot.
  apply classic.
  destruct pnoroot as [proot|pnoroot].
    subst.
    unfold parent.
    rewrite parent_root.
    unfold root in H0.
    auto.
  
  unfold descendand in * ; intros.
  repeat destruct H0.
  assert (Walk v a (name_component c) (name_component pp) (x ++ [name_component pp]) (x0 ++ [E_ends (name_component p) (name_component pp)])).
  apply (Walk_append v a (name_component c) (name_component p)) ; auto.
  apply (W_step) ; auto.
  apply W_null.
  apply Component_prop_1.
  apply Component_prop_1.
  assert ((a (A_ends (name_component pp) (name_component p)) /\ a (A_ends (name_component p) (name_component pp)))).
  apply (parent_arcs pp p) ; auto.
  apply Component_prop_1.
  destruct H1.
  auto.
  exists (x ++ [name_component pp]).
  exists (x0 ++ [E_ends (name_component p) (name_component pp)]).
  exists H1.
  unfold parent_walk' in * ; simpl in * ; intros.
  apply in_app_or in H2.
  destruct H2.
  + auto.
  + inversion H2.
    unfold parent in *.
    inversion H3.
    apply name_comp_name in H5.
    apply name_comp_name in H6.
    subst.
    auto.
    inversion H3.
Qed.

Lemma descendand_refl : forall n,
  descendand n n.
Proof.
  intros.
  unfold descendand.
  exists []. exists [].
  assert (Walk v a (name_component n) (name_component n) [] []).
  apply W_null ; auto.
  apply Component_prop_1.
  exists H. unfold parent_walk'.
  intros.
  inversion H0.
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


Lemma descendand_par : forall c p,
  p = parent c ->
  descendand c p.
Proof.
  intros.
  assert (c = root \/ c <> root).
  apply classic.
  destruct H0.
  subst. unfold root. unfold parent.
  rewrite parent_root.
  apply descendand_refl.

  subst.

  unfold descendand. unfold parent.

  assert (a (A_ends (name_component c) (name_component (parent' v a g c)))).

  apply (parent_isin_a v a g) ; auto.
  apply Component_prop_1.
  apply Component_prop_1.
  apply parent_diff ; auto.
  exists ([(name_component (parent' v a g c))]).
  exists ([E_ends (name_component c) (name_component (parent' v a g c))]).
  assert (Walk v a (name_component c) (name_component (parent' v a g c)) [(name_component (parent' v a g c))] [E_ends (name_component c) (name_component (parent' v a g c))]).
  apply W_step ; auto.
  apply W_null ; auto.
  apply (parent_help2 v a g c) ; auto.
  apply Component_prop_1.
  exists H1.
  unfold parent_walk'.
  intros.
  inversion H2.
  inversion H3 ; subst ; auto.
  apply name_comp_name in H6 ; auto.
  apply name_comp_name in H5 ; auto.
  subst. auto.
  inversion H3.
Qed.



End New_Spanning_Tree.