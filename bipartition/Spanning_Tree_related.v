Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.
Require Import Coq.Logic.Classical_Prop.


(* Edited and improved file of Samira Akilis Master's thesis (2018) - also in this git:
  leader-election/composition_witness_prop_leader_election.v *)

Section Spanning_Tree.
(************ Definitions of the tree with distance ************)

(* The set of components. *)
Variable v : V_set.
(* The set of arcs. *)
Variable a : A_set.
(* The network formed by the components and arcs. *)
Variable g : Connected v a.

(* Some special vertex of a tree. *)
Variable root: Vertex.
(* A function pointing to a neighbor in direction of root. *)
Variable parent : Vertex -> Vertex.
(* Distance to root. *)
Variable distance : Vertex -> nat.
(* Root is in the set of components. *)
Definition root_prop(c: Connected v a) := v root.
(* Property defining the parent function. *)

Definition parent_prop (x :Vertex) :=
x <> root /\ v (parent x) /\ a (A_ends x (parent x)) /\ a (A_ends (parent x) x)
\/
x=root /\ parent x = x.
(* Property defining the distance function. *)
Definition distance_prop (x: Vertex) :=
x <> root /\ distance x = distance (parent x) + 1
\/
(x=root) /\ distance x = 0.







Lemma parent_exists_ : (forall x,
  v x -> parent_prop x /\ distance_prop x) -> forall (x :Vertex) (prop: v x), v (parent x).
Proof.
  intros.
  specialize (H x). intuition. unfold parent_prop in H. unfold distance_prop in H1.
  intuition. subst. rewrite H2. auto.
Qed.

Fixpoint parent_iteration (n: nat) (c: Vertex) :Vertex:= match n with
| 0  =>  c
|(S n)  => parent (parent_iteration n  c) 
end.

(* "parent iteration" works one time as intented. *)
Lemma parent_it_prop : forall (n : nat) (c:Vertex),
parent_iteration (S n) c = parent (parent_iteration n c).
Proof.
intros.
auto.
Qed.

(* "parent iteration" always goes to components of the network. *)
Lemma parent_it_closed : (forall x,
  v x -> parent_prop x /\ distance_prop x) -> forall (x :Vertex)(n:nat) (prop: v x), v (parent_iteration n x).
Proof.
  intro spann.
intros. intuition. 
induction n.
unfold parent_iteration.
apply prop.
rewrite parent_it_prop.
apply parent_exists_ with (x:=parent_iteration n x) ; auto. 
Qed.

(* parent iteration only follows arcs existing in the network. *)
Lemma parent_it_arcs_induced: (forall x,
  v x -> parent_prop x /\ distance_prop x) -> forall (x:Vertex)(prop: v x)(n:nat), 
(parent_iteration n x) <> root -> a (A_ends (parent_iteration n x) (parent_iteration (S n) x)) /\ a (A_ends (parent_iteration (S n) x)(parent_iteration n x)).
Proof.
  intros spann.
intros.
assert (spann' := spann (parent_iteration n x)).
assert (v (parent_iteration n x)). apply parent_it_closed ; auto. intuition.
unfold parent_prop in H2. intuition.
unfold parent_prop in H2. intuition.
Qed.

(* parent iteration only follows arcs existing in the network. *)
Lemma parent_it_arcs_induced_left: (forall x,
  v x -> parent_prop x /\ distance_prop x) -> forall (x:Vertex)(prop: v x)(n:nat), 
(parent_iteration n x) <> root -> a (A_ends (parent_iteration n x) (parent_iteration (S n) x)).
Proof.
  intro spann.
intros. 
apply parent_it_arcs_induced with (n:=n)in prop.
destruct prop as [b c] .
apply b. auto.
apply H.
Qed.

(* parent iteration only follows arcs existing in the network. *)
Lemma parent_it_arcs_induced_right: (forall x,
  v x -> parent_prop x /\ distance_prop x) -> forall (x:Vertex)(prop: v x)(n:nat), 
(parent_iteration n x) <> root -> a (A_ends (parent_iteration (S n) x)(parent_iteration n x)).
Proof.
  intro spann.
intros. 
apply parent_it_arcs_induced with (n:=n)in prop.
destruct prop as [b c] .
apply c. auto.
apply H.
Qed.

(* Parent and parent_iteration are commutative together. *)
Lemma parent_it_commut: (forall x,
  v x -> parent_prop x /\ distance_prop x) -> 
(forall (x:Vertex) (n:nat) (prop1: v x),
(parent (parent_iteration  n x)) = (parent_iteration n (parent x))).
Proof.
  intros spann.
intros.
induction n.
unfold parent_iteration.
reflexivity.
rewrite parent_it_prop.
rewrite IHn.
rewrite parent_it_prop.
reflexivity.
Qed.


Lemma root_prop' : (forall x,
  v x -> parent_prop x /\ distance_prop x) -> v root.
Proof.
  unfold parent_prop. unfold distance_prop.
  intros.
  assert (forall x : Vertex,
    v x ->
    {x <> root /\ a (A_ends x (parent x)) /\
    distance x = 1 + distance (parent x)} + {x = root /\ parent x = x /\ distance x = 0}).
  intro x. destruct (V_eq_dec x root) as [rx|rx] ; specialize (H x) ; intuition.
  clear H.


  assert (forall x, v x -> (x = root \/ x <> root /\ exists p, v p /\ distance x = 1 + (distance p))).
  intros. specialize (H0 x). intuition. right. intuition.
  exists (parent x). intuition. admit.
  clear H0.

assert (exists x, v x) as vx.
  - induction g ; simpl in * ; subst ; intuition.
    + exists x. apply In_single.
    + exists y. apply In_left. apply In_single.
 -

  assert (g' := g).
  apply Connected_Isa_Graph in g'.
  assert (exists vl : V_list, forall v1, v v1 <-> In v1 vl). admit.
  destruct H0 as [vl vll].
  assert (forall x : Vertex,
    In x vl ->
    x = root \/
    x <> root /\ (exists p : Vertex, In p vl /\ distance x = 1 + distance p)).
  intros. specialize (H x). assert (vlll := vll). specialize (vll x). intuition.
  destruct H5. intuition. right. intuition. exists x0. intuition. apply (vlll x0). auto.
  apply (vll root). destruct vx as [x vx]. apply vll in vx.
  clear H. clear vll g' g v a parent.

  assert (exists x, In x vl /\ 

  generalize H0 vx. generalize x. generalize vl. clear H0 vx x vl.
  intro vl.

  induction vl ; intros ; intuition.
  simpl in *.
  destruct (V_eq_dec a root) as [aroot|aroot].
    subst. simpl. auto. simpl in *. right.
    assert (H0' := H0 x vx).
    intuition. subst. intuition.
    subst. auto.
    

    destruct vx. subst.

    simpl in *.
    destruct vx.
    subst.
    specialize (H0 x). intuition.
    right. destruct H2. destruct H. destruct H. subst.
    symmetry in H2. admit.
    
    
  


  induction x.
  assert (exists x, v x).
  - induction g ; simpl in * ; subst ; intuition.
    + exists x. apply In_single.
    + exists y. apply In_left. apply In_single.
    + exists x. auto.
  - destruct H1. apply H0 in H1. inversion H1.
  - simpl in *. intuition. clear H1.
    
  GV_list

(* assert (exists x, v x).
  - induction g ; simpl in * ; subst ; intuition.
    + exists x. apply In_single.
    + exists y. apply In_left. apply In_single.
  -  *)
    (* destruct H0.
    
    destruct (V_eq_dec x root). subst. auto.
    assert ((* forall x, v x -> x <> root -> *) (exists l: list (Vertex * Vertex), forall v1 v2, In (v1,v2) l -> v v1 /\ v v2 /\ 
            fst (hd (root, root) l) = x /\ snd (last l (x,x)) = root /\ 1 + (distance v1) = distance v2)).
    
    
 *)
 V_list

  induction g ; subst ; intuition.
  + admit.
  + destruct (V_eq_dec y root). subst. apply In_left. apply In_single.
    apply In_right.
    assert (H' := H x). assert (V_union (V_single y) v x). apply In_right. auto.
    specialize (H y). assert (V_union (V_single y) v y). apply In_left. apply In_single.
    intuition. subst. auto.
    clear H2 H3 H5.
    destruct H5 as [parx [disparx1 disparx2]].
    
  
  

  assert (exists x, v x /\ distance x = 0).



  assert (forall x:Vertex, v x -> parent_iteration (distance x) x = root).
  intros.
  assert (H0' := H0 x).  assert (H0'' := H0 (parent x)).
  assert (v (parent x)) as vp. admit.
  apply H0'' in vp. clear H0''.
  induction (distance x) ; intuition ; subst ; intuition.
  inversion H7. inversion H7.
  simpl. inversion H7. subst.
  




  admit.
  assert (exists x, v x).
  - induction g ; simpl in * ; subst ; intuition.
    + exists x. apply In_single.
    + exists y. apply In_left. apply In_single.
    + exists x. auto.
  - destruct H1.
    specialize (H x).
    intuition.
    rewrite <- H2.
    apply parent_it_closed ; auto. intro x0.
    assert (H0' := H0 x0).
    unfold parent_prop. unfold distance_prop.
    intuition.
    left. intuition.
    admit. admit.

(* exists, ..... -> Walk v a x root vl el *)
  assert(forall x, v x -> {vl : V_list & {el : E_list & {w : Walk v a x root vl el &
          ((forall v1 v2, In (E_ends v1 v2) el -> (v1 = parent v2 \/ v2 = parent v1)) /\
           length vl = distance x)}}}).
    intros.
    assert (H0' := H0 x).
    induction (distance x).
    + intuition. inversion H4. subst. admit.
    + 

    destruct (V_eq_dec x root) as [rx|rx] ; intuition.
    admit.
    induction H4.
    intuition.
    


  assert (exists x, v x).
  - induction g ; simpl in * ; subst ; intuition.
    + exists x. apply In_single.
    + exists y. apply In_left. apply In_single.
    + exists x. auto.
  - destruct H.
    assert (H0' := H0). specialize (H0' x).
    intuition.
    
    admit.
    subst. auto.
    

    apply IHn. intuition.
    specialize (H0 x). intuition.
    apply (H0 x).

    specialize (H0 root).
    intuition.
    
    induction (distance x) ; simpl in * ; subst ; intuition.
    
    

  assert (distance root = 0).
  induction g ; subst ; simpl in * ; intuition.
  + specialize (H0 x).
    assert (V_single x x). apply In_single. intuition.
    inversion H0.
    subst. auto.
  + assert (y = root \/ y <> root). apply classic. destruct H1 as [new|new].
    subst. clear H.
    assert (H0' := H0). specialize (H0' root).
    specialize (H0 x). assert (V_union (V_single root) v x). apply In_right. auto.
    assert (V_union (V_single root) v root). apply In_left. apply In_single.
    intuition.
    apply H. clear H.
    intros. assert (H0' := H0). specialize (H0' y).
    specialize (H0 x0). assert (V_union (V_single y) v x0). apply In_right. auto.
    assert (V_union (V_single y) v y). apply In_left. apply In_single.
    intuition. left. intuition. inversion H0 ; inversion H6 ; auto. inversion H7 ; inversion H10 ; subst ; intuition.
    rewrite <- H15 in *. intuition.
    rewrite <- H15 in *. rewrite H5 in H8.
    clear H5. induction (distance (parent x0)). inversion H8. inversion H8. auto.
    inversion H7 ; subst ; intuition.
    assert (Graph v a). apply Connected_Isa_Graph ; auto.
    apply (G_ina_inv1 v a H9) in H10. intuition.
  + assert (y = root \/ y <> root). apply classic. destruct H1 as [newy|newy].
    subst.
    assert (H0' := H0). specialize (H0' root).
    specialize (H0 x). assert (V_union (V_single root) v x). apply In_right. auto.
    intuition.
    assert (x = root \/ x <> root). apply classic. destruct H1 as [newx|newx].
    subst.
    assert (H0' := H0). specialize (H0' root).
    specialize (H0 y). assert (V_union (V_single root) v y). apply In_right. auto.
    intuition.

    destruct (V_eq_dec x (parent y)) as [newxx|newxx].
    subst. clear H.
    assert (H0' := H0). specialize (H0' y). specialize (H0 (parent y)).
    intuition.


    destruct (V_eq_dec y (parent x)) as [newyy|newyy].

    apply H ; intuition. clear H.
    assert (H0' := H0). specialize (H0' x). assert (H0'' := H0). specialize (H0'' x0).
    specialize (H0 y).

    intuition.
    left. intuition.
    inversion H2 ; inversion H0 ; inversion H7 ; auto.
    inversion H8 ; inversion H11 ; inversion H13 ; subst ; intuition.
    rewrite <- H17 in *. rewrite H4 in H6. admit.
    rewrite <- H17 in *. rewrite H4 in H6. admit.
    inversion H13 ; inversion H8 ; subst ; intuition.
    


(*  generalize H0. clear H0.

  induction g ; subst ; simpl in * ; intuition.
  + specialize (H0 x).
    assert (V_single x x). apply In_single. intuition.
    inversion H0.
    subst. apply In_single.
  + admit.
  + assert ((root = x \/ root = y) \/ ~ (root = x \/ root = y)).
    apply classic.
    destruct H1.
    destruct H1. subst. auto. subst. auto.
    assert (root <> x /\ root <> y).
    intuition.
    clear H1. destruct H2. *)



(* This is Gamma 1: there is a root component and the distance and 
   parent functions are correct in the whole network. *)
Definition spanning_tree (c: Connected v a) :=
root_prop c /\ (forall x, v x -> distance_prop x /\ parent_prop x).

(* The global spanning tree of this file. *)
Variable s : spanning_tree g.
(************ Definitions of the tree with distance ************)


(************ Some Lemmata that follow easily ************)
(* Root is its own parent. *)
Lemma parent_root : v root -> parent root = root.
Proof.
  intros rooted.
  unfold spanning_tree in s.
  destruct s.
  specialize (H0 root).
  assert (v root).
  apply rooted.
  apply H0 in H1.
  destruct H1.
  unfold parent_prop in H2.

  destruct H2.
  destruct H2.
  intuition.
  destruct H2.
  apply H3.
Qed.

(* The parent is part of the network. *)
Lemma parent_exists_ : forall (x :Vertex) (prop: v x), v (parent x).
Proof.
  intros.
  unfold spanning_tree in s.
  destruct s.
  specialize (H0 x).
  assert (propp := prop).
  apply H0 in prop.
  destruct prop.
  unfold parent_prop in H2.
  destruct H2.
  destruct H2.
  destruct H3.
  apply H3.
  destruct H2.
  rewrite H3.
  apply propp.
Qed.

(* For all components (not root) the parent of it is a neighbor. *)
Lemma parent_arc: forall (c k:Vertex)(prop: v c)(prop2: v k),
  c <> root -> parent c = k -> a (A_ends c k) /\ a (A_ends k c).
Proof.
  intros.
  unfold spanning_tree in s.
  destruct s.
  assert (H3 := H2).
  specialize (H2 c).
  specialize (H3 k).
  apply H3 in prop2.
  destruct prop2. unfold parent_prop in H5.
  apply H2 in prop.
  destruct prop.
  unfold parent_prop in H7.
  destruct H7.
  rewrite <- H0.
  destruct H7.
  destruct H8.
  apply H9.
  intuition.
Qed.

(* Root has distance of 0 to itself. *)
Lemma distance_root : distance root = 0.
Proof.
  intros.
  unfold spanning_tree in s.
  destruct s.
  specialize (H0 root).
  unfold root_prop in H.
  apply H0 in H.
  destruct H.
  unfold distance_prop in H.
  destruct H.
  intuition.
  destruct H.
  apply H2.
Qed.

(* For all other components the distance is one more, than of its parent. *)
Lemma distance_prop2 : forall (x:Vertex)(prop :v x),
x <>root -> distance x = distance (parent x) + 1.
Proof.
  intros.
  unfold spanning_tree in s.
  destruct s.
  specialize (H1 x).
  apply H1 in prop.
  destruct prop.
  unfold distance_prop in H2.
  destruct H2.
  destruct H2.
  apply H4.
  intuition.
Qed.

(* If some component has zero distance to root, it is root. *)
Lemma distance_root_ : forall (c:Vertex)(prop :v c),  distance c = 0 -> c = root.
Proof.
intros.
case (V_eq_dec  c root).
auto.
intros.
apply distance_prop2 in n.
omega.
apply prop.
Qed.

(* For most components the distance is greather than 0. *)
Lemma distance_greater_zero:
forall (comp: Vertex) (prop :v comp),
comp <> root -> distance comp > 0. 
Proof. 
intros.
rewrite (distance_prop2 comp).
elim distance.
auto.
intuition.
apply prop.
apply H.
Qed.

(* If distance is greater than zero, the component is not root. *)
Lemma distance_greater_zero_:
forall (comp: Vertex) (prop :v comp),
distance comp > 0 -> comp <> root. 
Proof.
intros.
case (V_eq_dec  comp root).
intros.
assert (distance comp <> 0). unfold not; intros. intuition.
unfold not ; intros.
rewrite H1 in H0.
assert (distance root = 0). apply distance_root.
intuition.
intros.
auto.
Qed.
(************ Some Lemmata that follow easily ************)





(************************* Auxiliary Function Parent_Iteration ***********************)
(* Function for: what is the nth next component on the path to root? *)
Fixpoint parent_iteration (n: nat) (c: Vertex) :Vertex:= match n with
| 0  =>  c
|(S n)  => parent (parent_iteration n  c) 
end.

(* "parent iteration" works one time as intented. *)
Lemma parent_it_prop : forall (n : nat) (c:Vertex),
parent_iteration (S n) c = parent (parent_iteration n c).
Proof.
intros.
auto.
Qed.

(* "parent iteration" always goes to components of the network. *)
Lemma parent_it_closed : forall (x :Vertex)(n:nat) (prop: v x), v (parent_iteration n x).
Proof.
intros.
induction n.
unfold parent_iteration.
apply prop.
rewrite parent_it_prop.
apply parent_exists_ with (x:=parent_iteration n x).
apply IHn.
Qed.

(* parent iteration only follows arcs existing in the network. *)
Lemma parent_it_arcs_induced: forall (x:Vertex)(prop: v x)(n:nat), 
(parent_iteration n x) <> root -> a (A_ends (parent_iteration n x) (parent_iteration (S n) x)) /\ a (A_ends (parent_iteration (S n) x)(parent_iteration n x)).
Proof.
intros.
apply parent_arc with (c:=parent_iteration n x) (k:=parent (parent_iteration n x)).
apply parent_it_closed with (x:=x).
apply prop.
rewrite <- parent_it_prop.
apply parent_it_closed with (x:=x).
apply prop.
apply H.
reflexivity.
Qed.

(* parent iteration only follows arcs existing in the network. *)
Lemma parent_it_arcs_induced_left: forall (x:Vertex)(prop: v x)(n:nat), 
(parent_iteration n x) <> root -> a (A_ends (parent_iteration n x)  (parent_iteration (S n) x)).
Proof.
intros. 
apply parent_it_arcs_induced with (n:=n)in prop.
destruct prop as [b c] .
apply b.
apply H.
Qed.

(* parent iteration only follows arcs existing in the network. *)
Lemma parent_it_arcs_induced_right: forall (x:Vertex)(prop: v x)(n:nat), 
(parent_iteration n x) <> root -> a (  A_ends (parent_iteration (S n) x)(parent_iteration n x) ).
Proof.
intros. 
apply parent_it_arcs_induced with (n:=n)in prop.
destruct prop as [b c] .
apply c.
apply H.
Qed.

(* Parent and parent_iteration are commutative together. *)
Lemma parent_it_commut:
(forall (x:Vertex) (n:nat) (prop1: v x),
(parent (parent_iteration  n x) )=  (parent_iteration n (parent x))).
Proof.
intros.
induction n.
unfold parent_iteration.
reflexivity.
rewrite parent_it_prop.
rewrite IHn.
rewrite parent_it_prop.
reflexivity.
Qed.
(************************* Auxiliary Function Parent_Iteration ***********************)


(************************* Inductive Type Connection : Trail defined by parent relation *************************)
(* Direction of construction : from parent to child *)
Inductive Connection:  Vertex -> Vertex -> A_list -> nat -> Set :=
  | self : forall x:Vertex,  v x -> Connection x x  A_nil 0
  | step : forall (x y z : Vertex)(al : A_list)(n:nat),
           Connection y z al n -> v x  -> parent x = y 
          -> a (A_ends x (parent x))  -> a (A_ends (parent x) x) 
       (*   -> ~ In (A_ends x (parent x))  el -> ~ In (A_ends (parent x) x)  el*)
          -> Connection x z ((A_ends (parent x) x ) :: al) (S n).

(* Direction of construction : from child to parent *)
Inductive Connection_up:  Vertex -> Vertex -> A_list -> nat -> Set :=
  | self_up : forall x:Vertex,  v x -> Connection_up x x  A_nil 0
  | step_up : forall (x y z : Vertex)(al : A_list)(n:nat),
           Connection_up z y al n -> v x  -> parent z = x 
          -> a (A_ends z (parent z))  -> a (A_ends (parent z) z) 
       (*   -> ~ In (A_ends x (parent x))  el -> ~ In (A_ends (parent x) x)  el*)
          -> Connection_up x y ((A_ends z (parent z)) :: al) (S n).

(* You can append Connections and they still form a correct Connection. *)
Lemma Connection_append :
 forall (x y z : Vertex)(el el' : A_list)(n n': nat),
 Connection x y el n ->
 Connection y z el' n'-> Connection x z (el ++ el') (n+n').
Proof.
        intros x y z el el' n n' Hw; elim Hw; simpl in |- *; intros.
        trivial.
        apply step with (y:=y0); auto.
Qed.

(* You can append Connections and they still form a correct Connection. *)
Lemma Connection_up_append :
 forall (x y z : Vertex)(el el' : A_list)(n n': nat),
Connection_up  z y  el' n' -> Connection_up  y x el n 
 -> Connection_up z x (el'++el) ( n + n').
Proof.
        intros x y z el el' n n' Hw.
        elim Hw.
        intros.
        simpl.
        assert( G: n + 0 = n).
        omega.  
        rewrite G.
        apply H.
        intros.   
        simpl.  
        assert( G: (n + S n0) = S (n0+n)).  
        omega.
        rewrite G.
        apply step_up with (y:= x).
        assert( I: (n0 + n) = (n + n0)).  
        omega.
        rewrite I.
        apply H.
        trivial.    
        trivial.
        trivial.
        trivial.
        trivial.
Qed.

(* Connection means Connection up. *)
Lemma Connection_Connection_up :
forall  (n:nat) (x y: Vertex)(prop1:v x)(prop2: v y), 
{al : A_list & Connection x y al n} -> {al : A_list & Connection_up y x al n}. 
Proof.
intros.
destruct H.
elim c.
simpl in |- *.
intros.
split with (A_nil).
apply self_up.
trivial.
intros.
destruct H.
split with (x2 ++ (A_ends  x1 (parent x1))::A_nil ).
apply Connection_up_append with 
(x:=x1) (y:=y0)  (z:=z)  (el' :=x2 )  (el:= (((A_ends  x1 (parent x1)) :: A_nil)) ) (n':=n0) (n:=1).
apply c1.
assert (parent x1 = parent_iteration 1 x1).
unfold parent_iteration.
auto.
assert (H':= v0). 
apply self_up in v0.
apply step_up with (x:=y0) in v0.
apply v0.
apply parent_exists_ in H'.
rewrite e in H'.
apply H'.
trivial.
trivial.
trivial.
Qed.
(************************* Inductive Type Connection : Trail defined by parent relation *************************)


(********************* Proof of Witness Property ******************************************)
(*path_to_root: inductive proof shows there is a path from root to each vertex via the parent relation *)
Lemma path_to_root:
forall (n:nat) (x:Vertex) (prop1 : v x),
v root ->  distance x = n -> {al : A_list & Connection x root al n }.
Proof.
intros n.
induction n.
intros x prop1 rooted.
split with A_nil. 
apply distance_root_ in H.
rewrite H.
apply self.
unfold spanning_tree in *.
destruct s.
apply rooted.
apply prop1.

(*Step*)
intros x prop1 rooted H.
destruct IHn with (x:= parent x) as [k i].
assert (H':= H). 
apply parent_exists_ in prop1.
apply prop1.
apply rooted.

unfold spanning_tree in s.
destruct s.
specialize (H1 x).
apply H1 in prop1.
destruct prop1.
unfold distance_prop in H2.

destruct H2.
destruct H2.
rewrite H in H4.
symmetry in H4.
intuition.

intuition.

apply (step x) in i.
exists (A_ends (parent x) x :: k).
apply i.
apply prop1.
reflexivity.
unfold spanning_tree in s.
destruct s.
specialize (H1 x).
apply H1 in prop1.
destruct prop1.
unfold parent_prop in H3.
destruct H3.
destruct H3.
intuition.
unfold distance_prop in H2.
destruct H2.
intuition.
destruct H2.
rewrite H4 in H.
inversion H.

unfold spanning_tree in s.
destruct s.
specialize (H1 x).
apply H1 in prop1.
destruct prop1.
unfold parent_prop in H3.
destruct H3.
destruct H3.
intuition.
unfold distance_prop in H2.
destruct H2.
intuition.
destruct H2.
rewrite H4 in H.
inversion H.
Qed.

(* parent_transitive_is_root shows that root is ancestor of every vertex  *)
Lemma parent_transitive_is_root :
forall  (n:nat) (x: Vertex)(prop1:v x), 
n= distance x ->  {al : A_list & Connection x root al (distance x)} -> root = parent_iteration (distance x) x .
Proof.
intros n .
induction n.
intros.
rewrite <- H.
unfold parent_iteration.
rewrite <- H in H0.
destruct H0.
inversion c.
trivial.

intros.
assert (S n  = distance x -> distance x > 0).
intuition.
rewrite <- H.
assert (H':= H). 
apply H1 in H.
apply distance_greater_zero_ in H.
rewrite  parent_it_prop.
Focus 2.
apply prop1.

rewrite IHn with (x:=parent x).
rewrite  <- parent_it_prop.
rewrite H'.

symmetry.

rewrite <- H'.
assert (distance x = S n -> distance (parent x) = n).
intros.
rewrite distance_prop2 in H2.
assert (distance (parent x) + 1 = S n -> distance (parent x) = n).
intuition.
apply H3.
apply H2.
apply prop1.
apply H.
rewrite H2.
rewrite  -> parent_it_prop.
rewrite parent_it_commut.
reflexivity.
apply prop1.
symmetry.
apply H'.
apply parent_exists_.
apply prop1.

assert (distance x = S n -> distance (parent x) = n).
intros.
rewrite distance_prop2 in H2.

assert (distance (parent x) + 1 = S n -> distance (parent x) = n).
intuition.
apply H3.
apply H2.
apply prop1.
apply H.
symmetry.
apply H2.
symmetry.
apply H'.
apply path_to_root with (x:=parent x).
apply parent_exists_.
apply prop1.
unfold spanning_tree in s.
destruct s.
apply H2.
reflexivity.
Qed.

(* If there is a Connection, there is a graphbasics walk with the same length. *)
Lemma Connection_to_walk: forall (n:nat)(x y:Vertex)(al:A_list),
  (Connection x y al n) -> {vl : V_list & {el: E_list & {w: Walk v a x y vl el & length el = n}}}.
Proof.
  intros n x y al c.
  induction c.

  exists V_nil. exists E_nil.
  assert (Walk v a x x V_nil E_nil) as w.
  apply W_null.
  apply v0.
  exists w.
  reflexivity.

  destruct IHc as [vl [el [w_old llength]]].
  rewrite e in a0. rewrite e in a1.
  exists (y :: vl).
  exists ((E_ends x y) :: el).
  assert (Walk v a x z (y :: vl) ((E_ends x y) :: el)) as w_new.
  apply W_step.
  apply w_old.
  apply v0.
  apply a0.
  exists w_new.
  simpl.
  rewrite <- llength.
  reflexivity.
Qed.

(* For all components there is a path to root with the length of the distance to root. *)
Lemma path_to_root2:
forall (x:Vertex) (prop1 : v x),
{al : A_list & Connection x root al (distance x)}.
Proof.
  intros x prop1.
  assert (forall (n:nat) (x:Vertex) (prop1 : v x), v root ->  distance x = n -> {al : A_list & Connection x root al n }).
  apply path_to_root.
  specialize (H (distance x) x prop1).
  unfold spanning_tree in s.
  destruct s.
  unfold root_prop in H0.
  apply H in H0.
  apply H0.
  reflexivity.
Qed.

End Spanning_Tree.