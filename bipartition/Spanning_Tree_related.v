Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.
Require Import Coq.Logic.Classical_Prop.

Section Spanning_Tree.


(************ Definitions of the tree with distance ************)

Variable v:V_set.
Variable a:A_set.
Variable g : Connected v a.


Variable root: Vertex.

Variable parent : Vertex -> Vertex.

Variable distance : Vertex -> nat.

Definition root_prop(c: Connected v a) := v root.

Definition parent_prop (x :Vertex) :=
x <> root /\ v (parent x) /\ a (A_ends x (parent x)) /\ a (A_ends (parent x) x)
\/
x=root /\ parent x = x.

Definition distance_prop (x: Vertex) :=
forall (x:Vertex), 
x <> root /\ distance x = distance (parent x) + 1
\/
(x=root) /\ distance x = 0.

Definition spanning_tree (c: Connected v a) :=
root_prop c /\ (forall x, v x -> distance_prop x /\ parent_prop x).
(* maybe we have to get rid of the \/ in spanning_tree *)

Variable s : spanning_tree g.
(************ Definitions of the tree with distance ************)









(************ Some Lemmata that follow easily ************)
Lemma parent_root : v root -> parent root = root.
Proof.
  intros rooted.
  unfold spanning_tree in s.
  destruct s.
  unfold root_prop in H0.
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

Lemma parent_exists_ : forall (x :Vertex) (prop: v x), v (parent x).
Proof.
  intros.
  unfold spanning_tree in s.
  destruct s.
  unfold root_prop in H0.
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
  specialize (H root).
  destruct H.
  intuition.
  destruct H.
  apply H2.
Qed.

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
  specialize (H2 x).
  destruct H2.
  destruct H2.
  apply H4.
  intuition.
Qed.

Lemma C_eq_dec : forall x y : Vertex, {x = y} + {x <> y}.
Proof.
  simple destruct x; simple destruct y; intros.
  case (eq_nat_dec n n0); intros.
  left; rewrite e; trivial.
  right; injection; trivial.
Qed.

Lemma distance_root_ : forall (c:Vertex)(prop :v c),  distance c = 0 -> c = root.
Proof.
intros.
case (C_eq_dec  c root).
auto.
intros.
apply distance_prop2 in n.
omega.
apply prop.
Qed.

Lemma distance_root_2 : forall (c:Vertex)(prop :v c),  c = root -> distance c = 0.
Proof.
intros.
rewrite H.
apply distance_root.
Qed.

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

Lemma distance_greater_zero_:
forall (comp: Vertex) (prop :v comp),
distance comp > 0 -> comp <> root. 
Proof.
intros.
case (C_eq_dec  comp root).
intros.
apply distance_root_2 in e.
omega.
apply prop.
auto.
Qed.
(************ Some Lemmata that follow easily ************)





(************************* Auxiliary Function Parent_Iteration ***********************)
Fixpoint parent_iteration (n: nat) (c: Vertex) :Vertex:= match n with
| 0  =>  c
|(S n)  => parent (parent_iteration n  c) 
end.


Lemma parent_it_prop : forall (n : nat) (c:Vertex),
parent_iteration (S n) c = parent (parent_iteration n c).
Proof.
intros.
auto.
Qed.

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

Lemma parent_it_arcs_induced: forall (x:Vertex)(prop: v x)(n:nat), 
(parent_iteration n x) <> root -> a (A_ends (parent_iteration n x)  (parent_iteration (S n) x)) /\ a (A_ends (parent_iteration (S n) x)(parent_iteration n x)).
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

Lemma parent_it_arcs_induced_left: forall (x:Vertex)(prop: v x)(n:nat), 
(parent_iteration n x) <> root -> a (A_ends (parent_iteration n x)  (parent_iteration (S n) x)).
Proof.
intros. 
apply parent_it_arcs_induced with (n:=n)in prop.
destruct prop as [b c] .
apply b.
apply H.
Qed.

Lemma parent_it_arcs_induced_right: forall (x:Vertex)(prop: v x)(n:nat), 
(parent_iteration n x) <> root -> a (  A_ends (parent_iteration (S n) x)(parent_iteration n x) ).
Proof.
intros. 
apply parent_it_arcs_induced with (n:=n)in prop.
destruct prop as [b c] .
apply c.
apply H.
Qed.


Lemma parent_aux_1:
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


Lemma Connection_append :
 forall (x y z : Vertex)(el el' : A_list)(n n': nat),
 Connection  x y el n ->
 Connection  y z  el' n'-> Connection  x z (el ++ el') (n+n').
Proof.
        intros x y z el el' n n' Hw; elim Hw; simpl in |- *; intros.
        trivial.
        apply step with (y:=y0); auto.
Qed.

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
unfold root_prop. 
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
specialize (H2 x).

destruct H2.
destruct H2.
rewrite H in H4.
symmetry in H4.
intuition.

intuition.


apply step in i.
specialize (IHn x prop1 rooted).
destruct IHn.





rewrite distance_prop2 in H.
assert (H1: distance (parent x) + 1 = S n -> distance (parent x) = n ).
intuition.
apply H1.
apply H.
apply prop1.
assert (distance x = S n -> distance x > 0).
intuition.
apply H0 in H.
apply distance_greater_zero_ in H.
apply H.
apply prop1.
split with ((A_ends (parent x) x ) :: k).
apply step with (y:= parent x).
apply i.
apply prop1.
reflexivity.
assert (H':= prop1). 
apply parent_exists_ in prop1.
apply parent_arc with (c:=x) in prop1 .
assert (H'':= prop1). 
destruct prop1 .
apply H0.
apply H'.
assert (distance x = S n -> distance x > 0).
intuition.
apply H0 in H.
apply distance_greater_zero_ in H.
trivial. trivial.
reflexivity.
assert (H'':= prop1). 
apply parent_exists_ in prop1.
apply parent_arc with (c:=x) in prop1 .
destruct prop1 .
apply H1.
apply H''.
assert (distance x = S n -> distance x > 0).
intuition.
apply H0 in H.
apply distance_greater_zero_ in H.
trivial. trivial.
reflexivity.
Qed.




(* parent_transitive_is_root shows that root is ancestor of every vertex  *)
Lemma parent_transitive_is_root :
forall  (n:nat) (x: Vertex)(prop1:v x), 
n= distance x ->  {al : A_list & Connection x root al (distance x) } -> root = parent_iteration (distance x) x .
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
rewrite parent_aux_1.
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
reflexivity.
Qed.

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



End Spanning_Tree.