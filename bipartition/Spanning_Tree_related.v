Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.
Require Import Coq.Logic.Classical_Prop.


Section Spanning_Tree.







(* representation of network *)

Definition Component := Vertex.


Definition Component_index (c : Component):nat := match c with
                          | index x => x
                          end.

Definition C_set := U_set Component.

Definition C_list := U_list Component.


(* Axiom Component_Graph: forall (c:Component), v c. *)

Variable a:A_set.
Variable v:C_set.
Variable g : Connected v a.


Variable root: Component.

Variable parent : Component -> Component.

Variable distance : Component -> nat.

Definition root_prop(c: Connected v a) := v root.

Definition parent_prop (x: Component) (v: C_set) :=
forall (x :Component), 
x <> root /\ v (parent x) /\ a (A_ends x (parent x)) /\ a (A_ends (parent x) x)
\/
x=root /\ parent x = x.

Definition distance_prop (x: Component) :=
forall (x:Component), 
x <> root /\ distance x = distance (parent x) + 1
\/
(x=root) /\ distance x = 0.

Definition spanningtree (c: Connected v a) :=
root_prop (c) /\ (forall x, v x -> distance_prop x /\ parent_prop x v).

Variable span_tree : spanningtree g.

(* Definition spanningtree (c: Connected v a) :=
root_prop (c) /\ 
  (forall x, v x -> 
    {x = root /\ distance x = 0 /\ parent x = x} +
    {x <> root /\ v (parent x) /\ a (A_ends x (parent x)) /\ a (A_ends x (parent x)) /\ distance x = distance (parent x) + 1}).
 *)
















(*CA_list: all arcs of a Connected-graph*)
Fixpoint CA_list (v : V_set) (a : A_set) (c : Connected v a) {struct c} :
 A_list :=
  match c with
  | C_isolated x => A_nil
  | C_leaf v' a' c' x y _ _ => CA_list v' a' c'
  | C_edge v' a' c' x y _ _ _ _ _ =>
      A_ends x y :: A_ends y x :: CA_list v' a' c'
  | C_eq v' _ a' _ _ _ c' => CA_list v' a' c'
  end.

(*CV_list: all vertices of a Connected-graph*)
Fixpoint CV_list (v : V_set) (a : A_set) (c: Connected v a) {struct c} :
 V_list :=
  match c with
  | C_isolated x => x::V_nil
  | C_leaf v' a' c' x y _ _ => x :: CV_list v' a' c'
  | C_edge v' a' c' x y _ _ _ _ _  => CV_list v' a' c'
  | C_eq v' _ a' _ _ _ c' => CV_list v' a' c'
  end.

(*C_non_directed: each arc in a connected graph is bidirectional*)
Lemma C_non_directed :forall (v : V_set) (a : A_set) (g : Connected v a) (x y : Vertex),
 a (A_ends x y) -> a (A_ends y x).
Proof.
intros.
apply Connected_Isa_Graph in g0.
apply G_non_directed with (v:=v0).
apply g0.
apply H.
Qed.

(*neighbors: all neighboring vertices of a vertex*)
Definition neighbors (g : Connected v a) (c: Component) : C_list :=
(A_in_neighborhood c (CA_list v a g)) .





(************************local witness predicates***********************)

(* (x) technical detail : collection of the values of the functions (parent, distance, leader) 
in order to prove properties about the constructed functions  *) 

(* gamma_i: local witness predicate of ordinary vertices (all but the root) *)
Definition gamma_i (i:Component)(distance_i:nat)(parent_i:Component)(distance_parent_i:nat)
:Prop :=
parent i = parent_i /\  (* (x) *)
a (A_ends i parent_i) /\
a (A_ends parent_i i) /\
distance i = distance_i /\ (* (x) *)
distance_parent_i = distance parent_i /\ (* consistency in neighbourhood ) *)
distance_i = distance_parent_i + 1.

(* gamma_root: local witness predicate of the root node *)
Definition gamma_root (i:Component)(distance_i:nat)(parent_i:Component)
: Prop :=
parent i = parent_i /\  (* (x) *)
parent_i =  i /\
distance i = distance_i /\  (* (x) *)
distance_i = 0.


(*Why gamma_root exactly once and in all other cases gamma_i?*)
(* There is exactly one leader: the root. The leader is its own leader and has distance 0. All others have a leader different from themselves 
and a distance of one more than their parent. *)
(************************local witness predicates************************)

Theorem composition_property:
forall ( parent_root: Component)( distance_root : nat), (gamma_root root  distance_root parent_root)  ->
forall (x:Component)(prop1: v x)(prop2: x <> root) (  parent_i  :Component )(distance_i distance_parent_i: nat), 
(gamma_i x distance_i parent_i  distance_parent_i  ) -> 
distance root = 0 /\ distance x = distance (parent x) + 1 /\
parent root = root /\ v (parent x)
/\ a (A_ends x (parent x)) /\ a (A_ends (parent x) x). 
Proof.
intros.
unfold gamma_root in H.
unfold gamma_i in H0.
destruct H as  [f [l [i  d]]].
destruct H0 as [c_i [f_i [l_i [i_i [m_i n_i]]]]].

split.
rewrite i.
apply d.
split.
rewrite c_i.
rewrite <- m_i.
rewrite  i_i.
trivial.
split.
rewrite f. (*LEADER PROPS*)
apply l.
apply C_ina_inv1 with (v:=v) (a:=a)  in l_i  .
rewrite <- c_i in l_i.
split.
trivial.
split.
rewrite <- c_i  in f_i.
trivial.
Focus 2.
apply g.
rewrite <- c_i in f_i.
apply C_non_directed  with (v:=v)  in f_i .
trivial.
apply g.
Qed.




Axiom rooted : v root.

Lemma parent_root : parent root = root.
Proof.
  unfold spanningtree in span_tree.
  destruct span_tree.
  unfold root_prop in H0.
  specialize (H0 root).
  assert (v root).
  apply rooted.
  apply H0 in H1.
  destruct H1.
  unfold parent_prop in H2.
  specialize (H2 root).
  destruct H2.
  destruct H2.
  intuition.
  destruct H2.
  apply H3.
Qed.

Lemma parent_exists_ : forall (x :Component) (prop: v x), v (parent x).
Proof.
  intros.
  unfold spanningtree in span_tree.
  destruct span_tree.
  unfold root_prop in H0.
  specialize (H0 x).
  assert (propp := prop).
  apply H0 in prop.
  destruct prop.
  unfold parent_prop in H2.
  specialize (H2 x).
  destruct H2.
  destruct H2.
  destruct H3.
  apply H3.
  destruct H2.
  rewrite H3.
  apply propp.
Qed.

Lemma parent_arc: forall (c k:Component)(prop: v c)(prop2: v k),
  c <> root -> parent c = k -> a (A_ends c k) /\ a (A_ends k c).
Proof.
  intros.
  unfold spanningtree in span_tree.
  destruct span_tree.
  assert (H3 := H2).
  specialize (H2 c).
  specialize (H3 k).
  apply H3 in prop2.
  destruct prop2. unfold parent_prop in H5.
  specialize (H5 c).
  destruct H5.
  destruct H5 as [i [j l]].
  rewrite <- H0.
  apply l.
  intuition.
Qed.

Lemma distance_root : distance root = 0.
Proof.
  intros.
  unfold spanningtree in span_tree.
  destruct span_tree.
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




Lemma distance_prop2 : forall (x:Component)(prop :v x),
x <>root -> distance x = distance (parent x) + 1.
Proof.
  intros.
  unfold spanningtree in span_tree.
  destruct span_tree.
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

(***************************************************************************)



(**************************** Auxiliary Lemmas **************************************)

Lemma C_eq_dec : forall x y : Component, {x = y} + {x <> y}.
Proof.
  simple destruct x; simple destruct y; intros.
  case (eq_nat_dec n n0); intros.
  left; rewrite e; trivial.
  right; injection; trivial.
Qed.



Lemma distance_root_ : forall (c:Component)(prop :v c),  distance c = 0 -> c = root.
Proof.
intros.
case (C_eq_dec  c root).
auto.
intros.
apply distance_prop2 in n.
omega.
apply prop.
Qed.

Lemma distance_root_2 : forall (c:Component)(prop :v c),  c = root -> distance c = 0.
Proof.
intros.
rewrite H.
apply distance_root.
Qed.


(*Lemma: All components have distance greater than zero except for root *)

Lemma distance_greater_zero:
forall (comp: Component) (prop :v comp),
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
forall (comp: Component) (prop :v comp),
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

(************************* Auxiliary Function Parent_Iteration ***********************)

Fixpoint parent_iteration (n: nat) (c: Component) :Component:= match n with
| 0  =>  c
|(S n)  => parent (parent_iteration n  c) 
end.


Lemma parent_it_prop : forall (n : nat) (c:Component),
parent_iteration (S n) c = parent (parent_iteration n c).  
Proof.
intros.
auto.
Qed.

Lemma parent_it_closed : forall (x :Component)(n:nat) (prop: v x), v (parent_iteration n x).
Proof.
intros.
induction n.
unfold parent_iteration.
apply prop.
rewrite parent_it_prop.
apply parent_exists_ with (x:=parent_iteration n x).
apply IHn.
Qed.

Lemma parent_it_arcs_induced: forall (x:Component)(prop: v x)(n:nat), 
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

Lemma parent_it_arcs_induced_left: forall (x:Component)(prop: v x)(n:nat), 
a (A_ends (parent_iteration n x)  (parent_iteration (S n) x)).
Proof.
intros. 
apply parent_it_arcs_induced with (n:=n)in prop.
destruct prop as [b c] .
apply b.
Qed.

Lemma parent_it_arcs_induced_right: forall (x:Component)(prop: v x)(n:nat), 
a (  A_ends (parent_iteration (S n) x)(parent_iteration n x) ).
Proof.
intros. 
apply parent_it_arcs_induced with (n:=n)in prop.
destruct prop as [b c] .
apply c.
Qed.


Lemma parent_aux_1:
(forall (x:Component) (n:nat) (prop1: v x),
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



Lemma parent_aux_2:
forall (x:Component) (n:nat) (prop1: v x),
leader (parent (parent_iteration (S n) x)) =
leader (parent_iteration n (parent x)).
Proof.
intros.
induction n.
unfold parent_iteration.
rewrite -> leader_prop_ with (x:=parent x).
reflexivity.
apply parent_exists_.
apply prop1.
rewrite parent_it_prop.
rewrite -> leader_prop_ with (x:=parent (parent_iteration (S n) x)) in IHn.
rewrite IHn.
rewrite parent_it_prop.
rewrite -> leader_prop_ with (x:=parent_iteration n (parent x)).
reflexivity.
apply parent_it_closed with (x:=parent x) (n:=n).
apply parent_exists_.
apply prop1.
rewrite <- parent_it_prop.
apply parent_it_closed with (x:= x) (n:=(S (S n))).
apply prop1.
Qed.


(***************************************************************)

(*********** Inductive Type Connection : Trail defined by parent relation ***************)

(* Direction of construction : from parent to child *)
Inductive Connection:  Vertex -> Vertex -> A_list -> nat -> Set :=
  | self : forall x:Vertex,  v x -> Connection x x  A_nil 0
  | step : forall (x y z : Vertex)(el : A_list)(n:nat),
           Connection y z el n -> v x  -> parent x = y 
          -> a (A_ends x (parent x))  -> a (A_ends (parent x) x) 
       (*   -> ~ In (A_ends x (parent x))  el -> ~ In (A_ends (parent x) x)  el*)
          -> Connection x z ((A_ends (parent x) x ) :: el) (S n).

(* Direction of construction : from child to parent *)
Inductive Connection_up:  Vertex -> Vertex -> A_list -> nat -> Set :=
  | self_up : forall x:Vertex,  v x -> Connection_up x x  A_nil 0
  | step_up : forall (x y z : Vertex)(el : A_list)(n:nat),
           Connection_up z y el n -> v x  -> parent z = x 
          -> a (A_ends z (parent z))  -> a (A_ends (parent z) z) 
       (*   -> ~ In (A_ends x (parent x))  el -> ~ In (A_ends (parent x) x)  el*)
          -> Connection_up x y ((A_ends z (parent z)) :: el) (S n).


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

(*It exists a connection between a vertex k and the result of parent_iteration n k with the length n*)
Lemma walk_to_parent_it: forall  (n:nat)(c k: Component)(el  : A_list) (prop1:v c),
parent_iteration n c = k -> {el : A_list  & Connection_up k c el n}.
Proof.
intros n.
induction n.
intros.
split with (A_nil).
unfold parent_iteration in H.
rewrite H.
apply self_up.
rewrite <- H.
apply prop1.
intros.
rewrite parent_it_prop in H.
destruct IHn with (c:=c)(k:=parent_iteration n c).
apply el.
apply prop1. 
reflexivity.
split with (A_ends (parent_iteration n c) (parent (parent_iteration n c))  ::x).
rewrite <- H.
apply step_up with
(y:= c)(x:=(parent (parent_iteration n c)))(z:=parent_iteration n c)(n:=n)(el:=x).
apply c0.
rewrite <- parent_it_prop.
apply parent_it_closed with (x:=c).
apply prop1.
reflexivity.
rewrite <- parent_it_prop.
apply parent_it_arcs_induced_left with (x:=c).
apply prop1.
apply parent_it_arcs_induced_right with (x:=c).
apply prop1.
Qed.

(*Exists connection between parent and child*)
Lemma walk_to_parent: forall (c k: Component)(el  : A_list) (prop1:v c),
parent c = k -> {el : A_list  & Connection c k el 1}.
Proof.
intros.
split with (A_ends k c ::A_nil).
rewrite <- H.
apply step with (y:=parent c).
apply self.
apply parent_exists_ in prop1.
apply prop1.
apply prop1.
reflexivity.
apply parent_arc with (c:=c)(k:=parent c) in prop1 .
destruct prop1.
apply H0.
apply parent_exists_ in prop1.
apply prop1.
reflexivity.
apply parent_arc with (c:=c)(k:=parent c) in prop1 .
destruct prop1.
apply H1.
apply parent_exists_ in prop1.
apply prop1.
reflexivity.
Qed.




Lemma Connection_Connection_up :
forall  (n:nat) (x y: Component)(prop1:v x)(prop2: v y), 
{el : A_list & Connection x y el n} -> {el : A_list & Connection_up y x el n}. 
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



(***************************************************************)

(********************* Proof of Witness Property ******************************************)
(*path_to_root: inductive proof shows there is a path from root to each vertex via the parent relation *)

Lemma path_to_root:
forall (n:nat) (x:Component) (prop1 : v x),
distance x = n -> {el : A_list & Connection x root el n }.
Proof.
intros n.
induction n.
intros.
split with A_nil. 
apply distance_root_ in H.
rewrite H.
apply self.
apply rootprop.
apply prop1.

(*Step*)
intros.
destruct IHn with (x:= parent x) as [k i].
assert (H':= H). 
apply parent_exists_ in prop1.
apply prop1.
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
reflexivity.
assert (H'':= prop1). 
apply parent_exists_ in prop1.
apply parent_arc with (c:=x) in prop1 .
destruct prop1 .
apply H1.
apply H''.
reflexivity.
Qed.


(*Every vertex agrees on the leader with its parent and thereby recursivly with its ancestors *)
Lemma parent_is_leader:
forall (n:nat)(x y: Component)(prop1: v x) (prop2:v y), 
 leader x = leader (parent_iteration n x).
Proof.
intros n.
induction n.
intros.
unfold parent_iteration.
reflexivity.
intros.
rewrite  IHn with (y:=parent_iteration n x).
rewrite leader_prop_.
rewrite parent_it_prop.
reflexivity.
apply parent_it_closed with (x:=x).
apply prop1.
apply prop1.
apply parent_it_closed with (x:=x).
apply prop1.
Qed.




(* parent_transitive_is_root shows that root is ancestor of every vertex  *)
Lemma parent_transitive_is_root :
forall  (n:nat) (x: Component)(prop1:v x), 
n= distance x ->  {el : A_list & Connection x root el (distance x) } -> root = parent_iteration (distance x) x .
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





Theorem global_witness_property:

exists (l : Component), v l -> forall (x:Component)(prop1: v x), leader x = l.
Proof.
exists root.
intros.
case (C_eq_dec  x root).
intros.
rewrite e.
apply leader_root.
intros.
rewrite parent_is_leader with (n:=distance x) (y:=root).
apply leader_prop in n.
destruct n.
symmetry.
rewrite <- parent_transitive_is_root with (n:=distance x) (x:=x) .
symmetry.
apply leader_root.
apply prop1.
reflexivity.
apply path_to_root with (n:=distance x).

apply prop1.
reflexivity.
apply prop1.
apply prop1.
apply rootprop.

Qed.

End Spanning_Tree.
(***************************************************************)


(*
Section GlobalWitnessProperty2.
Axiom leader_root : leader root = root.
Hint Resolve leader_root : core.

Axiom leader_prop_ : forall x, v x -> leader x =  leader (parent x).

Axiom parent_exists_ : forall x, v x -> v (parent x).
Hint Resolve parent_exists_ : core.

Axiom distance_prop2 : forall x, v x -> x<>root -> distance x = S (distance (parent x)).

Lemma C_eq_dec : forall x y : Component, {x = y} + {x <> y}.
Proof.
  destruct x as [n], y as [m]; destruct (eq_nat_dec n m); subst; auto.
  right; intro d; inversion d; subst; omega.
Qed.

Theorem global_witness_property2 :
  forall x, v x -> leader x = root.
Proof.
  intros x pvx.
  auto.
  remember (distance x) as dx.
  revert dependent x.
  induction dx; intros x vx dxx.

  { destruct (C_eq_dec x root) as [d|d]; subst; auto.
    apply distance_prop2 in d; auto; omega. }

  { destruct (C_eq_dec x root) as [d|d]; subst; auto.
    apply distance_prop2 in d; auto.
    rewrite d in dxx.
    inversion dxx as [xx]; clear dxx d.
    apply IHdx in xx; auto.
    rewrite <- leader_prop_ in xx;auto. }
Qed.

Theorem global_witness_property3 :
  exists l, v l -> forall x, v x -> leader x = l.
Proof.
  exists root; intro vr.
  apply global_witness_property2.
Qed.
End GlobalWitnessProperty2.
*)