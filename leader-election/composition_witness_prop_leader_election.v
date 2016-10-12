Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.
Require Import Coq.Logic.Classical_Prop.





(* representation of network *)

Definition Component := Vertex.


Definition Component_index (c : Component):nat := match c with
                          | index x => x
                          end.

Definition C_set := U_set Component.

Definition C_list := U_list Component.


(*Axiom Component_Graph: forall (c:Component), v c.*)

Variable a:A_set.
Variable v:C_set.
Variable g : Connected v a.
Variable root: Component.
Variable rootprop: v root.

Fixpoint CA_list (v : V_set) (a : A_set) (c : Connected v a) {struct c} :
 A_list :=
  match c with
  | C_isolated x => A_nil
  | C_leaf v' a' c' x y _ _ => CA_list v' a' c'
  | C_edge v' a' c' x y _ _ _ _ _ =>
      A_ends x y :: A_ends y x :: CA_list v' a' c'
  | C_eq v' _ a' _ _ _ c' => CA_list v' a' c'
  end.

Fixpoint CV_list (v : V_set) (a : A_set) (c: Connected v a) {struct c} :
 V_list :=
  match c with
  | C_isolated x => x::V_nil
  | C_leaf v' a' c' x y _ _ => x :: CV_list v' a' c'
  | C_edge v' a' c' x y _ _ _ _ _  => CV_list v' a' c'
  | C_eq v' _ a' _ _ _ c' => CV_list v' a' c'
  end.

Lemma C_non_directed :forall (v : V_set) (a : A_set) (g : Connected v a) (x y : Vertex),
 a (A_ends x y) -> a (A_ends y x).
Proof.
intros.
apply Connected_Isa_Graph in g0.
apply G_non_directed with (v:=v0).
apply g0.
apply H.
Qed.

Definition neighbors (g : Connected v a) (c: Component) : C_list :=
(A_in_neighborhood c (CA_list v a g)) .


Variable leader :Component -> Component.

Variable parent : Component -> Component.

Variable distance : Component -> nat.


Section CompositionProperty.


(*local witness predicates*)

(* (x) technical detail : collection of the values of the functions (parent, distance, leader) 
in order to prove properties about the constructed functions  *) 

Definition gamma_i (i:Component)(leader_i:Component)(distance_i:nat)(parent_i:Component)(leader_parent_i:Component)(distance_parent_i:nat)
(leader_neighbors : C_list)
:Prop :=
leader i <>  i /\ 
parent i = parent_i /\  (* (x) *)
a (A_ends i parent_i) /\ 
a (A_ends parent_i i) /\
distance i = distance_i /\ (* (x) *) 
distance_parent_i = distance parent_i /\ (* consistency in neighbourhood ) *)
distance_i = distance_parent_i + 1 /\
leader i = leader_parent_i /\ (* (x) *)
leader_parent_i = leader (parent i)(* consistency in neighbourhood  *)
/\ ((forall (k:Component), In k leader_neighbors-> k = leader i))
/\ ((forall (c:Component) , In c (neighbors g i) -> In (leader c) leader_neighbors)). (*consistency in neighbourhood leader*)

Definition gamma_root (i:Component)(leader_i:Component)(distance_i:nat)(parent_i:Component)(leader_neighbors : C_list)
: Prop :=
leader i = leader_i /\  (* (x) *)
leader_i =  i  /\
parent i = parent_i /\  (* (x) *)
parent_i =  i /\
distance i = distance_i /\  (* (x) *)
distance_i = 0
/\ ((forall (k:Component), In k leader_neighbors-> k = leader i))
/\  ((forall (c:Component) , In c (neighbors g i) -> In (leader c) leader_neighbors)). 


(*Argument: Warum genau einmal gamma_root und ansonsten gamma_i*)

(*local witness predicates*)

Theorem composition_property:
forall (leader_root parent_root: Component)( distance_root : nat)(leader_neighbors_root : C_list), (gamma_root root leader_root distance_root parent_root leader_neighbors_root)  ->
forall (x:Component)(prop1: v x)(prop2: x <> root) (leader_i  parent_i leader_parent_i :Component )(distance_i distance_parent_i: nat)(leader_neighbors_i : C_list), 
(gamma_i x leader_i distance_i parent_i leader_parent_i distance_parent_i leader_neighbors_i ) -> 
distance root = 0 /\ distance x = distance (parent x) + 1 /\
leader root = root /\ leader x <>  x /\ leader x =  leader (parent x) /\
parent root = root /\ v (parent x)
/\ a (A_ends x (parent x)) /\ a (A_ends (parent x) x)
/\ (forall (c:Component), In c (neighbors g x) -> leader c = leader x) 
/\ (forall (c:Component), In c (neighbors g root) -> leader c = leader root). 
Proof.
intros.
unfold gamma_root in H.
unfold gamma_i in H0.
split.
destruct H as [j  [c [f [l [i  d]]]]].
rewrite i.
apply d.
split.
destruct H0 as [j_i  [c_i [f_i [l_i [i_i [m_i [n_i  d_i]]]]]]].
rewrite c_i.
rewrite <- m_i.
rewrite  i_i.
trivial.
split.
destruct H as [j  [c [f [l [i  d]]]]].
rewrite j.
trivial.
split.
destruct H0 as [j_i[k_i v_i]].
apply j_i.
split.
destruct H0 as [j_i  [c_i [f_i [l_i [i_i [m_i [n_i  d_i]]]]]]].
Focus 2.
split.
destruct H as [j  [c [f [l [i  d]]]]].
rewrite f. (*LEADER PROPS*)
apply l.
destruct H0 as [j_i  [c_i [f_i [l_i [i_i [m_i [n_i [p_i  d_i]]]]]]]].
apply C_ina_inv1 with (v:=v) (a:=a)  in l_i  .
rewrite <- c_i in l_i.
split.
trivial.
split.
rewrite <- c_i  in f_i.
trivial.
Focus 2.
apply g.
destruct d_i as [p q].
split.
rewrite <- c_i in f_i.
apply C_non_directed  with (v:=v)  in f_i .
trivial.
apply g.
split.
destruct q.
intros.
apply H0 with (k:=leader c).
apply H1 with (c:=c).
apply H2.
intros.
destruct H as [j_r  [c_r [f_r [l_r [i_r [m_r  d_r]]]]]].
destruct d_r.
apply H with (k:=leader c).
apply H1.
apply H0.
destruct d_i as [p [y q]].
rewrite p.
rewrite y.
trivial.
Qed.


End CompositionProperty.

Section GlobalWitnessProperty.


(**********************Global Witness Predicate holds for global winess******************)
(*LEADER PROPS*)
Axiom leader_root : leader root = root.

Axiom leader_prop : forall (x:Component)(prop :v x),
x <>root -> leader x <>  x /\ leader x =  leader (parent x).

Axiom leader_prop_ : forall (x:Component)(prop :v x),
leader x =  leader (parent x).

Axiom leader_neighbors_prop : forall (x:Component)(prop :v x),
forall (c:Component), In c (neighbors g x) -> leader c = leader x.

(*PARENT PROPS*)
Axiom parent_root : parent root = root.

Axiom parent_exists_ : forall (x :Component) (prop: v x), v (parent x).

Axiom parent_arc: forall (c k:Component)(prop: v c)(prop2: v k),
parent c = k -> a (A_ends c k) /\ a (A_ends k c).

(*DISTANCE PROPS*)

Axiom distance_root : distance root = 0 .
Axiom distance_prop : forall (x:Component)(prop :v x),
x <>root -> distance x = distance (parent x) + 1.

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
apply distance_prop in n.
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
rewrite (distance_prop comp).
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
a (A_ends (parent_iteration n x)  (parent_iteration (S n) x)) /\ a (  A_ends (parent_iteration (S n) x)(parent_iteration n x) ).
Proof.
intros.
apply parent_arc with (c:=parent_iteration n x) (k:=parent (parent_iteration n x))  .
apply parent_it_closed with (x:=x).
apply prop.
rewrite <- parent_it_prop.
apply parent_it_closed with (x:=x).
apply prop.
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
rewrite distance_prop in H.
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
rewrite distance_prop in H2.
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
rewrite distance_prop in H2.

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

(***************************************************************)


End GlobalWitnessProperty.
















