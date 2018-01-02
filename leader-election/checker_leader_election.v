Require Import GraphBasics.Graphs.
Require Import GraphBasics.Trees.
Require Import Coq.Logic.Classical_Prop.

Load composition_witness_prop_leader_election.
Require Export Coq.Bool.BoolEq.
Extraction Language Haskell. 





Record local_input: Set := mk_local_input {
  i : Component;
  neighbours : C_list;
}.

Record checker_input : Set := mk_checker_input {
leader_i : Component;
distance_i : nat;
parent_i : Component;
distance_parent_i : nat;
leader_parent_i : Component;
leader_neighbors_i : C_list;
}.


Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Definition beq (n m : Component) : bool :=
beq_nat (Component_index n) (Component_index m). 


 (*Variable beq : Component -> Component -> bool.*)

  Variable beq_refl : forall x:Component, true = beq x x.

  Variable beq_eq : forall x y:Component, true = beq x y -> x = y.

  Variable beq_eq_true : forall x y:Component, x = y -> true = beq x y.

  Variable beq_eq_not_false : forall x y:Component, x = y -> false <> beq x y.

  Variable beq_false_not_eq : forall x y:Component, false = beq x y -> x <> y.

 Variable exists_beq_eq : forall x y:Component, {b : bool | b = beq x y}.

 Variable not_eq_false_beq : forall x y:Component, x <> y -> false = beq x y.

  Variable eq_dec : forall x y:Component, {x = y} + {x <> y}.



Definition construct_local_input(g: Connected v a)  (c: Component) :  local_input :=
mk_local_input c (neighbors g c).



Axiom neighbours_neighbors: forall  (l: local_input) (g: Connected v a) (c: Component), 
l.(neighbours) = neighbors g c.


Fixpoint In_bool (a: Component) (l:C_list) : bool:=
  match l with
  | nil => false
  | b :: m => beq b a || In_bool a m
  end.

Axiom Inbool_In: forall (a: Component) (l:C_list),
In_bool a l  = true <-> In a l.



Lemma parent_neighbors_: forall (c:Component)(k:Component),
a (A_ends c k) <-> In k (A_in_neighborhood c (CA_list v a g)).
Proof.
Admitted.

Lemma parent_neighbors: forall (c:Component),
a (A_ends c (parent c)) <-> In (parent c) (A_in_neighborhood c (CA_list v a g)).
Proof.
intros.
unfold iff.
refine (conj _ _).
intros.
apply  parent_neighbors_ with (k:=parent c) (c:= c).
trivial.
intros.
apply  parent_neighbors_ with (k:=parent c) (c:= c).
trivial.
Qed.

Fixpoint forallb_neighbors (l:C_list) (c:Component) : bool :=
      match l with
        | nil => true
        | a::k => beq a c && forallb_neighbors k c
      end.

Axiom forallb_forall_ : forall (l:C_list) (c:Component) (x:Component),
(forallb_neighbors l c = true) <-> (In x l ->  x = c).




Definition checker (l: local_input) (c : checker_input) : bool :=
(((negb (beq c.(leader_i) l.(i))) && beq c.(leader_i) c.(leader_parent_i))
 &&  beq_nat c.(distance_i) ( c.(distance_parent_i)+1 ) && In_bool c.(parent_i) l.(neighbours)) &&
(forallb_neighbors c.(leader_neighbors_i) c.(leader_i))||

beq c.(leader_i) l.(i) && beq_nat c.(distance_i) 0 && beq  c.(parent_i) l.(i) &&
(forallb_neighbors c.(leader_neighbors_i) c.(leader_i)).


Extraction beq_nat.
Extraction beq.
Extraction checker. 


(****  
Extraction of checker to Haskell, works analogously for the programming languages Scheme and OCaml.


beq_nat :: Nat -> Nat -> Bool

beq_nat n m =
  case n of {
   O ->
    case m of {
     O -> True;
     S _ -> False};
   S n' ->
    case m of {
     O -> False;
     S m' -> beq_nat n' m'}}

beq :: Component -> Component -> Bool

beq n m =
  beq_nat (component_index n) (component_index m)

checker :: Local_input -> Checker_input -> Bool

checker l c =
  orb
    (andb
      (andb
        (andb
          (andb (negb (beq (leader_i c) (i l)))
            (beq (leader_i c) (leader_parent_i c)))
          (beq_nat (distance_i c)
            (add (distance_parent_i c) (S O))))
        (in_bool (parent_i c) (neighbours l)))
      (forallb_neighbors (leader_neighbors_i c)
        (leader_i c)))
    (andb
      (andb
        (andb (beq (leader_i c) (i l))
          (beq_nat (distance_i c) O))
        (beq (parent_i c) (i l)))
      (forallb_neighbors (leader_neighbors_i c)
        (leader_i c)))


 ****)






Definition construct_checker  (g: Connected v a )  : list (checker_input -> bool) :=
map checker (map (construct_local_input g) ( CV_list v a g)).

(****  assumption about consistency in neighbourhood ****)

Definition leaderconsistency (i: Component)(leader_parent_i: Component):Prop:=
leader_parent_i = leader (parent i).

Definition distanceconsistency (i: Component) (distance_parent_i : nat):Prop:=
distance_parent_i = distance (parent i).

Definition neighboursconsistency (i: Component)(leader_neighbours_i: C_list):Prop:=
forall (c:Component), In c (neighbors g i) -> In (leader c) leader_neighbours_i .


Definition componentconsistency (i: Component)(leader_i parent_i : Component) (distance_i : nat) :Prop:=
leader_i = leader i /\ distance_i = distance i /\ parent_i = parent i.

(* (x) technical detail -> see local witness predicate *)
(*******)

Theorem checker_correctness (l: local_input) (c:checker_input):
(leaderconsistency l.(i) c.(leader_parent_i)) /\ (distanceconsistency l.(i) c.(distance_parent_i)) /\ (componentconsistency l.(i) c.(leader_i) c.(parent_i) c.(distance_i)/\
(neighboursconsistency l.(i) c.(leader_neighbors_i))  )
 -> 
(checker l c = true) <->  ((gamma_i l.(i) c.(leader_i) c.(distance_i) c.(parent_i) c.(leader_parent_i)  c.(distance_parent_i)  c.(leader_neighbors_i)
\/ gamma_root l.(i) c.(leader_i) c.(distance_i)  c.(parent_i) c.(leader_neighbors_i) )).


Proof.
intros.
unfold iff.
refine (conj _ _).
intros.
unfold checker in H0.
(** checker_i -> gamma_i****)
unfold gamma_i.
unfold leaderconsistency in H.
unfold componentconsistency in H.
unfold neighboursconsistency in H.
apply  orb_true_iff in H0.
destruct H0.
apply  andb_true_iff in H0.
destruct H0.
apply  andb_true_iff in H0.
destruct H0.
apply  andb_true_iff in H0.
destruct H0.
apply  andb_true_iff in H0.
destruct H0.

left.
assert (negb (beq (leader_i c) (i l)) = true -> beq (leader_i c) (i l) = false).
Focus 1.
intros.
apply negb_false_iff in H5.
rewrite negb_involutive in H5.
apply H5.
apply H5 in H0.
symmetry in H0.
apply beq_false_not_eq in H0.
destruct H as [lip [dip [li  pi ]]].
destruct li as [li1 [li2 li3]].
rewrite  li1 in H0.
split.
trivial.
split.
symmetry.
trivial.
split.

(***In neighbours --> Arcs exist****)
Focus 1. 
apply Inbool_In in H2.
rewrite li3.
apply parent_neighbors.
rewrite neighbours_neighbors with (g:=g) (c:=i l) in H2 .
unfold neighbors in H2.
rewrite  li3 in H2.
intuition.
split.
apply C_non_directed with (v:=v).
apply g.


Focus 1. 
apply Inbool_In in H2.
rewrite li3.
apply parent_neighbors.
rewrite neighbours_neighbors with (g:=g) (c:=i l) in H2 .
unfold neighbors in H2.
rewrite  li3 in H2.
intuition.


(***In neighbours --> Arcs exist****)



split.
symmetry.
trivial.
split.
unfold distanceconsistency in dip.
rewrite <- li3 in dip.
trivial.
split.

apply beq_nat_true in H3.
trivial.
split.
rewrite li1 in H4.
symmetry in H4.
apply beq_eq in H4.
trivial.
split.
intuition.
(*neighbors leader prop*)
intros.


split.
intros.
apply forallb_forall_ with (x:=k) in H1.
rewrite <- li1.
trivial.
trivial.
trivial.

(*(** checker_root -> gamma_root****)*)
right.
unfold gamma_root.
destruct H as [lip [dip [li pi]]].
split.
symmetry.
destruct li as [li1 [li2 li3]].
trivial.
split.
apply  andb_true_iff in H0.
destruct H0.
apply  andb_true_iff in H.
destruct H.
apply  andb_true_iff in H.
destruct H.
symmetry in H.
apply beq_eq in H.
trivial.
split.
symmetry.
destruct li as [li1 [li2 li3]].
trivial.
split.
destruct li as [li1 [li2 li3]].
trivial.
apply  andb_true_iff in H0.
destruct H0.
apply  andb_true_iff in H.
destruct H.
symmetry in H1.
apply beq_eq in H1.
trivial.
split.
symmetry.
destruct li as [li1 [li2 li3]].
trivial.
apply  andb_true_iff in H0.
destruct H0.
apply  andb_true_iff in H.
destruct H.
apply  andb_true_iff in H.
destruct H.
apply beq_nat_true in H2.
split.
trivial.
split.

intros.
apply forallb_forall_ with (x:=k) in H0.
destruct li as [li1 [li2 li3]].
rewrite <- li1.
trivial.
trivial.
apply pi.


(** gamma_i -> checker_i ****)

intros.
unfold checker.
apply orb_true_iff.
destruct H0.
unfold gamma_i in H0.
destruct H0 as [lip [dip [li [di [ki [hi [pi [mi zi]]]]]]]].
left.
apply  andb_true_iff.
split.
apply  andb_true_iff.
split.
apply  andb_true_iff.
split.
apply  andb_true_iff.
split.
assert (  beq (leader_i c) (i l) = false  -> negb (beq (leader_i c) (i l)) = true).

Focus 1.
intros.
apply negb_false_iff.
rewrite negb_involutive.
apply H0.


apply H0.
symmetry.
apply not_eq_false_beq.
trivial.
unfold componentconsistency in H.
destruct H as  [oi [gi [ri qi]]].
destruct ri as [ri1 [ri2 ri3]].
rewrite <- ri1 in lip.
trivial.
symmetry.
apply beq_eq_true.


destruct H as  [oi [gi ri]].
destruct ri as [ri1 ri3].
unfold componentconsistency in ri1.
destruct ri1 as [ri11 [ri12 ri13]].
rewrite <- ri11 in mi.
trivial.
apply beq_nat_true_iff.
trivial.

Focus 1. 
apply Inbool_In.
rewrite neighbours_neighbors with (g:=g) (c:=i l) .
unfold neighbors.
assert (HZ:In (i l)
  (A_in_neighborhood (parent_i c) (CA_list v a g)) -> In (parent_i c)
  (A_in_neighborhood (i l) (CA_list v a g))  ).
intros.
apply parent_neighbors_ with (k:= parent_i c).
apply li.
apply HZ.
apply parent_neighbors_ with (k:= i l ).
apply di.
apply forallb_forall_ with (x:=leader_i c).
destruct zi.

destruct H1.
intros.
trivial.
(** gamma_root -> checker_root ****)
right.
unfold gamma_root in H0.
apply  andb_true_iff.
split.
apply  andb_true_iff.
split.
apply  andb_true_iff.
split.
symmetry.
apply beq_eq_true.


destruct H0 as  [oi [gi [ri [wi qi]]]].
apply gi.
Focus 2.
symmetry.
apply beq_eq_true.

destruct H0 as  [oi [gi [ri [wi qi]]]].
apply wi.
apply beq_nat_true_iff.
destruct H0 as  [oi [gi [ri [wi [zi [qi vi]]]]]].
trivial.
destruct H0 as  [oi [gi [ri [wi [zi [qi vi]]]]]].
destruct vi.

apply forallb_forall_ with (x:=leader_i c).
intros.
trivial.
Qed.
