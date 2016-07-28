Section GRAPH.
Require Import List.
Require Import Arith Omega.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Le.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Logic.Classical_Prop.

Definition set n := { x : nat | x < n }.

Record graph : Set := mk_graph {
  V : nat;
  E : (set V) -> (set V) -> nat;
  s : (set V)
}.

Check graph.

Inductive path (g : graph) : 
  list (set g.(V)) -> (** vertices along the path **)
  set g.(V) ->        (** last vertex of the path **)
  set g.(V) ->        (** first vertex of the path **)
  nat ->              (** total cost of the path **)           
  Prop :=
  | zerop : forall v,
          path g (v::nil) v v 0 
  | consp : forall u v, 
          g.(E) u v > 0 ->
            forall p sv d, path g (u::p) u sv d ->
              path g (v::u::p) v sv (d + g.(E) u v).

Check path_ind.
Check nat_ind.

Definition shortest_path (g : graph) (p : list (set g.(V))) 
  (v sv : set g.(V)) (d : nat) :=
  path g p v sv d /\ forall p' d', path g p' v sv d' -> d <= d'.

Variable g : graph.

Lemma lastv_auxilary : forall p d v,
  path g p v g.(s) d -> 
    exists p', path g (v::p') v g.(s) d. 
Proof. 
  intros.
  inversion H.
  {
    exists (nil). 
    apply zerop.
  }
  {
    exists (u::p0). 
    apply consp. 
    apply H0. 
    apply H1.
  }
Qed.

Lemma shortest_path_opt_substructure : forall u v p d, 
  g.(E) u v > 0 ->
    shortest_path g (v::u::p) v g.(s) (d + g.(E) u v) -> 
      shortest_path g (u::p) u g.(s) d.
Proof.
  intros u v p d HE_uv HSP_vup.
  destruct (classic (shortest_path g (u::p) u g.(s) d)) as [HSP_up | notHSP_up].
  assumption.
  exfalso.
  unfold shortest_path in notHSP_up.
  apply not_and_or in notHSP_up.
  destruct notHSP_up as [notHP_up|notHSP_up].
  {
    (* discard the left part of the disjunction in not_HSP_up *)
    assert (HP_up : path g (u::p) u g.(s) d).
    unfold shortest_path in HSP_vup.
    destruct HSP_vup as [HP_vup HSP_vup].
    inversion HP_vup.
    assert (A : d = d0).
    omega.
    rewrite <- A in H6.
    assumption.
    tauto.
  }
  (* a little first order reasoning provides, that
     there must be a (hypothetical) path from g.(s) 
     to u which is shorter than d *)
  apply not_all_ex_not in notHSP_up.
  destruct notHSP_up as [p' HP_up'].
  apply not_all_ex_not in HP_up'.
  destruct HP_up' as [d' HP_up'].
  apply imply_to_and in HP_up'.
  (* we use the edge (u, v) to create a hypothetical
     path to v, which is shorter than d + g.(E) u v.
     this contradicts HSP_vup  *)
  destruct HP_up' as [HP_up' Hd_gt_d'].
  apply lastv_auxilary in HP_up'.
  destruct HP_up' as [p'' HP_up].
  apply consp with (p := p'') (d := d') (sv := g.(s)) in HE_uv.
  destruct HSP_vup as [HP_vup HSP_vup].
  apply HSP_vup in HE_uv.
  omega.
  assumption.
Qed.

End GRAPH.
