

(* Teil des Zeugen, bzw. Teil des Interfacemodels vom CDA *)
Variable parent : Vertex -> Vertex.
Variable distance : Vertex -> nat.
Variable color : Vertex -> bool.
Variable root: Vertex.
(* Variable v1 : Vertex. *)
(*  *)




(* Gamma 1 *)
Definition spanning_tree (c: Connected v a) :=
root_prop c /\ (forall x, v x -> distance_prop x /\ parent_prop x).
(* Distributable-Theorem von Samira klauen *)







(* Theorem for Gamma 2 being existentially distribubility,  (Annahmen Gamma1 und gamma2) *)
Theorem special_vertices_make_odd_closed: 
  forall (v:V_set) (a:A_set) (c : Connected v a) (t : spanning_tree v a root parent distance c)(x y: Component),

  special_vertices v a c t x y ->

{vlx : V_list & {vly : V_list & {elx: E_list & {ely: E_list & {w: Walk v a y y (x :: (vlx ++ vly)) ((E_ends y x) :: (elx ++ ely)) & 
odd_closed y y (x :: (vlx ++ vly)) ((E_ends y x) :: (elx ++ ely)) w}}}}}.












Definition bipartite (v : V_set) (a : A_set) (g: Graph v a) :=
  bipartite3 a.

Definition colored_spanning_tree (v: V_set) (a:A_set) (c: Connected v a):=
  spanning_tree v a root parent distance c -> (color root = true /\ forall (x : Component), (v x /\ x <> root) -> color x <> color (parent x)).

Definition colored_spanning_tree2 (v: V_set) (a:A_set) (c: Connected v a):=
  spanning_tree v a root parent distance c -> forall (x : Component), odd (distance x) -> color x = false /\ even (distance x) -> color x = true.

Lemma spanning_trees_can_be_colored: forall (v : V_set) (a : A_set) (c: Connected v a),
  spanning_tree v a root parent distance c -> colored_spanning_tree v a c.
Admitted.

Lemma no_special_vertices_make_connected_bi: forall (v : V_set) (a : A_set) (c: Connected v a) (t: spanning_tree v a root parent distance c),
  ~ (exists (x : Component), exists (y : Component), special_vertices v a c t x y) -> bipartite3 a.
Proof.
  intros v a c t H.
  assert (cst := t).
  apply (spanning_trees_can_be_colored v a c) in cst.
  unfold colored_spanning_tree in cst.
  destruct cst as [cst1 cst2].
  apply t.
  unfold not in H.
  unfold special_vertices in H.
  unfold bipartite3.
  unfold spanning_tree in t.
  destruct t as [t1 t2].
  unfold root_prop in t1.
  destruct ar.
  intros.
  exists v0 in H.
  specialize (cst2 v0).
  specialize (t2 v0).


(* TODO: 
  - intros -> intros v a ...
  - bipartiteness of a graph, not of arcs --> Gammas of a graph etc.
  - sort and delete unneeded stuff
  - /usr/local/lib/coq/theories/Init/Nat.vo
*)