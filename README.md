# Verified Certifying Distributed Algorithms

## License
GNU General Public License

## What is this repository for?

This repository is a collection of verified certifying distributed 
algorithms. A certifying algorithm computes for an input x an output y and 
additionally a witness w. If a so called witness predicate holds for a
triple (x,y,w), then the input-output pair (x,y) is correct. 
A simple checker algorithm decides the witness predicate at runtime.
The user of a certifying algorithm does not have to trust the algorithm but 
(1) has to understand why the witness predicate implies correctness, and
(2) to trust the checker algorithm. 
Rizkallah combines certifying algorithms with theorem proving for (1) and
program verification for (2). Thus, if the verified checker program
accepts for a triple (x,y,w), then there is a machine-checked proof that the
input-output pair (x,y) is correct.
For further informations check out the [Wikipedia-page](https://en.wikipedia.org/wiki/Certifying_algorithm) 
with its listed references from Mehlhorn, Rizkallah and others.

We adapt Rizkallahs method to certifying distributed algorithms (CDA) and build a
collection of verified certifiying distributed algorithms.
We use the proof assistant Coq for program verification as well as for
theorem proving, and use Coq's program extraction.


## How do I get set up?

Install [Coqide](https://coq.inria.fr/download) in version 8.5pl2 or 
later. Start it with the parameter `coqide -impredicative-set`. Further 
compile and install ![GraphBasics](https://github.com/coq-contribs/graph-basics) and ![Verdi](http://verdi.uwplse.org/). If you need further help, do not hesitate to contact us!


##Framework

###Proof Obligations

**PO I**
The implemented termination detection is correct.
 -- work in progress

**PO II**
Witness predicate Γ has the following properties:

**(i)** Γ has the witness property.

**(ii)** Γ is distributable.

See Case Studies as described below:
https://github.com/voellinger/verified-certifying-distributed-algorithms/tree/master/leader-election
https://github.com/voellinger/verified-certifying-distributed-algorithms/tree/master/shortest-path-problem


**PO III** The Theorem 1 for distributed checking of consistency.

See https://github.com/voellinger/verified-certifying-distributed-algorithms/tree/master/framework/consistency


**PO IV** The implemented distributed checker is correct:

**(i)** Each sub-checker checks if its sub-witness is complete.
-- work in progress

**(ii)** Each sub-checker takes part in checking if the witness is connected.
-- work in progress


**(iii)** Each sub-checker checks the consistency sub-witnesses in the 
neighborhood.
See https://github.com/voellinger/verified-certifying-distributed-algorithms/tree/master/framework/consistency

**(iv)** Each sub-checker decides the sub-predicates for its component.

See Case Studies as described below:
https://github.com/voellinger/verified-certifying-distributed-algorithms/tree/master/leader-election
https://github.com/voellinger/verified-certifying-distributed-algorithms/tree/master/shortest-path-problem

**(v)** Each sub-checker takes part in evaluation of Γ.
-- work in progress

Moreover, as a foundation, we have a model of the network (topology and communication) and the interface of a
CDA.

See https://github.com/voellinger/verified-certifying-distributed-algorithms/tree/master/framework/newtorkmodel


## Case Studies

### Certifying Leader Election:
This case study is published at [NFM17](https://link.springer.com/chapter/10.1007%2F978-3-319-57288-8_27).

#### Files:

**composition_witness_prop_leader_election.v**:
the formalisation and machine checked proofs for the witness property and the
composition property

**checker_leader_election.v**:
verified local checkers with possibility of program extraction


### Certifying Distributed Bipartite Testing:
The certifying variant of distributed bipartite testing will be 
published at RV17 but not the coq formalisation.

#### Files:
**Bipartition_related.v**:
The formalisation and machine checked proofs for the witness property and the composition property.


**Spanning_Tree_related.v**:
Reusing and adapting **composition_witness_prop_leader_election.v** of _Certifying Leader Election_ some more lemmata 
are shown.

All other files consist of minor lemmata, that are needed in the proofs for the theorem in **Bipartition_related.v**, 
or that came up, while trying to solve it.


### Certifying Shortest Path Construction:
The certifying variant of distributed shortest path construction is
published at [SEFM15](https://link.springer.com/chapter/10.1007%2F978-3-319-22969-0_14) but not the coq formalisation.


