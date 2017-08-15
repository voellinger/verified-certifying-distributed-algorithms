# Verified Certifying Distributed Algorithms

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
For further informations check out the ![Wikipedia-page](https://en.wikipedia.org/wiki/Certifying_algorithm) 
with its listed references from Mehlhorn, Rizkallah and others.

We adapt Rizkallahs method to certifying distributed algorithms and build a
collection of verified certifiying distributed algorithms.
We use the proof assistant Coq for program verification as well as for
theorem proving, and use Coq's program extraction.


## Case Studies

### Certifying Leader Election:
This case study is published at ![NFM17](https://link.springer.com/chapter/10.1007%2F978-3-319-57288-8_27).

#### Files:

composition_witness_prop_leader_election.v:
the formalisation and machine checked proofs for the witness property and the
composition property

checker_leader_election.v:
verified local checkers with possibility of program extraction


### Certifying Distributed Bipartite Testing:
The certifying variant of distributed bipartite testing will be 
published at RV17 but not the coq formalisation.
The coq formalisation is work in progress.


### Certifying Shortest Path Construction:
The certifying variant of distributed shortest path construction is
published at ![SEFM15](https://link.springer.com/chapter/10.1007%2F978-3-319-22969-0_14) but not the coq formalisation.


## How do I get set up?

Install ![Coqide](https://coq.inria.fr/download) in version 8.5pl2 or 
later. Start it with the parameter `coqide -impredicative-set`. Further 
compile and install ![GraphBasics](https://github.com/coq-contribs/graph-basics). If you need further help, don't hesitate to contact us!


