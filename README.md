# Verified certifying distributed algorithms

This repository is a collection of verified certifying distributed algorithms. A certifying algorithm computes in addition to each result a witness for the result's correctness. C. Rizkallah showed how certifying sequential algorithms can be verified so that they ensure formal instance correctness. She proved the correctness of checkers via program verification and the correctness of witness properties via theorem proving (Isabelle). We adapt her method to certifying distributed algorithms and use Coq.

## How to use

Install ![Coqide](https://coq.inria.fr/download) in version 8.5pl2 or later. Start it with the parameter `coqide -impredicative-set`. Further compile and install ![GraphBasics](https://github.com/coq-contribs/graph-basics). If you need further help, don't hesitate to contact us!
