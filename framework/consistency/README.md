#Proof Obligations Consistency

##Files:

**nw_model_version_consistency.v**
The file contains the network model as a foundation of the consistency part.
Note that there is an improved and more general version of the network model:
https://github.com/voellinger/verified-certifying-distributed-algorithms/tree/master/framework/networkmodel

**PO_III.v**
The file contains the formalization of the notion of consistency and 
the proof of the theorem 'distributed checkability of consistency' 
indicating that for a connected witness it is enough to check the 
consistency in the neighborhoods.

A generic interface of a CDA (PO I(i)) is also included in the file.
Note that there is an improved and more general version of a CDA interface:
https://github.com/voellinger/verified-certifying-distributed-algorithms/tree/master/framework/networkmodel


**PO IV_iii.v**
The file contains a verified implementation of 
the distributed consistency check in
each neihghborhood of a component.
