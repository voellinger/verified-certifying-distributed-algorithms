import build_graphs
import random

min_count = 1
max_count = 4 * min_count
node_count = random.randint(min_count, max_count)
sparsity = random.randint(3*min_count, 3*max_count)
g = build_graphs.Graph(node_count, sparsity)
g.build_random_connected_graph()
#g.dottify("The original graph")
g.check_bipartition()
#print(g)
g.dottify("The graph and its spanning tree")
print()
print(g.build_haskell_code())
