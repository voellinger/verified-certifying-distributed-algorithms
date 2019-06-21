import build_graphs
import random

k = 1
while k:
    k -= 1
    min_count = 3
    max_count = 3
    sparsity = 0
    #min_count = 10
    #max_count = 20
    #sparsity = random.randint(min_count, 2 * max_count)
    node_count = random.randint(min_count, max_count)
    g = build_graphs.Graph(node_count, sparsity)
    g.build_random_connected_graph()
    g.is_bipartite()
    g.dottify("The graph and its spanning tree")
    g.build_haskell_code()
