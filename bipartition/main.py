import build_graphs
import random

k = 1
while k:
    k -= 1
    # min_count = 5
    # max_count = 5
    # sparsity = 4
    min_count = 10
    max_count = 20
    sparsity = random.randint(min_count, 2 * max_count)
    node_count = random.randint(min_count, max_count)
    g = build_graphs.Graph(node_count, sparsity)

    g.build_random_connected_graph()
    if g.is_bipartite():
        print("Graph IS bipartite.")
    else:
        print("Graph is NOT bipartite.")
    g.dottify("The graph and its spanning tree")
