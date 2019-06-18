import build_graphs
import random

mini = random.randint(10, 20)
maxi = random.randint(mini, 2*mini)
sparsity = random.randint(3*mini, 3*maxi)
g = build_graphs.Graph(mini, maxi, sparsity)
g.build_random_connected_graph()
#g.dottify("The original graph")
g.check_bipartition()
#print(g)
g.dottify("The graph and its spanning tree")
