import build_graphs
import random

min = random.randint(10, 20)
max = random.randint(min, 2*min)
sparsity = random.randint(3*min, 3*max)
g = build_graphs.Graph(min, max, sparsity)
g.build_random_connected_graph()
#print(g)
g.dottify("The graph")
g.build_spanning_tree()
g.dottify("The graph and its spanning tree", whole_graph=False)