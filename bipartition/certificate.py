class Certificate:
    def __init__(self, node_id, neighbors, leader, distance, parent, nld, local_bipartite):
        self.__id = node_id
        self.__neighbors = neighbors
        self.__leader = leader
        self.__distance = distance
        self.__parent = parent
        self.__nld = nld
        self.__local_bipartite = local_bipartite

        self.__global_output_consistent = True
        # Simulation of a successful consistency check, which is not yet verified in COQ.

    def g_id(self):
        return self.__id

    def g_neighbors(self):
        return self.__neighbors

    def g_leader(self):
        return self.__leader

    def g_parent(self):
        return self.__parent

    def g_distance(self):
        return self.__distance

    def g_nld(self):
        return self.__nld

    def g_local_bipartite(self):
        return self.__local_bipartite

    def g_global_output_consistent(self):
        return self.__global_output_consistent

    def is_leader(self) -> bool:
        return self.__id == self.__leader.g_id()

    def is_local_bipartite(self) -> bool:
        return self.__local_bipartite

    def is_even(self) -> bool:
        if self.__distance != None:
            return self.__distance % 2 == 0
        else:
            return False