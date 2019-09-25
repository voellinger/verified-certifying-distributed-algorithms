import component

import random
import graphviz


class Graph:
    def __init__(self, node_count: int, sparsity: int) -> None:
        self.__node_count = node_count
        self.__sparsity = sparsity
        self.__components = []
        self.__dot = None

    def __str__(self) -> str:
        ret = ""
        for c in self.__components:
            ret += c.__str__()
        return ret

    def build_random_connected_graph(self) -> None:
        """Builds a connected graph with self.__node_count many nodes. The __sparsity describes inversely how many nodes will be
        approximately connected."""
        for v in range(1, self.__node_count + 1):
            new_vertex = component.Component(v, [])
            self.__components.append(new_vertex)
            while v > 1 and not new_vertex.has_neighbors():
                for n in range(0, v-1):
                    if random.randint(0, self.__sparsity) == 0:
                        new_vertex.add_neighbor(self.__components[n])
                        self.__components[n].add_neighbor(new_vertex)
        self.random_rename()

    def dottify(self, title="") -> None:
        """Render the graph."""
        self.__dot = graphviz.Digraph(name=title, engine="neato")
        for c in self.__components:
            pen_width = "1"
            color = "black"
            if c.is_leader():
                color = "#CC4444"
                pen_width = "4"
            if c.is_even():
                fill_color = "white"
            else:
                fill_color = "gray"
            if not c.is_local_bipartite():
                if fill_color != "white":
                    fill_color = "#AFAFCC"
                else:
                    fill_color = "#DDDDF0"
            self.__dot.node("C" + str(c.g_id()), str(c.g_id()), color=color, fillcolor=fill_color, shape="circle", style="filled", penwidth=pen_width)
            for n in c.g_neighbors():
                if n.is_parent(c):
                    self.__dot.edge("C" + str(n.g_id()), "C" + str(c.g_id()), color="#CC4444", penwidth="1", constraint="false", arrowhead="normal")
                elif (not n.is_parent_or_child(c)) and n.g_id() > c.g_id():
                    self.__dot.edge("C" + str(c.g_id()), "C" + str(n.g_id()), color="#0000FF", constraint="false", arrowhead="none")
        self.__dot.render(title + ".gv", view=True)

    def random_rename(self) -> None:
        """The __components rename themselves randomly for a true random graph.
        Temporary negative ids are given to each component, afterwards the names are flipped again."""
        for c in self.__components:
            c.s_id(self.generate_new_neg_id())
        for c in self.__components:
            c.s_id(-c.g_id())
            c.init_thread()

    def generate_new_neg_id(self) -> int:
        """A temporary new random negative __id is found."""
        while True:
            r = -random.randint(1, self.__node_count)
            if r not in [c.g_id() for c in self.__components]:
                return r

    def is_bipartite(self) -> bool:
        for c in self.__components:
            c.start_thread()
        for c in self.__components:
            if c.is_thread_started():
                c.join_thread()
        for c in self.__components:
            if c.is_leader():
                return c.is_global_bipartite()
