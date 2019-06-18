import random
import graphviz
import threading, logging
from queue import Queue

class Graph:
    def __init__(self, min_size : int, max_size : int, sparsity : int) -> None:
        self.node_count = random.randint(min_size, max_size)
        self.sparsity = sparsity
        self.components = []
        self.dot = graphviz.Graph(name="", engine="neato")

    def build_spanning_tree(self):
        for c in self.components:
            c.st_thread.start()
        for c in self.components:
            c.st_thread.join(1)

    def build_random_connected_graph(self) -> None:
        """Builds a connected graph with self.node_count many nodes. The sparsity describes inversely how many nodes will be
        approximately connected."""
        for v in range(1, self.node_count+1):
            new_vertex = Component(v, [])
            self.components.append(new_vertex)
            while v > 1 and not new_vertex.neighbours:
                for n in range(0, v-1):
                    if random.randint(0, self.sparsity) == 0:
                        new_vertex.neighbours.append(self.components[n])
                        self.components[n].neighbours.append(new_vertex)
        self.random_rename()
        for c in self.components:
            c.st_thread = ST_thread("Thread " + str(c.id), c)

    def dottify(self, title="", whole_graph=True) -> None:
        """Render the graph."""
        self.dot.name = title
        for c in self.components:
            if c.root:
                c.color = "red"
            if c.fill_color == 0:
                c.fill_color = "gray"
            else:
                c.fill_color = "white"
            self.dot.node("C"+str(c.id), str(c.id), color=c.color, fillcolor=c.fill_color, style="filled")
            for n in [n.id for n in c.neighbours]:
                if whole_graph:
                    if n > c.id:
                        self.dot.edge("C"+str(c.id), "C"+str(n), constraint="false")
                else:
                    if n == c.parent.id:
                        self.dot.edge("C" + str(c.id), "C" + str(n), color="red", constraint="false")
        self.dot.render(title, view=True)

    def __str__(self) -> str:
        ret = ""
        for c in self.components:
            ret += c.__str__() + "\n"
        return ret

    def random_rename(self) -> None:
        """The components rename themselves randomly for a true random graph.
        Temporary negative ids are given to each component, afterwards the names are flipped again."""
        for c in self.components:
            c.id = self.generate_new_neg_id()
        for c in self.components:
            c.id = -c.id

    def generate_new_neg_id(self) -> int:
        """A temporary new random negative id is found."""
        while True:
            r = -random.randint(1, self.node_count)
            if not r in [c.id for c in self.components]:
                return r

class Component():
    def __init__(self, given_id, neighbours=[]) -> None:
        self.id = given_id
        self.neighbours = neighbours
        self.fill_color = "white"
        self.color = "black"
        self.st_thread = None
        self.leader = None
        self.parent = None
        self.children = []
        self.root = False
        self.q = Queue(maxsize=0)

    def __str__(self) -> str:
        return str(self.id) + " " + str([n.id for n in self.neighbours])

    def is_in_neighbours(self, c) -> bool:
        if type(c) == int:
            return c in self.neighbour_ids
        return c in self.neighbours





class ST_thread(threading.Thread):
    def __init__(self, name = None, component = None):
        super(ST_thread,self).__init__()
        self.name = name
        self.component = component
        self.root = False
        self.leader = self.component
        self.parent = self.component
        self.children = []
        self.unexplored = self.component.neighbours[:]
        self.stop_request = threading.Event()
        self.switcher = {
            "leader":self.leader_f,
            "already":self.already_f,
            "parent":self.parent_f,
            "stop":self.stop
        }

    def run(self):
        self.explore()

        while not self.stop_request.isSet():
            try:
                message = self.component.q.get(True)
            except Queue.Empty:
                pass
            else:
                self.component.q.task_done()
                self.switcher.get(message.m_type)(message.value, message.from_id)

    def leader_f(self, new_leader, from_):
        if self.leader.id < new_leader.id:
            self.leader = new_leader
            self.parent = from_
            self.children = []
            self.unexplored = [n for n in self.component.neighbours if n.id != from_.id]
            self.explore()
        else:
            if self.leader.id == new_leader.id:
                from_.q.put(Message(self.component, "already", self.leader))

    def already_f(self, new_leader, from_):
        if new_leader.id == self.leader.id:
            self.explore()

    def parent_f(self, new_leader, from_):
        if new_leader.id == self.leader.id:
            self.children.append(from_)
            self.explore()

    def explore(self):
        if self.unexplored:
            p_k = self.unexplored.pop()
            p_k.q.put(Message(self.component, "leader", self.leader))
        else:
            if self.parent.id != self.component.id:
                self.parent.q.put(Message(self.component, "parent", self.leader))
            else:
                self.root = True
                self.stop(1, 0)

    def stop(self, val, from_):
        for c in self.children:
            c.q.put(Message(self.component, "stop", 1-val))
        self.stop_request.set()
        self.component.fill_color = 1 - val
        self.component.parent = self.parent
        self.component.leader = self.leader
        self.component.children = self.children
        self.component.root = self.root


class Message:
    def __init__(self, from_id, m_type, value):
        self.from_id = from_id
        self.m_type = m_type
        self.value = value

    def __str__(self):
        return str(self.from_id) + " " + self.m_type + " " + str(self.value)