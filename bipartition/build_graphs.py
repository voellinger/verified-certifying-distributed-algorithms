import random
import graphviz
import threading
import subprocess
from subprocess import PIPE
from queue import Queue


class Graph:
    def __init__(self, node_count : int, sparsity : int) -> None:
        self.node_count = node_count
        self.sparsity = sparsity
        self.components = []
        self.dot = None

    def is_bipartite(self) -> bool:
        for c in self.components:
            c.st_thread.start()
        for c in self.components:
            c.st_thread.join(1)
        for c in self.components:
            if c.is_leader():
                return c.global_bipartite

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

    def dottify(self, title="") -> None:
        """Render the graph."""
        self.dot = graphviz.Graph(name=title, engine="neato")
        for c in self.components:
            pen_width = "1"
            color = "black"
            if c.is_leader():
                color = "#CC4444"
                pen_width = "4"
            if not c.certificate or c.certificate.distance % 2 == 0:
                fill_color = "white"
            else:
                fill_color = "gray"
            if not c.local_bipartite:
                if fill_color != "white":
                    fill_color = "#AAAACC"
                else:
                    fill_color = "#DDDDFF"
            self.dot.node("C"+str(c.id), str(c.id), color=color, fillcolor=fill_color, shape="circle", style="filled", penwidth=pen_width)
            for n in c.neighbours:
                if (n.parent.id == c.id or c.parent.id == n.id) and n.id > c.id:
                    self.dot.edge("C" + str(c.id), "C" + str(n.id), color="#CC4444", penwidth="2", constraint="false")
                elif n.id > c.id:
                    self.dot.edge("C"+str(c.id), "C"+str(n.id), constraint="false")
        self.dot.render(title+".gv", view=True)

    def random_rename(self) -> None:
        """The components rename themselves randomly for a true random graph.
        Temporary negative ids are given to each component, afterwards the names are flipped again."""
        for c in self.components:
            c.id = self.generate_new_neg_id()
        for c in self.components:
            c.id = -c.id
            c.init_thread()

    def generate_new_neg_id(self) -> int:
        """A temporary new random negative id is found."""
        while True:
            r = -random.randint(1, self.node_count)
            if not r in [c.id for c in self.components]:
                return r


class Component:
    def __init__(self, given_id, neighbours=[]):
        self.id = given_id
        self.neighbours = neighbours
        self.certificate = None
        self.st_thread = None
        self.q = Queue(maxsize=0)
        self.global_bipartite = None

    def is_leader(self) -> bool:
        return self.certificate.leader.id == self.id

    def init_thread(self):
        self.st_thread = ST_thread("Thread " + str(self.id), self)


class ST_thread(threading.Thread):
    def __init__(self, name=None, component=None):
        super(ST_thread, self).__init__()
        self.name = name
        self.component = component
        self.leader = self.component
        self.parent = self.component
        self.distance = -1
        self.children = []
        self.unexplored = self.component.neighbours[:]
        self.stop_request = threading.Event()
        self.nld = []
        self.local_bipartite = None
        self.converge_messages = 0
        self.switcher = {
            "leader": self.leader_f,
            "already": self.already_f,
            "parent": self.parent_f,
            "stop": self.stop,
            "certadd": self.certadd,
            "aggregate": self.aggregate
        }

    def run(self):
        # print(str(self.component.id) + " starting ...")
        self.phase1()
        self.phase2()
        self.run_checks()
        # print(str(self.component.id) + " shutting down ...")

    def phase1(self):
        """A spanning tree is built. The node with the highest id becomes root.
           Afterwards all certificates get filled with information of neighboring nodes.
           Each node can now compute its local bipartiteness."""
        self.explore()
        while not self.stop_request.isSet() or not self.nld_is_full():
            self.get_message_execute_message()
        self.local_bipartite = self.component.local_bipartite = self.check_local_bipartition(self.nld)
        self.component.certificate = Certificate(self.component.id, self.component.neighbours, self.leader, self.distance, self.parent, self.nld, self.local_bipartite)

    def map_and(self, ll):
        for l in ll:
            if not l:
                return False
        return True

    def phase2(self):
        """A convergecast, starting from leafs going to the root. The attribute local_bipartite is sent to root."""
        while self.converge_messages < len(self.children):
            self.get_message_execute_message()
        if self.parent.id != self.component.id:
            self.parent.q.put(Message(self.component, "aggregate", self.local_bipartite))
        else:
            self.component.global_bipartite = self.local_bipartite

    def aggregate(self, local_bipartite, from_):
        self.local_bipartite = self.local_bipartite and local_bipartite
        self.converge_messages += 1

    def get_message_execute_message(self):
        try:
            message = self.component.q.get(True)
        except Queue.Empty:
            pass
        else:
            self.component.q.task_done()
            self.switcher.get(message.m_type)(message.value, message.from_id)

    def nld_is_full(self):
        return len(self.component.neighbours) <= len(self.nld)

    def check_local_bipartition(self, nld):
        for n in nld:
            if self.distance % 2 == n[2] % 2:
                return False
        return True

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
                self.stop(0, None)

    def stop(self, val, from_):
        self.distance = val
        for c in self.children:
            c.q.put(Message(self.component, "stop", val+1))
        for c in self.component.neighbours:
            c.q.put(Message(self.component, "certadd", (self.leader, self.distance)))
        self.stop_request.set()

        #  Output for GraphViz
        self.component.parent = self.parent
        self.component.leader = self.leader
        self.component.children = self.children
        self.component.distance = self.distance
        # /Output for Graphviz

    def certadd(self, val, from_) -> None:
        self.nld.append((from_, val[0], val[1]))

    def run_checks(self) -> None:
        # (id:ni:l:p:d:nld:lb:goc)
        id = str(self.component.certificate.id)
        ni = str([n.id for n in self.component.certificate.neighbors])
        l = str(self.component.certificate.leader.id)
        p = str(self.component.certificate.parent.id)
        d = str(self.component.certificate.distance)
        nld = str([(n[0].id, n[1].id, n[2]) for n in self.component.certificate.nld])
        lb = str(self.component.certificate.local_bipartite).capitalize()
        goc = str(self.component.certificate.global_output_consistent).capitalize()
        cert_correct = b'true' == subprocess.run(["./Local_checker_io", id, ni, l, p, d, nld, lb, goc], stdout=PIPE, stderr=PIPE).__dict__["stdout"]
        print("Certificate of node " + str(self.component.certificate.id) + " correct? " + str(cert_correct))


class Message:
    def __init__(self, from_id, m_type, value):
        self.from_id = from_id
        self.m_type = m_type
        self.value = value


class Certificate:
    def __init__(self, id, neighbors, leader, distance, parent, nld, local_bipartite):
        self.id = id
        self.neighbors = neighbors
        self.leader = leader
        self.distance = distance
        self.parent = parent
        self.nld = nld
        self.local_bipartite = local_bipartite

        self.global_output_consistent = True
        # Simulation of a successful consistency check, which is not yet verified in COQ.
