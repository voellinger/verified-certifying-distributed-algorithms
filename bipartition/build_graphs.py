import random
import graphviz
import threading
import subprocess
from subprocess import PIPE
from queue import Queue
from typing import List


class Graph:
    def __init__(self, node_count: int, sparsity: int) -> None:
        self.__node_count = node_count
        self.__sparsity = sparsity
        self.__components = []
        self.__dot = None

    def is_bipartite(self) -> bool:
        for c in self.__components:
            c.start_thread()
        for c in self.__components:
            if c.is_thread_started():
                c.join_thread()
        for c in self.__components:
            if c.is_leader():
                return c.is_global_bipartite()

    def build_random_connected_graph(self) -> None:
        """Builds a connected graph with self.__node_count many nodes. The __sparsity describes inversely how many nodes will be
        approximately connected."""
        for v in range(1, self.__node_count + 1):
            new_vertex = Component(v, [])
            self.__components.append(new_vertex)
            while v > 1 and not new_vertex.has_neighbors():
                for n in range(0, v-1):
                    if random.randint(0, self.__sparsity) == 0:
                        new_vertex.add_neighbor(self.__components[n])
                        self.__components[n].add_neighbor(new_vertex)
        self.random_rename()

    def __str__(self) -> str:
        ret = ""
        for c in self.__components:
            ret += c.__str__()
        return ret

    def dottify(self, title="") -> None:
        """Render the graph."""
        self.__dot = graphviz.Graph(name=title, engine="neato")
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
                    fill_color = "#AAAACC"
                else:
                    fill_color = "#DDDDFF"
            self.__dot.node("C" + str(c.g_id()), str(c.g_id()), color=color, fillcolor=fill_color, shape="circle", style="filled", penwidth=pen_width)
            for n in c.g_neighbors():
                if (n.is_parent_or_child(c)) and n.g_id() > c.g_id():
                    self.__dot.edge("C" + str(c.g_id()), "C" + str(n.g_id()), color="#CC4444", penwidth="2", constraint="false")
                elif n.g_id() > c.g_id():
                    self.__dot.edge("C" + str(c.g_id()), "C" + str(n.g_id()), constraint="false")
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


class Component:
    def __init__(self, given_id, neighbours=None):
        self.__id = given_id
        if neighbours is None:
            self.__neighbours = []
        else:
            self.__neighbours = neighbours
        self.__certificate = None
        self.__st_thread = None
        self.__q = Queue(maxsize=0)
        self.__global_bipartite = None

    def __str__(self) -> str:
        ret = str(self.__id) + " ["
        for n in self.__neighbours:
            ret += str(n.g_id()) + ", "
        ret += "]\n"
        return ret

    def q_put(self, message) -> None:
        self.__q.put(message)

    def q_get(self, b):
        return self.__q.get(b)

    def q_task_done(self) -> None:
        self.__q.task_done()

    def q_is_empty(self) -> bool:
        return self.__q.empty()

    def s_certificate(self, certificate) -> None:
        self.__certificate = certificate

    def g_certificate(self) -> object:
        return self.__certificate

    def s_id(self, new_id) -> None:
        self.__id = new_id

    def g_id(self) -> int:
        return self.__id

    def s_global_bipartite(self, g_bipartite) -> None:
        self.__global_bipartite = g_bipartite

    def is_global_bipartite(self) -> bool:
        return self.__global_bipartite

    def is_leader(self) -> bool:
        if self.__certificate is not None:
            return self.__certificate.is_leader()
        return False

    def has_neighbors(self) -> bool:
        return self.__neighbours is not None and self.__neighbours != []

    def add_neighbor(self, new_neighbor) -> None:
        self.__neighbours.append(new_neighbor)

    def g_neighbors(self) -> List[object]:
        return self.__neighbours[:]

    def init_thread(self):
        self.__st_thread = StThread("Thread " + str(self.__id), self)

    def is_local_bipartite(self) -> bool:
        if self.__certificate is not None:
            return self.__certificate.is_local_bipartite()
        return False

    def is_even(self) -> bool:
        if self.__certificate is not None:
            return self.__certificate.is_even()
        return False

    def is_parent_or_child(self, p_or_child) -> bool:
        if self.__certificate is not None:
            return self.__certificate.g_parent().g_id() == p_or_child.g_id() or p_or_child.is_parent(self)
        return False

    def is_parent(self, parent) -> bool:
        if self.__certificate is not None:
            return self.__certificate.g_parent().g_id() == parent.g_id()
        return False

    def join_thread(self) -> None:
        self.__st_thread.join(1)

    def start_thread(self) -> None:
        self.__st_thread.start()

    def is_thread_started(self) -> bool:
        return self.__st_thread.isAlive()



class StThread(threading.Thread):
    def __init__(self, name=None, component=None):
        super(StThread, self).__init__()
        self.name = name
        self.component = component
        self.id = self.component.g_id()
        self.neighbors = self.component.g_neighbors()

        self.leader = self.component
        self.parent = self.component
        self.distance = -1
        self.children = []
        self.unexplored = self.neighbors[:]
        self.stop_request = threading.Event()
        self.nld = []
        self.local_bipartite = None
        self.global_bipartite = True
        self.converge_messages = 0
        self.switcher = {
            "leader": self.leader_f,
            "already": self.already_f,
            "parent": self.parent_f,
            "stop": self.stop,
            "cert_add": self.certadd,
            "aggregate": self.aggregate
        }

    def run(self):
        # print(str(self.id) + " starting ...")
        self.phase1()
        self.phase2()
        self.run_checks()
        # print(str(self.id) + " shutting down ...")

    def phase1(self):
        """A spanning tree is built. The node with the highest __id becomes root.
           Afterwards all certificates get filled with information of neighboring nodes.
           Each node can now compute its local bipartiteness."""
        self.explore()
        while not self.stop_request.isSet() or not self.nld_is_full():
            self.get_message_execute_message()
        self.local_bipartite = self.check_local_bipartition(self.nld)
        self.component.s_certificate(Certificate(self.id, self.neighbors, self.leader, self.distance, self.parent, self.nld, self.local_bipartite))

    def phase2(self):
        """A converge-cast, starting from leafs going to the root. The attribute local_bipartite is sent to root."""
        while self.converge_messages < len(self.children):
            self.get_message_execute_message()
        if self.parent.g_id() != self.id:
            self.parent.q_put(Message(self.component, "aggregate", self.global_bipartite and self.local_bipartite))
        else:
            self.component.s_global_bipartite(self.global_bipartite)

    def aggregate(self, tree_bipartite, *_):
        self.global_bipartite = self.global_bipartite and tree_bipartite
        self.converge_messages += 1

    def get_message_execute_message(self):
        try:
            message = self.component.q_get(True)
        except self.component.queue_is_empty():
            pass
        else:
            self.component.q_task_done()
            self.switcher.get(message.m_type)(message.value, message.from_id)

    def nld_is_full(self):
        return len(self.neighbors) <= len(self.nld)

    def check_local_bipartition(self, nld):
        for n in nld:
            if self.distance % 2 == n[2] % 2:
                return False
        return True

    def leader_f(self, new_leader, from_):
        if self.leader.g_id() < new_leader.g_id():
            self.leader = new_leader
            self.parent = from_
            self.children = []
            self.unexplored = [n for n in self.neighbors if n.g_id() != from_.g_id()]
            self.explore()
        else:
            if self.leader.g_id() == new_leader.g_id():
                from_.q_put(Message(self.component, "already", self.leader))

    def already_f(self, new_leader, *_):
        if new_leader.g_id() == self.leader.g_id():
            self.explore()

    def parent_f(self, new_leader, from_):
        if new_leader.g_id() == self.leader.g_id():
            self.children.append(from_)
            self.explore()

    def explore(self):
        if self.unexplored:
            p_k = self.unexplored.pop()
            p_k.q_put(Message(self.component, "leader", self.leader))
        else:
            if self.parent.g_id() != self.id:
                self.parent.q_put(Message(self.component, "parent", self.leader))
            else:
                self.stop(0, None)

    def stop(self, val, *_):
        self.distance = val
        for c in self.children:
            c.q_put(Message(self.component, "stop", val+1))
        for c in self.neighbors:
            c.q_put(Message(self.component, "cert_add", (self.leader, self.distance)))
        self.stop_request.set()

    def certadd(self, val, from_) -> None:
        self.nld.append((from_, val[0], val[1]))

    def run_checks(self) -> None:
        # (__id:ni:l:p:d:nld:lb:goc)
        n_id = str(self.component.g_certificate().g_id())
        ni = str([n.g_id() for n in self.component.g_certificate().g_neighbors()])
        le = str(self.component.g_certificate().g_leader().g_id())
        p = str(self.component.g_certificate().g_parent().g_id())
        d = str(self.component.g_certificate().g_distance())
        nld = str([(n[0].g_id(), n[1].g_id(), n[2]) for n in self.component.g_certificate().g_nld()])
        lb = str(self.component.g_certificate().g_local_bipartite()).capitalize()
        goc = str(self.component.g_certificate().g_global_output_consistent()).capitalize()
        cert_correct = b'true' == subprocess.run(["./Local_checker_io", n_id, ni, le, p, d, nld, lb, goc], stdout=PIPE, stderr=PIPE).__dict__["stdout"]
        print("Certificate of node " + str(self.component.g_certificate().g_id()) + " correct? " + str(cert_correct))


class Message:
    def __init__(self, from_id, m_type, value):
        self.from_id = from_id
        self.m_type = m_type
        self.value = value


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
        return self.__distance % 2 == 0




#Phase 1: Baum bilden
#Phase 2: von Blättern her Wurzel bescheid geben
#Phase 3: Wurzel-Broadcast entlang der Parent-Relation