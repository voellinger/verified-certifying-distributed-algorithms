import random
import graphviz
import threading, logging, subprocess
from subprocess import PIPE
from queue import Queue


def int_to_nat(n) -> str:
    ret = "O"
    for k in range(n):
        ret = "S (" + ret + ")"
    return ret

def list_to_List(ls) -> str:
    ret = "Nil"
    for l in ls:
        ret = "Cons (" + l + ") (" + ret + ")"
    return ret

def pair_to_prod(p1, p2) -> str:
    return "Pair (" + p1 + ") (" + p2 + ")"

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
            if c.no_bi_edge:
                return False
        return True

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

    def dottify(self, title="") -> None:
        """Render the graph."""
        self.dot = graphviz.Graph(name=title, engine="neato")
        for c in self.components:
            penwidth = "1"
            color = "black"
            if c.leader.id == c.id:
                color = "#CC4444"
                penwidth = "4"
            if not c.certificate or c.certificate.distance % 2 == 0:
                fill_color = "white"
            else:
                fill_color = "gray"
            if c.no_bi_edge:
                if fill_color != "white":
                    fill_color = "#AAAACC"
                else:
                    fill_color = "#DDDDFF"
            self.dot.node("C"+str(c.id), str(c.id), color=color, fillcolor=fill_color, shape="circle", style="filled", penwidth=penwidth)
            for n in c.neighbours:
                if (n.parent.id == c.id or c.parent.id == n.id) and n.id > c.id:
                    self.dot.edge("C" + str(c.id), "C" + str(n.id), color="#CC4444", penwidth="2", constraint="false")
                elif n.id > c.id:
                    self.dot.edge("C"+str(c.id), "C"+str(n.id), constraint="false")
        self.dot.render(title+".gv", view=True)

    def build_haskell_code(self) -> None:
        start_string = "--This file was created automatically\nmodule Main where\n\n"
        end_string = open("temp.tmp", "r").read()
        self.run_check(start_string, "Checker_local_bipartition", end_string)
        self.run_check(start_string, "Checker_local_output_consistent", end_string)
        self.run_check(start_string, "Checker_tree", end_string)

    def run_check(self, start_string, file_name, end_string) -> list:
        end_string = end_string.replace("##", file_name)
        end_string = end_string.replace("**", file_name.lower())
        end_string = end_string.replace("@@", "("+int_to_nat(self.node_count)+")")
        if file_name != "Checker_local_bipartition":
            end_string = end_string.replace(" nnnn_iiii", " neighbours_input")
        else:
            end_string = end_string.replace(" nnnn_iiii", "")
        ret = start_string
        ret += "import " + file_name + "\n\n"
        ret += self.str_leader()
        ret += self.str_distance()
        ret += self.str_parent()
        ret += self.str_neighbours()
        ret += self.str_nld()
        file_name_var = file_name + "_vars"
        file_name_complete = file_name_var + ".hs"
        text_file = open(file_name_complete, "w")
        text_file.write(ret + end_string)
        text_file.close()
        subprocess.run(["ghc", file_name_complete], stdout=PIPE, stderr=PIPE)
        print([b==b'true' for b in subprocess.run(["./" + file_name_var], stdout=PIPE, stderr=PIPE).__dict__["stdout"].split()])
        return

    def str_leader(self) -> str:
        ret = "leader :: (Component -> Component)\n"
        for c in self.components:
            ret += "leader (" + int_to_nat(c.id) + ") = " + int_to_nat(c.certificate.leader.id) + "\n"
        return ret + "\n\n"

    def str_distance(self) -> str:
        ret = "distance :: (Component -> Nat)\n"
        for c in self.components:
            ret += "distance (" + int_to_nat(c.id) + ") = " + int_to_nat(c.certificate.distance) + "\n"
        return ret + "\n\n"

    def str_parent(self) -> str:
        ret = "parent :: (Component -> Component)\n"
        for c in self.components:
            ret += "parent (" + int_to_nat(c.id) + ") = " + int_to_nat(c.certificate.parent.id) + "\n"
        return ret + "\n\n"

    def str_neighbours(self) -> str:
        ret = "neighbours_input :: (Component -> List Component)\n"
        for c in self.components:
            ret += "neighbours_input (" + int_to_nat(c.id) + ") = " + list_to_List([int_to_nat(n.id) for n in c.neighbours]) + "\n"
        return ret + "\n\n"

    def str_nld(self) -> str:
        ret = "neighbors_leader_distance :: (Component -> List (Prod (Prod Component Component) Nat))\n"
        for c in self.components:
            ret += "neighbors_leader_distance (" + int_to_nat(c.id) + ") = "
            ret += list_to_List([pair_to_prod("("+pair_to_prod(int_to_nat(nld[0].id), int_to_nat(nld[1].id))+")", int_to_nat(nld[2])) for nld in c.certificate.nld]) + "\n"
        return ret + "\n\n"

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

class Component:
    def __init__(self, given_id, neighbours=[]) -> None:
        self.id = given_id
        self.neighbours = neighbours
        self.certificate = None
        self.st_thread = None
        self.q = Queue(maxsize=0)
        self.no_bi_edge = None

    def is_in_neighbours(self, c) -> bool:
        if type(c) == int:
            return c in self.neighbour_ids
        return c in self.neighbours




class ST_thread(threading.Thread):
    def __init__(self, name = None, component = None):
        super(ST_thread,self).__init__()
        self.name = name
        self.component = component
        self.leader = self.component
        self.parent = self.component
        self.distance = -1
        self.children = []
        self.unexplored = self.component.neighbours[:]
        self.stop_request = threading.Event()
        self.nld = []
        self.switcher = {
            "leader":self.leader_f,
            "already":self.already_f,
            "parent":self.parent_f,
            "stop":self.stop,
            "certadd":self.certadd
        }

    def run(self):
        #print(str(self.component.id) + " starting ...")
        self.explore()

        while not self.stop_request.isSet():
            try:
                message = self.component.q.get(True)
            except Queue.Empty:
                pass
            else:
                self.component.q.task_done()
                self.switcher.get(message.m_type)(message.value, message.from_id)
        while len(self.component.neighbours) > len(self.nld):
            try:
                message = self.component.q.get(True)
            except Queue.Empty:
                pass
            else:
                self.component.q.task_done()
                self.switcher.get(message.m_type)(message.value, message.from_id)
        self.component.certificate = Certificate(self.leader, self.distance, self.parent, self.nld)
        self.component.no_bi_edge = self.check_local_bipartition(self.component.certificate)
        #print(str(self.component.id) + " shutting down ...")

    def check_local_bipartition(self, cert):
        for n in cert.nld:
            if cert.distance % 2 == n[2] % 2:
                return True
        return False

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
        self.component.parent = self.parent
        self.component.leader = self.leader
        self.component.children = self.children
        self.component.distance = self.distance

    def certadd(self, val, from_) -> None:
        self.nld.append((from_, val[0], val[1]))


class Message:
    def __init__(self, from_id, m_type, value):
        self.from_id = from_id
        self.m_type = m_type
        self.value = value

    def __str__(self):
        return str(self.from_id) + " " + self.m_type + " " + str(self.value)

class Certificate:
    def __init__(self, leader, distance, parent, nld):
        self.leader = leader
        self.distance = distance
        self.parent = parent
        self.nld = nld

    def __str__(self):
        return "Cert(" + str(self.leader) + " " + str(self.distance) + " " + str(self.parent) + " " + str([n.id for n in self.n_leaders]) + " " + str(self.n_distances) + ")"