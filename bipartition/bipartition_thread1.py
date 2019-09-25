import certificate, message

import threading
import subprocess
from subprocess import PIPE


class bipartitionThread(threading.Thread):
    def __init__(self, name=None, component=None):
        super(bipartitionThread, self).__init__()
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
        self.build_spanning_tree_check_bipartition()
        self.check_local_bipartitenesses()
        self.run_checks()
        # print(str(self.id) + " shutting down ...")

    def build_spanning_tree_check_bipartition(self):
        """A spanning tree is built. The node with the highest __id becomes root.
           Afterwards all certificates get filled with information of neighboring nodes.
           Each node can now compute its local bipartiteness."""
        self.explore()
        while not self.stop_request.isSet() or not self.nld_is_full():
            self.get_message_execute_message()
        self.local_bipartite = self.check_local_bipartition(self.nld)
        self.component.s_certificate(certificate.Certificate(self.id, self.neighbors, self.leader, self.distance, self.parent, self.nld, self.local_bipartite))

    def check_local_bipartitenesses(self):
        """A converge-cast, starting from leafs going to the root. The attribute local_bipartite is sent to root."""
        while self.converge_messages < len(self.children):
            self.get_message_execute_message()
        if self.parent.g_id() != self.id:
            self.parent.q_put(message.Message(self.component, "aggregate", self.global_bipartite and self.local_bipartite))
        else:
            self.component.s_global_bipartite(self.global_bipartite)

    def aggregate(self, tree_bipartite, *_):
        self.global_bipartite = self.global_bipartite and tree_bipartite
        self.converge_messages += 1

    def get_message_execute_message(self):
        try:
            msg = self.component.q_get(True)
        except self.component.queue_is_empty():
            pass
        else:
            self.component.q_task_done()
            self.switcher.get(msg.m_type)(msg.value, msg.from_id)

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
                from_.q_put(message.Message(self.component, "already", self.leader))

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
            p_k.q_put(message.Message(self.component, "leader", self.leader))
        else:
            if self.parent.g_id() != self.id:
                self.parent.q_put(message.Message(self.component, "parent", self.leader))
            else:
                self.stop(0, None)

    def stop(self, val, *_):
        self.distance = val
        for c in self.children:
            c.q_put(message.Message(self.component, "stop", val+1))
        for c in self.neighbors:
            c.q_put(message.Message(self.component, "cert_add", (self.leader, self.distance)))
        self.stop_request.set()

    def certadd(self, val, from_) -> None:
        self.nld.append((from_, val[0], val[1]))

    def run_checks(self) -> None:
        if 1==1:
            return
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
        # print("Certificate of node " + str(self.component.g_certificate().g_id()) + " correct? " + str(cert_correct))
