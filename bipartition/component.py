import bipartition_thread1
from queue import Queue
from typing import List


class Component:
    def __init__(self, given_id, neighbours=None):
        self.__id = given_id
        if neighbours is None:
            self.__neighbours = []
        else:
            self.__neighbours = neighbours
        self.__certificate = None
        self.__bipartition_thread = None
        self.__q = Queue(maxsize=0)
        self.__global_bipartite = None

    def __str__(self) -> str:
        ret = str(self.__id) + " ["
        for n in self.__neighbours:
            ret += str(n.g_id()) + ", "
        ret += "]\n"
        return ret

    def q_put(self, message) -> None:
        # print(message)
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
        self.__bipartition_thread = bipartition_thread1.bipartitionThread("Bipartition Thread " + str(self.__id), self)

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
        self.__bipartition_thread.join(1)

    def start_thread(self) -> None:
        self.__bipartition_thread.start()

    def is_thread_started(self) -> bool:
        return self.__bipartition_thread.isAlive()
