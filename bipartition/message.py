class Message:
    def __init__(self, from_id, m_type, value):
        self.from_id = from_id
        self.m_type = m_type
        self.value = value

    def __str__(self) -> str:
        return "from: " + str(self.from_id.g_id()) + " type: " + str(self.m_type) + ": " + str(self.value)