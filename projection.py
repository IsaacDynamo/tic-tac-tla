import re
import networkx
from networkx import MultiDiGraph as Graph
from enum import Enum
import json

def parse_value(value: str):
    value = value.strip()

    if value.startswith("\"") and value.endswith("\""):
        return value[1:-1]

    if value.startswith("<<") and value.endswith(">>"):
        return tuple(parse_value(x) for x in value[2:-2].split(","))

    if value.startswith("(") and value.endswith(")"):
        mapping = {}
        items = value[1:-1].split("@@")
        for item in items:
            k, _, v = item.partition(":>")
            k, v = parse_value(k), parse_value(v)
            mapping[k] = v
        return mapping

    try:
        return int(value)
    except ValueError:
        pass

    return value

def parse_state(values: str) -> dict:
    state = {}
    for name_value in values.split("/\\"):
        if name_value == "":
            continue
        name, _, value = name_value.partition(" = ")
        name = name.strip()
        state[name] = parse_value(value)
    return state

REGEX_EDGE = re.compile(r"(-?\d*) -> (-?\d*) \[label=\"(.*)\",color=\"black\",fontcolor=\"black\"\];")
REGEX_STATE = re.compile(r"(-?\d*) \[label=\"(.*)\"(?:,style = filled)?\];?")

def parse_tla_dot(input: str) -> Graph:
    graph = Graph()
    for line in input.splitlines():
        e = REGEX_EDGE.match(line)
        if e:
            src = int(e.group(1))
            dst = int(e.group(2))
            label = e.group(3).encode('utf-8').decode('unicode_escape')
            graph.add_edge(src, dst, label)

        s = REGEX_STATE.match(line)
        if s:
            id = int(s.group(1))
            label = s.group(2).encode('utf-8').decode('unicode_escape').replace("\n", " ")
            state = parse_state(label)
            graph.add_node(id, state=state)
    return graph

class Projection:
    def __init__(self):
        self._id = 0
        self.graph = Graph()
        self.mapping = {}
        self.id_to_pid = {}

    def id(self):
        i = self._id
        self._id += 1
        return i

    def to_dot(self, file: str):
        g = Graph()

        for id in self.graph.nodes():
            s = self.graph.nodes[id]["state"]
            g.add_node(id, label=f"{s}")

        for (s,d,a) in self.graph.edges(keys=True):
            g.add_edge(s,d, label=f"{a}")

        networkx.nx_pydot.write_dot(g, file)

    def to_svg(self, dot, file: str):
        dot_file = file.removesuffix(".svg") + ".dot"
        self.to_dot(dot_file)
        dot.run("-Tsvg", "-o", file, dot_file)

class ActionType(Enum):
    Loop = 1
    Internal = 2
    External = 3

class Lens:
    filter_actions = True
    def map_state(self, state):
        # Convert dict into something hashable
        return json.dumps(state, sort_keys=True, indent=1).replace(":", "=").removesuffix("\n}").removeprefix("{\n")

    def map_action(self, action, type: ActionType):
        return action

def project(graph: Graph, lens: Lens) -> Projection:
    p = Projection()
    for id in graph.nodes():
        s = lens.map_state(graph.nodes[id]["state"])
        if s is not None:
            pid = p.mapping.get(s, None)
            if pid is None:
                pid = p.id()
                p.mapping[s] = pid
                p.graph.add_node(pid, state = s)
            p.id_to_pid[id] = pid

    for (src, dst, action) in graph.edges(keys=True):
        psrc = p.id_to_pid.get(src, None)
        pdst = p.id_to_pid.get(dst, None)
        if psrc is not None and pdst is not None:
            if src == dst:
                t = ActionType.Loop
            elif psrc == pdst:
                t = ActionType.Internal
            else:
                t = ActionType.External

            if lens.filter_actions and t != ActionType.External:
                paction = None
            else:
                paction = lens.map_action(action, t)

            if paction is not None:
                p.graph.add_edge(psrc, pdst, paction)

    return p
