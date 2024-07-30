import subprocess
import os
import re
from typing import Any, Callable, List
import networkx
from networkx import MultiDiGraph as Graph

# Tool paths
JAVA = "C:/tools/amazon-corretto-11.0.15.9.1-windows-x64-jdk/jdk11.0.15_9/bin/java.exe"
TLA2TOOLS = "C:/tools/TLAToolbox-1.7.1-win32.win32.x86_64/toolbox/tla2tools.jar"


def file_ts(file):
    try:
        return os.path.getmtime(file)
    except FileNotFoundError:
        return 0

def is_fresh(dst: str, src: List[str]) -> bool:
    dst_ts = file_ts(dst)
    return all(file_ts(s) < dst_ts for s in src)

def tlc(input_path, config_path, output_path):
    if is_fresh(output_path, [input_path, config_path]):
        return

    args = [JAVA, "-jar", TLA2TOOLS, "-config", config_path, "-dump", "dot,actionlabels", output_path.removesuffix(".dot"), input_path]
    subprocess.run(args)

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

class GraphProjection:
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
        dot = Graph()

        for id in self.graph.nodes():
            s = self.graph.nodes[id]["state"]
            dot.add_node(id, label=f"{s}")

        for (s,d,a) in self.graph.edges(keys=True):
            dot.add_edge(s,d, label=f"{a}")

        networkx.nx_pydot.write_dot(dot, file)

def project(graph: Graph, projection: Callable[[Any], Any]) -> GraphProjection:
    p = GraphProjection()
    for id in graph.nodes():
        s = projection(graph.nodes[id]["state"])
        pid = p.mapping.get(s, None)
        if pid is None:
            pid = p.id()
            p.mapping[s] = pid
            p.graph.add_node(pid, state = s)
        p.id_to_pid[id] = pid

    for e in graph.edges(keys=True):
        src = p.id_to_pid[e[0]]
        dst = p.id_to_pid[e[1]]
        key = e[2]
        p.graph.add_edge(src, dst, key)

    return p

output_path = "tictactoe.dot"
tlc("tictactoe.tla", "minimal.cfg", output_path)

with open(output_path) as f:
    graph = parse_tla_dot(f.read())


def project_tokens(state):
    tokens = len([x for x in state["board"].values() if x != " "])

    if state["result"] != "?":
        return state["result"]

    return tokens

graph_projection = project(graph, project_tokens)

graph_projection.to_dot("projection.dot")

subprocess.run(["wsl.exe", "-e", "dot", "-Tsvg", "-o", "projection.svg", "projection.dot"])
