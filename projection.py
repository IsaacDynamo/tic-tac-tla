import re
from typing import Any, Hashable
import networkx
from networkx import MultiDiGraph as Graph
from enum import Enum
import json
import pydot
import tempfile
from IPython.display import SVG
import os
import subprocess
import parse

REGEX_EDGE = re.compile(r"(-?\d*) -> (-?\d*) \[label=\"(.*)\",color=\"black\",fontcolor=\"black\"\];")
REGEX_STATE = re.compile(r"(-?\d*) \[label=\"(.*)\"(,style = filled)?\];?")

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
            label = s.group(2).encode('utf-8').decode('unicode_escape')
            initial = s.group(3) is not None
            state = parse.parse(label)
            graph.add_node(id, state=state, initial=initial)
    return graph

class Projection:
    def __init__(self, graph, lens: 'Lens'):
        self.parent = graph
        self.lens = lens
        self._id = 0
        self.graph = Graph()
        self.mapping = {}
        self.id_to_pid = {}
        self.id_to_eqv_class_id = {}

    def id(self):
        i = self._id
        self._id += 1
        return i

    def to_dot(self, file: str):
        g = Graph()
        id_to_n = {}

        for id in self.graph.nodes():
            node = self.graph.nodes[id]

            id_n = len(id_to_n) + 1
            id_to_n[id] = id_n

            extra = {}
            style = []
            if self.lens.show_initial and node["contains_initial"]:
                style.append("filled")

            if self.lens.show_single_state and node["single_state"]:
                style.append("bold")

            if style:
                extra.update({ "style": ",".join(style) })

            label = self.lens.state_label(node["eqv_class"])
            if label is not None:
                if self.lens.show_node_count:
                    count = len(node["state_ids"])
                    label = label + f"\n#{count}"

                # Used json to escape the string, this seems to work for .dot files
                label = json.dumps(label)

                g.add_node(id_n, label=label, **extra)

        for (s,d,a) in self.graph.edges(keys=True):
            edge = self.graph.edges[s, d, a]

            if s == d and not self.lens.show_self_actions:
                continue

            extra = {}
            if self.lens.style_edge:
                if not edge["semi_deterministic"]:
                    extra.update({ "color": "gray" })

                if not edge["definite"]:
                    extra.update({ "style": "dashed" })

            label = self.lens.action_label(a)
            if label is not None:
                if self.lens.show_edge_count:
                    count = len(edge["sources"])
                    label = label + f"\n#{count}"

                # Used json to escape the string, this seems to work for .dot files
                label = json.dumps(label)

                g.add_edge(id_to_n[s], id_to_n[d], label=label, **extra)

        d: pydot.Dot = networkx.nx_pydot.to_pydot(g)
        d.set("rankdir", "LR")
        d.write(file)

    def to_svg(self, dot, file: str):
        dot_file = file.removesuffix(".svg") + ".dot"
        self.to_dot(dot_file)
        dot.run("-Tsvg", "-o", file, dot_file)

    def show(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            dot_file = os.path.join(tmpdir, 'graph.dot')
            self.to_dot(dot_file)

            cmd = ["wsl.exe", "-e", "dot", "-Tsvg", "-o", "graph.svg", "graph.dot"]
            subprocess.run(cmd, cwd=tmpdir, check = True)

            svg_file = os.path.join(tmpdir, 'graph.svg')
            return SVG(filename=svg_file)

    def dump(self) -> str:
        with tempfile.TemporaryDirectory() as tmpdir:
            dot_file = os.path.join(tmpdir, 'graph.dot')
            self.to_dot(dot_file)

            with open(dot_file) as f:
                return f.read()


class Lens:
    show_self_actions = False
    show_node_count = False
    show_edge_count = False
    show_initial = True
    show_single_state = True
    style_edge = True

    def projection(self, state) -> Any:
        return state

    def serialize(self, state) -> Hashable:
        return parse.serialize(state)

    def state_label(self, state) -> str:
        if isinstance(state, str):
            return state
        return parse.serialize(state)

    def action_label(self, action) -> str:
        return ""

    def focus(self, graph) -> Projection:
        return project(graph, self)

class IdentityLens(Lens):
    style_edge = False
    show_single_state = False

    def action_label(self, action):
        return action

def project(graph: Graph, lens: Lens) -> Projection:
    p = Projection(graph, lens)
    for id in graph.nodes():
        eqv_class = lens.projection(graph.nodes[id]["state"])
        eqv_class_id = lens.serialize(eqv_class)

        if not p.graph.has_node(eqv_class_id):
            p.graph.add_node(eqv_class_id, state_ids = set(), eqv_class = eqv_class)
            p.graph.nodes[eqv_class_id]["action_src_ids"] = {}
            p.graph.nodes[eqv_class_id]["action_dst_eqv_class_ids"] = {}

        p.graph.nodes[eqv_class_id]["state_ids"].add(id)
        p.id_to_eqv_class_id[id] = eqv_class_id

    for (src, dst, action) in graph.edges(keys=True):
        src_eqv_class_id = p.id_to_eqv_class_id[src]
        dst_eqv_class_id = p.id_to_eqv_class_id[dst]

        src_eqv_class = p.graph.nodes[src_eqv_class_id]

        if action not in src_eqv_class["action_src_ids"]:
            src_eqv_class["action_src_ids"][action] = set()
        src_eqv_class["action_src_ids"][action].add(src)

        if action not in src_eqv_class["action_dst_eqv_class_ids"]:
            src_eqv_class["action_dst_eqv_class_ids"][action] = set()
        src_eqv_class["action_dst_eqv_class_ids"][action].add(dst_eqv_class_id)

        if not p.graph.has_edge(src_eqv_class_id, dst_eqv_class_id, action):
            p.graph.add_edge(src_eqv_class_id, dst_eqv_class_id, action, source_state_ids = set())
        p.graph.edges[src_eqv_class_id, dst_eqv_class_id, action]["source_state_ids"].add(src)

    # Run analysis
    for eqv_class_id in p.graph.nodes():
        eqv_class = p.graph.nodes[eqv_class_id]
        state_ids = eqv_class["state_ids"]
        eqv_class["single_state"] = len(state_ids) == 1
        eqv_class["contains_initial"] = any(p.parent.nodes[id]["initial"] for id in state_ids)

    for (s,d,a) in p.graph.edges(keys=True):
        edge = p.graph.edges[s, d, a]
        edge["definite"] = p.graph.nodes[s]["action_src_ids"][a] == p.graph.nodes[s]["state_ids"]
        edge["semi_deterministic"] = len(p.graph.nodes[s]["action_dst_eqv_class_ids"][a]) == 1

    return p
