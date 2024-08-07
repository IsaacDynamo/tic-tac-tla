import subprocess
import os
from typing import List

from projection import project, Lens, parse_tla_dot

# Tool paths
JAVA = "C:/tools/amazon-corretto-11.0.15.9.1-windows-x64-jdk/jdk11.0.15_9/bin/java.exe"
TLA2TOOLS = "C:/tools/TLAToolbox-1.7.1-win32.win32.x86_64/toolbox/tla2tools.jar"

class Tlc:
    def __init__(self, java_path, tla2tools_path):
        self.java_path = java_path
        self.tla2tools_path = tla2tools_path

    # Generate dot file, with fast path based on file timestamps
    def make_dot(self, input_path: str, config_path: str, output_path: str):
        def file_ts(file: str) -> int:
            try:
                return os.path.getmtime(file)
            except FileNotFoundError:
                return 0

        def outdated(artifact: str, sources: List[str]) -> bool:
            artifact_ts = file_ts(artifact)
            return any(file_ts(src) > artifact_ts for src in sources)

        # Skip running TLC when sources are not newer then artifact
        if not outdated(output_path, [input_path, config_path]):
            return

        subprocess.run([
            self.java_path,
            "-jar", self.tla2tools_path,
            "-config", config_path,
            "-dump", "dot,actionlabels", output_path.removesuffix(".dot"),
            input_path],
            check = True)

class Dot:
    def run(self, *args):
        cmd = ["wsl.exe", "-e", "dot"]
        cmd.extend(list(args))
        subprocess.run(cmd, check = True)


def main():
    tlc = Tlc(JAVA, TLA2TOOLS)
    dot = Dot()

    os.makedirs("output", exist_ok=True)

    output_path = "output/tictactoe.dot"
    tlc.make_dot("tictactoe.tla", "minimal.cfg", output_path)

    with open(output_path) as f:
        graph = parse_tla_dot(f.read())

    class TurnLens(Lens):
        def map_state(self, state):
            return state["turn"]

        def map_action(self, action, type):
            return ""

    project(graph, TurnLens()).to_svg(dot, "output/turn_projection.svg")

    class ResultLens(Lens):
        def map_state(self, state):
            return state["result"]

        def map_action(self, action, type):
            return ""

    project(graph, ResultLens()).to_svg(dot, "output/result_projection.svg")

    class CountLens(Lens):
        show_node_count = True
        show_initial = True
        def map_state(self, state):
            if state["result"] != "?":
                return state["result"]
            pieces = len([x for x in state["board"].values() if x != " "])
            return f"Pieces {pieces}"

        def map_action(self, action, type):
            return ""

    project(graph, CountLens()).to_svg(dot, "output/count_projection.svg")

if __name__ == "__main__":
    main()