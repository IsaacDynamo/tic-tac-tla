import os
import utils
from projection import project, Lens, parse_tla_dot

# Tool paths
JAVA = "C:/tools/amazon-corretto-11.0.15.9.1-windows-x64-jdk/jdk11.0.15_9/bin/java.exe"
TLA2TOOLS = "C:/tools/TLAToolbox-1.7.1-win32.win32.x86_64/toolbox/tla2tools.jar"

class TurnLens(Lens):
    def projection(self, state):
        return state["turn"]

class ResultLens(Lens):
    def projection(self, state):
        return state["result"]

class CountLens(Lens):
    show_node_count = True

    def projection(self, state):
        if state["result"] != "?":
            return state["result"]
        pieces = len([x for x in state["board"].values() if x != " "])
        return f"Pieces {pieces}"

    def map_action(self, action, type):
        return ""


def main():
    tlc = utils.Tlc(JAVA, TLA2TOOLS)
    dot = utils.Dot()

    os.makedirs("output", exist_ok=True)

    output_path = "output/tictactoe.dot"
    tlc.make_dot("tictactoe.tla", "minimal.cfg", output_path)

    with open(output_path) as f:
        graph = parse_tla_dot(f.read())

    project(graph, TurnLens()).to_svg(dot, "output/turn_projection.svg")
    project(graph, ResultLens()).to_svg(dot, "output/result_projection.svg")
    project(graph, CountLens()).to_svg(dot, "output/count_projection.svg")


if __name__ == "__main__":
    main()
