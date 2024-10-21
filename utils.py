import os
import subprocess
from typing import List

class Tlc:
    def __init__(self, java_path, tla2tools_path):
        self.java_path = java_path
        self.tla2tools_path = tla2tools_path

    # Generate dot file, with fast path based on file timestamps
    def make_dot(self, input_path: str, config_path: str, output_path: str):
        def file_ts(file: str) -> float:
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