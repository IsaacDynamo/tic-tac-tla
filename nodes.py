import os
import utils

from projection import IdentityLens, parse_tla_dot

# Tool paths
JAVA = "C:/tools/amazon-corretto-11.0.15.9.1-windows-x64-jdk/jdk11.0.15_9/bin/java.exe"
TLA2TOOLS = "C:/tools/TLAToolbox-1.7.1-win32.win32.x86_64/toolbox/tla2tools.jar"

tlc = utils.Tlc(JAVA, TLA2TOOLS)
dot = utils.Dot()

os.makedirs("output", exist_ok=True)

output_path = "output/nodes.dot"
tlc.make_dot("nodes.tla", "nodes.cfg", output_path)
