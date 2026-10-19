from pathlib import Path
from xml.dom.minidom import parse
import io, sys

PROJECT_ROOT = Path(__file__).resolve().parents[1]
SVG = parse(sys.stdin)
SVG_ELEMENT = SVG.getElementsByTagName("svg")[0]
ENTIRE_GRAPH_ELEMENT = SVG_ELEMENT.getElementsByTagName("g")[0]
ENTIRE_GRAPH_ELEMENT.removeChild(ENTIRE_GRAPH_ELEMENT.getElementsByTagName("title")[0])
SVG_ELEMENT.setAttribute("onload", "makeEdgesInteractive(evt)")
for line in io.open(PROJECT_ROOT / "assets" / "extra" / "header.html"):
    print(line, end='')
print('<link href="resources/depgraph.css" rel="stylesheet" type="text/css" />')
print('<script type="text/javascript" src="resources/depgraph.js"></script>')
print('<p class="depgraph-hint">Scroll to zoom, drag to move, double-click to see the whole graph; click an edge to highlight it.</p>')
SVG_ELEMENT.writexml(sys.stdout)
for line in io.open(PROJECT_ROOT / "assets" / "extra" / "footer.html"):
    print(line, end='')
