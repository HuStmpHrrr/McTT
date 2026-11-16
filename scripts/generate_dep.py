import itertools, re, sys, textwrap
from pathlib import Path
from typing import Iterable

PROJECT_ROOT = Path(__file__).resolve().parents[1]
THEORIES_ROOT = PROJECT_ROOT / "theories"
ROOT_MODULE_NAME = "Mctt"
COLORS = {
    "Algorithmic": "darkturquoise",
    "Completeness": "deeppink3",
    "Core": "goldenrod",
    "Entrypoint": "steelblue1",
    "Syntactic": "darkorange",
    "Semantic": "forestgreen",
    "Soundness": "goldenrod1",
    "Frontend": "darkslategray4",
    "Extraction": "darkslategray3",
    "SetModel": "mediumpurple2",
    "Consequences": "sienna2",
    "Reference": "lightsalmon3",
    "others": "lightpink",
}

# The folders right under Core take their color from that folder, so that
# Core/Completeness/Consequences stays a part of Completeness.
def color_of_module_parts(parts: tuple[str, ...]) -> str:
    if len(parts) > 2 and parts[0] == "Core" and parts[1] in COLORS:
        return COLORS[parts[1]]
    dedupe_parts = list(dict.fromkeys(parts))
    return next((COLORS[part] for part in reversed(dedupe_parts) if part in COLORS), COLORS["others"])

GRAPH_SET: set[str] = set()
EDGES: list[tuple[str, str]] = []

# The set model depends only on the syntax, but it is the last part of the
# metatheory: its files that import no other set-model file are ranked with
# the soundness theorem, so that the set model is drawn below it.
SETMODEL_PREFIX = f"{ROOT_MODULE_NAME}.Core.SetModel."
SETMODEL_ANCHOR = f"{ROOT_MODULE_NAME}.Core.Soundness"

def setmodel_rank() -> str:
    setmodel = {m for edge in EDGES for m in edge if m.startswith(SETMODEL_PREFIX)}
    entered = {sink for source, sink in EDGES if source in setmodel and sink in setmodel}
    sources = sorted(setmodel - entered)
    return f"""{{ rank=same; "{SETMODEL_ANCHOR}"; {" ".join(f'"{m}";' for m in sources)} }}"""

def under_subgraph(name: str, body: str) -> str:
    return f"""subgraph "{name}" {{ {body} }}"""

def subgraph_decl(*, name: str, label: str = "", tooltip: str = "", color: str, body: str = "") -> str:
    GRAPH_SET.add(name)
    return under_subgraph(name, f"""graph[color={color},fontcolor={color},label="{label}",tooltip="{tooltip}"]; node[fillcolor={color}]; {body}""")

def default_subgraph_decl(name: str, body: str = "") -> str:
    return subgraph_decl(name=name, label=name, tooltip=f"{ROOT_MODULE_NAME}.{name}", color=COLORS[name], body=body)

def core_subgraph_decl(name: str, body: str = "") -> str:
    return under_subgraph("Core", subgraph_decl(name=f"Core/{name}", label=name, tooltip=f"{ROOT_MODULE_NAME}.Core.{name}", color=COLORS[name], body=body))

DEPLINE_PATTERN = re.compile(r"(\S*\.vo).*:(.*)")
DEPSOURCE_PATTERN = re.compile(r"\S*\.vo")

def module_parts_of_path(path: str) -> tuple[str, ...]:
    return Path(path).resolve().relative_to(THEORIES_ROOT).with_suffix("").parts

def module_name_of_module_parts(parts: Iterable[str]) -> str:
    return f"""{ROOT_MODULE_NAME}.{".".join(parts)}"""

def module_name_of_path(path: str) -> str:
    return module_name_of_module_parts(module_parts_of_path(path))

def node_of_path(path: str) -> str:
    parts = module_parts_of_path(path)
    color = color_of_module_parts(parts)
    subgraph_names = list(itertools.accumulate(parts[:-1], func="{0}/{1}".format))
    module_name = module_name_of_module_parts(parts)
    node_label = parts[-1]

    # Handle special case for two main theorems
    # so that printed graph looks better
    if module_name == "Mctt.Core.Completeness" or module_name == "Mctt.Core.Soundness":
        result = under_subgraph(f"Core/{node_label}", f""""{module_name}"[label="{node_label}",tooltip="{module_name}",color={color},fillcolor=white];""")
    elif module_name == "Mctt.LibTactics":
        result = f"""{{ graph[cluster=false,rank=min]; "{module_name}"[label="{node_label}",tooltip="{module_name}",fillcolor={color}]; }}"""
    elif module_name == "Mctt.Core.Consequences.Consistency":
        result = f"""{{ cluster=false; rank=max; "{module_name}"[label="{node_label}",tooltip="{module_name}",fillcolor={color}]; }}"""
    else:
        result = f""""{module_name}"[label="{node_label}",tooltip="{module_name}",fillcolor={color}];"""

    for subgraph_name in reversed(subgraph_names):
        if subgraph_name in GRAPH_SET:
            result = under_subgraph(subgraph_name, result)
        else:
            GRAPH_SET.add(subgraph_name)
            result = under_subgraph(subgraph_name, f"""graph[cluster=true,label={parts[subgraph_names.index(subgraph_name)]},tooltip="{module_name_of_module_parts(subgraph_name.split("/"))}"]; {result}""")

    return result

def data_of_depline(depline: str) -> str:
    if result := DEPLINE_PATTERN.fullmatch(depline.strip()):
        sink_module = module_name_of_path(result.group(1))
        source_paths = result.group(2).split(" ")
        source_modules = [module_name_of_path(source_path) for source_path in source_paths if DEPSOURCE_PATTERN.match(source_path)]
        EDGES.extend((source_module, sink_module) for source_module in source_modules)
        edges = "\n".join(f""""{source_module}" -> "{sink_module}";""" for source_module in source_modules)
        return f"""{edges}{node_of_path(result.group(1))}"""
    else:
        raise ValueError(f"Broken Dependency: \"{depline}\"")

def gen_graph() -> str:
    newline = "\n"
    data = newline.join(data_of_depline(depline) for depline in sys.stdin)
    return textwrap.dedent(f"""
      digraph Mctt {{
        graph [center=true,class="depgraph",cluster=true,fontname="Open Sans",fontsize=28,label="Mctt",labeljust=l,labelloc=t,newrank=true,nodesep=0.1,penwidth=2,splines=true,tooltip=""];
        node [fontsize=18,shape=note,style=filled,URL="\\N.html"];
        {default_subgraph_decl("Algorithmic")}
        {default_subgraph_decl("Core")}
        {core_subgraph_decl("Completeness")}
        {core_subgraph_decl("Semantic")}
        {core_subgraph_decl("Soundness")}
        {core_subgraph_decl("Syntactic")}
        {core_subgraph_decl("SetModel")}
        {core_subgraph_decl("Consequences")}
        {default_subgraph_decl("Extraction")}
        {default_subgraph_decl("Frontend")}
        {default_subgraph_decl("Reference")}
        {textwrap.indent(data, "        ").lstrip()}
        {setmodel_rank()}
      }}""")

print(gen_graph())
