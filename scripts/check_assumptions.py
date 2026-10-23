#!/usr/bin/env python3
"""Check the assumptions of the main theorems (make check-assumptions).

Runs every `Print Assumptions` of theories/CheckAssumptions.v against the
built theories and fails unless each theorem is closed under the global
context, or uses only the axioms theories/CheckAssumptions.expected allows
it.  Each `Print Assumptions X.` is preceded by `Locate X.` in a temporary
copy, so that every printed block is matched to its theorem.
"""

import os
import re
import subprocess
import sys
import tempfile

THEORIES = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "theories")
SOURCE = os.path.join(THEORIES, "CheckAssumptions.v")
EXPECTED = os.path.join(THEORIES, "CheckAssumptions.expected")
PRINT = re.compile(r"^\s*Print Assumptions\s+([^\s.][^\s]*?)\s*\.\s*$")
CONSTANT = re.compile(r"^Constant\s+(\S+)")
HEADER = re.compile(r"^[A-Z][A-Za-z ]*:$")
ENTRY = re.compile(r"^(\S+)\s+:")


def read_expected():
    allowed = {}
    with open(EXPECTED) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            name, _, axioms = line.partition(":")
            allowed[name.strip()] = axioms.split()
    return allowed


def project_flags():
    """The -R/-Q and -arg flags of theories/_CoqProject, for rocq compile."""
    flags = []
    with open(os.path.join(THEORIES, "_CoqProject")) as f:
        for line in f:
            words = line.split()
            if not words or words[0].endswith(".v"):
                continue
            if words[0] in ("-R", "-Q") and len(words) == 3:
                flags += [words[0], os.path.join(THEORIES, words[1]), words[2]]
            elif words[0] == "-arg":
                flags += words[1::2]
    return flags


def run(names_lines):
    with tempfile.TemporaryDirectory() as tmp:
        script = os.path.join(tmp, "CheckAssumptionsRun.v")
        with open(script, "w") as f:
            f.writelines(names_lines)
        rocq = os.environ.get("ROCQ", "rocq")
        cmd = [rocq, "compile"] + project_flags() + [script]
        proc = subprocess.run(cmd, cwd=tmp, capture_output=True, text=True)
        if proc.returncode != 0:
            sys.stderr.write(proc.stdout + proc.stderr)
            sys.exit("check-assumptions: CheckAssumptions.v does not compile")
        return proc.stdout


def parse(output):
    """Map each theorem's full name to the assumption names printed for it."""
    result, current = {}, None
    for line in output.splitlines():
        m = CONSTANT.match(line)
        if m:
            current = m.group(1)
            result[current] = []
            continue
        if current is None or not line.strip() or line.startswith((" ", "\t")):
            continue
        if line.strip() == "Closed under the global context" or HEADER.match(line.strip()):
            continue
        m = ENTRY.match(line)
        if m:
            result[current].append(m.group(1))
    return result


def allowed_by(printed, allowed):
    return any(a == printed or a.endswith("." + printed) for a in allowed)


def main():
    # A wide margin, so that no name or assumption is wrapped over two lines.
    lines, count = ["Set Printing Width 10000.\n"], 0
    with open(SOURCE) as f:
        for line in f:
            m = PRINT.match(line)
            if m:
                lines.append("Locate %s.\n" % m.group(1))
                count += 1
            lines.append(line)
    found = parse(run(lines))
    if len(found) != count:
        sys.exit("check-assumptions: %d theorems listed, %d located" % (count, len(found)))
    expected, failures = read_expected(), []
    for name, assumptions in found.items():
        extra = [a for a in assumptions if not allowed_by(a, expected.get(name, []))]
        if extra:
            failures.append("%s uses %s" % (name, ", ".join(extra)))
    for name in expected:
        if name not in found:
            failures.append("%s is in CheckAssumptions.expected but not checked" % name)
    if failures:
        sys.stderr.write("\n".join(failures) + "\n")
        sys.exit("check-assumptions: %d problem(s)" % len(failures))
    print("check-assumptions: %d theorems, all as expected" % count)


if __name__ == "__main__":
    main()
