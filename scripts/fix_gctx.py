#!/usr/bin/env python3
"""Fix the global context of a semantic file.

The file's commands go into sections [Fixed_GCtx] with [Context {GC : GCtx}].
What a section cannot export is made local inside it and re-declared after its
[End]: hints, [Arguments], instances (including those of
[Add Parametric Morphism]), notations.  Tactics cannot be defined in a section
and still be seen after it, so a section is closed before each top-level
[Ltac]/[Tactic Notation] and a new one opened after it.  [Reserved Notation]s go
to the top."""
import re, sys

HEADER = re.compile(r'\s*(From|Require|Import|Export|Open|Set|#\[local\] Open)\b')

def take(body, j):
    """The command starting at line j: up to the line ending in '.'"""
    k = j; cmd = [body[j]]
    while not cmd[-1].rstrip().endswith('.'):
        k += 1; cmd.append(body[k])
    return cmd, k + 1

def transform(src):
    lines = src.split('\n')
    # the header: blank lines, comments and Require/Import lines at the top
    i, depth, cont = 0, 0, False
    while i < len(lines):
        l = lines[i]
        if depth == 0 and not (cont or l.strip() == '' or HEADER.match(l) or l.lstrip().startswith('(*')):
            break
        depth += l.count('(*') - l.count('*)')
        # a header command continued on the next line
        cont = depth == 0 and l.strip() != '' and (cont or HEADER.match(l)) and not l.rstrip().endswith('.')
        i += 1
    head, body = lines[:i], lines[i:]
    # the relations NbE defines, at the fixed global context
    body = [re.sub(r'(?<![\w.])(initial_env|nbe_ty|nbe)(?=\s)', r'\1_f', l) for l in body]
    head = [re.sub(r'Import Domain_Notations\.', 'Import Domain_Notations Fixed_Notations.', l) for l in head]
    if not any('Fixed_Notations' in l for l in head):
        head.append('Import Fixed_Notations.')
    res = list(head)
    chunk, tail = [], []

    def flush():
        if any(l.strip() for l in chunk):
            res.extend(['', 'Section Fixed_GCtx.', '  Context {GC : GCtx}.', ''])
            res.extend(chunk)
            res.extend(['End Fixed_GCtx.', ''])
            res.extend(tail)
        else:
            res.extend(chunk)
        chunk.clear(); tail.clear()

    j = 0
    while j < len(body):
        l = body[j]
        # a top-level tactic, possibly under an attribute line
        is_attr = re.match(r'#\[(local|export|global)\]\s*$', l)
        nxt = body[j+1] if j + 1 < len(body) else ''
        if re.match(r'(#\[local\]\s*)?(Ltac|Tactic Notation)\b', l) or (is_attr and re.match(r'(Ltac|Tactic Notation)\b', nxt)):
            flush()
            if is_attr:
                cmd, j = take(body, j + 1); res.append(l); res.extend(cmd)
            else:
                cmd, j = take(body, j); res.extend(cmd)
            continue
        # [Arguments] may be global in a section, and is discharged correctly
        m = re.match(r'(\s*)(#\[global\]\s*)?Arguments\b(.*)$', l)
        if m:
            cmd, k = take(body, j)
            chunk.append(m.group(1) + '#[global] Arguments' + m.group(3)); chunk.extend(cmd[1:])
            j = k; continue
        m = re.match(r'(\s*)#\[(export|global)\]\s*$', l)
        if m and re.match(r'\s*Arguments', nxt):
            cmd, k = take(body, j + 1)
            chunk.append('#[global] ' + cmd[0].lstrip()); chunk.extend(cmd[1:])
            j = k; continue
        if m and re.match(r'\s*(Hint|Instance)', nxt):
            cmd, k = take(body, j + 1)
            if cmd[0].lstrip().startswith('Instance'):
                name = re.match(r'\s*Instance\s+(\S+)', cmd[0]).group(1)
                chunk.append('#[local] ' + cmd[0].lstrip()); chunk.extend(cmd[1:])
                tail.append('#[%s] Existing Instance %s.' % (m.group(2), name))
            else:
                chunk.extend(cmd)
                tail.append('#[%s]' % m.group(2)); tail.extend(c.lstrip() for c in cmd)
            j = k; continue
        m = re.match(r'(\s*)#\[(export|global)\]\s*(Hint)(.*)$', l)
        if m:
            cmd, k = take(body, j)
            chunk.append(m.group(1) + m.group(3) + m.group(4)); chunk.extend(cmd[1:])
            tail.append('#[%s] %s%s' % (m.group(2), m.group(3), m.group(4)))
            tail.extend(c.lstrip() for c in cmd[1:])
            j = k; continue
        if re.match(r'Add Parametric Morphism\b', l):
            k = j; cmd = [l]
            while not re.search(r'\bas\s+([\w']+)\s*\.', cmd[-1]):
                k += 1; cmd.append(body[k])
            name = re.search(r'\bas\s+([\w']+)\s*\.', cmd[-1]).group(1)
            chunk.extend(cmd); tail.append('#[export] Existing Instance %s_Proper.' % name)
            j = k + 1; continue
        if re.match(r'(Reserved Notation|Notation|Infix)\b', l):
            cmd, k = take(body, j)
            if l.startswith('Reserved'):
                res.extend(cmd)
            else:
                chunk.extend(cmd); tail.extend(cmd)
            j = k; continue
        m = re.match(r'\s*where (".*?") := (\(.*\))(\s*:\s*\w+)?\s*\.?\s*$', l)
        if m:
            tail.append('Notation %s := %s%s.' % (m.group(1), m.group(2), m.group(3) or ''))
        chunk.append(l); j += 1
    flush()
    return '\n'.join(res) + '\n'

for f in sys.argv[1:]:
    s = open(f).read()
    if 'Section Fixed_GCtx' in s: continue
    open(f, 'w').write(transform(s))
