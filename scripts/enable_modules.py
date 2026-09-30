#!/usr/bin/env python3
"""Re-enable modules commented out of [_CoqProject] while being ported."""
import sys
p = '_CoqProject'
s = open(p).read()
for f in sys.argv[1:]:
    f = f[2:] if f.startswith('./') else f
    line = '# ./%s  (not yet ported to module parameters)' % f
    if line in s:
        s = s.replace(line, './%s' % f)
    else:
        print('not found: ' + f)
open(p, 'w').write(s)
