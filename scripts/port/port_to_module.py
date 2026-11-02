#!/usr/bin/env python3
"""Vendor the import closure of XiRectangle.Final from the reinmann checkout and
mechanically port each file to Lean's module system:
  * insert `module` before the first command (after leading plain comments),
  * turn every `import X` into `public import X`,
  * open `@[expose] public section` right after the import block.
Source files in the reinmann checkout are never modified."""
import os, re, sys, shutil
src, dst, listfile = sys.argv[1:4]
mods = [l.strip() for l in open(listfile) if l.strip()]
imp = re.compile(r'^(\s*)import\s+(\S+)\s*$')
for m in mods:
    rel = m.replace('.', '/') + '.lean'
    lines = open(os.path.join(src, rel), encoding='utf-8').read().split('\n')
    out = []; i = 0; n = len(lines)
    # leading plain comments / blank lines
    while i < n:
        s = lines[i].strip()
        if s == '' or s.startswith('--'):
            out.append(lines[i]); i += 1; continue
        if s.startswith('/-') and not s.startswith('/-!') and not s.startswith('/--'):
            while i < n:
                out.append(lines[i]); done = '-/' in lines[i][lines[i].find('/-')+2:] if lines[i].strip().startswith('/-') else '-/' in lines[i]
                i += 1
                if done: break
            continue
        break
    out.append('module'); out.append('')
    last_imp = None
    while i < n:
        s = lines[i].strip()
        mm = imp.match(lines[i])
        if mm:
            out.append(f'public import {mm.group(2)}'); last_imp = len(out); i += 1; continue
        if s == '' or s.startswith('--'):
            out.append(lines[i]); i += 1; continue
        break
    if last_imp is None: last_imp = len(out)
    out.insert(last_imp, '\n@[expose] public section')
    out.extend(lines[i:])
    p = os.path.join(dst, rel); os.makedirs(os.path.dirname(p), exist_ok=True)
    open(p, 'w', encoding='utf-8').write('\n'.join(out))
print('ported', len(mods), 'files')
