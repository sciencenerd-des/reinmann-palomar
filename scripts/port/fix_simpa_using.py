#!/usr/bin/env python3
"""Lean 4.35 checks `simpa ... using h` at reducible transparency; `using!`
restores the default-transparency check that Lean 4.30 used. Rewrite the
first `using` of each `simpa` tactic (continuation lines must be indented
more deeply than the `simpa` line)."""
import re, sys
tot=0
for p in sys.argv[1:]:
    s=open(p,encoding='utf-8').read(); out=[]; i=0; n=0
    for m in re.finditer(r'\bsimpa\b', s):
        if m.start()<i: continue
        ls=s.rfind('\n',0,m.start())+1
        indent=len(s[ls:m.start()])-len(s[ls:m.start()].lstrip(' '))
        j=m.end(); k=None
        while j<len(s):
            if s[j]=='\n':
                nl=s[j+1:]; ind=len(nl)-len(nl.lstrip(' '))
                if nl.strip()=='' or ind<=indent: break
            if s.startswith('using',j) and not (s[j-1].isalnum() or s[j-1]=='_') and not (j+5<len(s) and (s[j+5].isalnum() or s[j+5] in '_!')):
                k=j; break
            j+=1
        if k is not None:
            out.append(s[i:k+5]); out.append('!'); i=k+5; n+=1
    out.append(s[i:]); 
    if n: open(p,'w',encoding='utf-8').write(''.join(out)); tot+=n
print('rewrote',tot,'simpa ... using')
