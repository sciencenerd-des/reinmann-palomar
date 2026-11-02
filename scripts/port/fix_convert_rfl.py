#!/usr/bin/env python3
"""After a stand-alone `convert ... using n` tactic, insert `all_goals try rfl`
to close the side goals that Mathlib v4.30's `convert` closed by `rfl` and that
v4.35's no longer does."""
import re, sys
tot=0
for p in sys.argv[1:]:
    L=open(p,encoding='utf-8').read().split('\n'); out=[]; i=0; n=0
    while i<len(L):
        line=L[i]; out.append(line)
        m=re.match(r'^(\s*)(·\s+)?convert\b',line)
        if m:
            ind=len(m.group(1))+(len(m.group(2)) if m.group(2) else 0)
            j=i
            while not re.search(r'\busing\s+\d+\s*$',L[j]):
                if j+1<len(L) and len(L[j+1])-len(L[j+1].lstrip())>len(m.group(1)) and L[j+1].strip() and not L[j+1].strip().startswith('·'):
                    j+=1; out.append(L[j])
                else: break
            if re.search(r'\busing\s+\d+\s*$',L[j]) and '<;>' not in L[j]:
                out.append(' '*ind+'all_goals try rfl'); n+=1
            i=j+1; continue
        i+=1
    if n: open(p,'w',encoding='utf-8').write('\n'.join(out)); tot+=n
print('inserted',tot)
