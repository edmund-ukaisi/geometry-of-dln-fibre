#!/usr/bin/env python3
"""Mechanism of closure: the per-cut inequality with TRUE minAdm on redChain,
   and whether cap-active cuts are ever binding."""
import io, contextlib
_buf = io.StringIO()
with contextlib.redirect_stdout(_buf):
    import rankcharge as R
from itertools import product

minAdm = R.minAdmRec
redChain = R.redChain

def analyse(M):
    """returns list of (t,a,b,s,capActive, as_sum, cmp) and the min."""
    n = min(M[2:])
    m = minAdm(M)
    rows=[]
    for t in range(min(M[0],M[1])+1):
        a=M[0]-t; b=M[1]-t; s=min(b,n)
        capActive = (s<b and a>0)
        val = a*s + minAdm(redChain(t,M))
        rows.append((t,a,b,s,capActive,val, "BIND" if val==m else ("<<<" if val<m else "")))
    return m, rows

# ---- per-cut inequality  a*s + minAdm(redChain) >= minAdm  at TOP level, exhaustive ----
print("== per-cut inequality (top level), exhaustive over L+1=3,4,5 ==")
for Lp1, wmax in [(3,7),(4,6),(5,4)]:
    percut_fail=0
    capactive_binding=0     # cap-active cut that BINDS (equals minAdm)
    total_chains=0
    ex_capbind=[]
    for M in product(range(0,wmax+1),repeat=Lp1):
        if len(M)<3: continue
        total_chains+=1
        m,rows=analyse(M)
        for (t,a,b,s,ca,val,tag) in rows:
            if val<m: percut_fail+=1
            if ca and val==m:
                capactive_binding+=1
                if len(ex_capbind)<10: ex_capbind.append((M,t,a,b,s,val,m))
    print(f"  L+1={Lp1}, w0..{wmax}: chains={total_chains}  per-cut(<minAdm) fails={percut_fail}  "
          f"cap-active-BINDING cuts={capactive_binding}")
    if ex_capbind:
        print(f"    e.g. cap-active binding: {ex_capbind[:6]}")

# ---- Is there ALWAYS a cap-INACTIVE cut that binds?  (mechanism for equality) ----
print("\n== is there always a cap-inactive binding cut (a==0 or s==b)? ==")
for Lp1, wmax in [(3,7),(4,6),(5,4)]:
    no_capinactive_bind=0; total=0; ex=[]
    for M in product(range(0,wmax+1),repeat=Lp1):
        if len(M)<3: continue
        total+=1
        m,rows=analyse(M)
        has = any((not ca) and val==m for (t,a,b,s,ca,val,tag) in rows)
        if not has:
            no_capinactive_bind+=1
            if len(ex)<10: ex.append((M,m,rows))
    print(f"  L+1={Lp1}, w0..{wmax}: chains={total}  chains w/o any cap-inactive binding cut = {no_capinactive_bind}")
    for M,m,rows in ex[:4]:
        print(f"     {M} minAdm={m}: {[(r[0],r[3],r[4],r[5]) for r in rows]}")

# ---- worked breakdown of the mission anchors (as/ab per cut, cap flag) ----
print("\n== mission-anchor per-cut breakdown (t: a,b,s cap? -> as_sum vs minAdm) ==")
for M in [(2,4,1),(3,3,4),(3,3,3,4),(4,4,2,2)]:
    m,rows=analyse(M)
    print(f"  {M} minAdm={m}: " + "  ".join(
        f"t{t}[{a}x{s}{'*' if ca else ''}]={val}{'(B)' if tag=='BIND' else ''}"
        for (t,a,b,s,ca,val,tag) in rows))
print("  legend: t{t}[a x s]  '*'=cap active (s<b, a>0)  '(B)'=binding (=minAdm)")
