#!/usr/bin/env python3
"""Self-contained: emit the 9 explicit W3-clean native σ_p block-shear displacements for (3,3,4)
(dom(i,j) = surviving A0[i,j]). φ_(i,j)[k] = (shearH_disp(u∘σ))[σ(k)], σ = colswap(j)∘rowswap(i).
This is the DIRECT native form (NOT the σ⁻¹∘shearH∘σ conjugate). See assembly-extraction.md §2."""
import sympy as sp
u = sp.symbols('u0:21')
def shearH_disp(w):  # the canonical (dom 0,0) displacement = Corank2ChartJac.shearPhiH
    g=[sp.Integer(0)]*21
    g[4]=w[0]*w[2]; g[5]=w[1]*w[2]; g[6]=w[0]*w[3]; g[7]=w[1]*w[3]
    g[8]=-w[0]*w[12]-w[1]*w[16]; g[9]=-w[0]*w[13]-w[1]*w[17]
    g[10]=-w[0]*w[14]-w[1]*w[18]; g[11]=-w[0]*w[15]-w[1]*w[19]
    return g
A0slot={(0,0):20,(0,1):2,(0,2):3,(1,0):0,(1,1):4,(1,2):6,(2,0):1,(2,1):5,(2,2):7}
def rowswap(i):
    if i==0: return lambda k:k
    m={}
    for j in range(3): m[A0slot[(0,j)]]=A0slot[(i,j)]; m[A0slot[(i,j)]]=A0slot[(0,j)]
    for a in range(4): m[8+a]=8+4*i+a; m[8+4*i+a]=8+a
    return lambda k:m.get(k,k)
def colswap(j):
    if j==0: return lambda k:k
    m={}
    for i in range(3): m[A0slot[(i,0)]]=A0slot[(i,j)]; m[A0slot[(i,j)]]=A0slot[(i,0)]
    return lambda k:m.get(k,k)
def sigma(i,j):
    r=rowswap(i); c=colswap(j); return lambda k: c(r(k))
for i in range(3):
  for j in range(3):
    s=sigma(i,j); disp=shearH_disp([u[s(t)] for t in range(21)])
    phi=[sp.expand(disp[s(k)]) for k in range(21)]
    nz={k:phi[k] for k in range(21) if phi[k]!=0}
    reads=sorted({int(str(x)[1:]) for v in nz.values() for x in v.free_symbols})
    print(f"dom({i},{j}) pivot=slot{A0slot[(i,j)]} cleared={sorted(nz)} reads={reads}")
    for k,v in nz.items(): print(f"    phi[{k}] = {v}")
    print()
