import sympy as sp
import numpy as np
# Test L=3 (2,2,2,2): is the residual core empty at every fibre v except deepest, or are there
# intermediate singular fibre points with non-empty cores?
# Chain C1 C2 C3, each 2x2. prod = C1 C2 C3. Fibre {prod=0}.
# Take v in an intermediate stratum, e.g. t=(1,1,0): rank C1=1, rank(C1C2)=1, rank(C1C2C3)=0.
# Is v a smooth point of {prod=0}? Compute generator Jacobian rank vs codim.
w = sp.symbols('w0:12', real=True)  # 3 matrices x 4 entries
C1=sp.Matrix([[w[0],w[1]],[w[2],w[3]]]); C2=sp.Matrix([[w[4],w[5]],[w[6],w[7]]]); C3=sp.Matrix([[w[8],w[9]],[w[10],w[11]]])
# v: pick rank C1=1, then C2 generic (rank C1C2=1), then C3 s.t. C1C2C3=0.
# v1 = [[1,0],[0,0]] (rank1). v2 = [[1,1],[1,1]]? rank1. C1 v2 = [[1,1],[0,0]] rank1. 
# Need (C1 C2) C3 = 0: C1C2 = [[1,1],[0,0]], C3 with cols in ker([[1,1],[0,0]]) = {x: x0+x1=0} = span[1,-1].
# v3 cols = multiples of [1,-1]: v3 = [[1,2],[-1,-2]].
v1=sp.Matrix([[1,0],[0,0]]); v2=sp.Matrix([[1,1],[1,1]]); v3=sp.Matrix([[1,2],[-1,-2]])
# check fibre: 
prodv = v1*v2*v3
print("v in fibre? prod(v) =", (prodv).tolist(), "(should be 0)")
# build germ
C1v=v1+sp.Matrix([[w[0],w[1]],[w[2],w[3]]]); C2v=v2+sp.Matrix([[w[4],w[5]],[w[6],w[7]]]); C3v=v3+sp.Matrix([[w[8],w[9]],[w[10],w[11]]])
P=sp.expand(C1v*C2v*C3v)
allv=list(w)
gens=[P[i,j] for i in range(2) for j in range(2)]
J=sp.Matrix([[sp.diff(sp.expand(g),vv).subs({x:0 for x in allv}) for vv in allv] for g in gens])
rk=J.rank()
from itertools import product
def Mval(M,t):
    tt=[M[0]]+list(t); L=len(M)-1
    return sum((tt[j-1]-tt[j])*(M[j]-tt[j]) for j in range(1,L+1))
print(f"=== L=3 (2,2,2,2), v in S(1,1,0): Jacobian rank = {rk}, Mval(1,1,0) = {Mval((2,2,2,2),(1,1,0))} ===")
print(f"  gens=4. rank {rk} => {'SMOOTH (core empty)' if rk==4 else 'SINGULAR (residual core non-empty, dim<'+str(4-rk if rk<4 else 0)+')'}")
# also test t=(1,0,0):
v1b=sp.Matrix([[1,0],[0,0]]); v2b=sp.Matrix([[0,0],[1,1]]); v3b=sp.Matrix([[1,1],[1,1]])
print("  t=(1,0,0) test: prod=", (v1b*v2b*v3b).tolist())
C1b=v1b+sp.Matrix([[w[0],w[1]],[w[2],w[3]]]); C2b=v2b+sp.Matrix([[w[4],w[5]],[w[6],w[7]]]); C3b=v3b+sp.Matrix([[w[8],w[9]],[w[10],w[11]]])
Pb=sp.expand(C1b*C2b*C3b); gensb=[Pb[i,j] for i in range(2) for j in range(2)]
Jb=sp.Matrix([[sp.diff(sp.expand(g),vv).subs({x:0 for x in allv}) for vv in allv] for g in gensb])
print(f"  t=(1,0,0): Jac rank = {Jb.rank()}, Mval(1,0,0)={Mval((2,2,2,2),(1,0,0))}")
