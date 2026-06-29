"""
Verify the BLOCK-TRIANGULAR structure of J under the b-0 boundary ordering, at (3,3,3,3).
The per-piece factorization as a PRODUCT of triangular pieces is equivalent to:
  J, with outputs grouped by 'piece' and inputs grouped by boundary, is block-triangular,
  diagonal blocks = the per-boundary frame factors (det = (detK)^{r+c}*lduMon) + radial.

We assign each output A_k entry and each input coord to a 'piece index' and check the
off-(block-)diagonal vanishing in ONE direction (the b-0 one-sidedness).
"""
import sympy as sp
from sympy import symbols, eye, zeros, Matrix, expand
from perpiece_v2 import build, flatten
from anchor3333 import blocks_3333

NC=27
x=symbols('x0:%d'%NC,real=True); u=x[0]
bl,used=blocks_3333(x)
A,C=build(3,[3,3,3,3],[3,3,2,1],bl,u)
vec=flatten(A,3)
n=len(vec)
J=Matrix(n,n,lambda r,c: sp.diff(vec[r],x[c]))

# coord -> boundary (the 'owning' boundary in the b-0 sense: which K-core/N/W it belongs to)
own={0:'radial-u'}
for j in range(1,12): own[j]='b1'
for j in range(12,24): own[j]='b2'
for j in range(24,27): own[j]='leaf'

# output A_k entry -> 'piece': the boundary whose K-core/det content it carries.
# A_k top T[k+1] rows = C_{k+1} - N_k W_k (carries boundary k+1's K-core); bottom c_k rows = W_k (boundary k lift).
Text=[3,3,2,1]
out_piece=[]
for k in range(3):
    Tk1=Text[k+1]; ck=[3,3,3][k]-Tk1  # Wext k = 3
    rows=A[k].rows; cols=A[k].cols
    for i in range(rows):
        for jj in range(cols):
            if i < Tk1:
                out_piece.append(f'b{k+1}' if k+1<3 else ('leaf' if k+1==3 else f'b{k+1}'))
            else:
                out_piece.append(f'b{k}-lift')

print("Distinct output pieces:", sorted(set(out_piece)))
print("Distinct coord owners:", sorted(set(own.values())))
# Cross-coupling matrix: for each (output piece P, coord owner Q), is there a nonzero J entry?
import collections
coupling=collections.defaultdict(bool)
for r in range(n):
    for c in range(n):
        if J[r,c]!=0:
            coupling[(out_piece[r], own[c])]=True
owners=sorted(set(own.values()))
pieces=sorted(set(out_piece))
print("\nCOUPLING TABLE (rows=output piece, cols=coord owner; X = nonzero block):")
print("            "+"".join(f"{o:>12}" for o in owners))
for p in pieces:
    print(f"{p:>12}"+"".join(("    X       " if coupling[(p,o)] else "    .       ") for o in owners))
