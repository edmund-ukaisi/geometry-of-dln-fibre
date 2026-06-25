import sympy as sp
print("="*78)
print("CROSS-CHECK 2 (structural): why n=M(last) Morse count is L=2-only")
print("="*78)
print("""
At the deepest node, blow up layer 0: A0 = y0·Ahat. core = ||Ahat·B||^2, B = A1·A2···A^L.
The Schur row-decomp: Erow = (row 0 of Ahat·B) = B[0,:] + u·Bred, Bred = B[1:,:].

L=2 case: B = A1 (a SINGLE free matrix, k×n). Then B[0,:] and Bred are FREE LINEAR coordinates.
  Erow_j = B[0,j] + sum_i u_i Bred[i,j] is, at fixed (u,Bred), a det-1 affine SHEAR of the free
  B[0,j]. So {Erow_j} are n FREE smooth coords (unipotent reparametrization). => clean Morse block,
  count n = M(last). VALID.

L>=3 case: B = A1·A2···A^L is a PRODUCT of >=2 free matrices. B[0,:] is NOT a free coordinate --
  it is a degree-(L-1) polynomial in the entries of A1..A^L (the (0,:) row of the product). So:
""")
# Demonstrate L=3: B = A1·A2, A1 (k x p), A2 (p x n). B[0,j] = sum_a A1[0,a] A2[a,j] -- BILINEAR.
k,p,n=2,2,2
A1=sp.Matrix(k,p,lambda i,j:sp.Symbol(f'P{i}{j}'))
A2=sp.Matrix(p,n,lambda i,j:sp.Symbol(f'Q{i}{j}'))
B=A1*A2
print(f"  L=3: B=A1·A2.  B[0,0] = {B[0,0]}  (BILINEAR in A1,A2 entries, NOT a free coord).")
print("  => Erow_0 = B[0,0] + u·Bred[:,0] is a bilinear+linear form, NOT a free linear coordinate.")
print("  => {Erow_j} are NOT n free smooth Morse directions: the map (free params)->(Erow) is NOT")
print("     a diffeo (degenerate Jacobian where the product degenerates). The 'n Morse squares'")
print("     OVERCOUNTS the genuine smooth directions.")
print()
print("STRUCTURAL ROOT (schurStateRed preserves depth): redM=(M0-1,M1-1,M2,...,M_last) keeps L layers.")
print("  So the recursion NEVER reaches the L=2 (single-free-B) base where Erow is genuinely free.")
print("  Every node with L>=3 has a PRODUCT B => the n-Morse-count is wrong at every such node.")
print("  The true per-node increment d = minAdm(M)-minAdm(redM) is NON-LOCAL (depends on the whole")
print("  tail profile, not just M_last) for L>=3.")
print()
# verify d = minAdm - minAdm(red) vs n=M_last for the witnesses
import itertools
def admBound(M,j,L): return min(M[0],M[1]) if j==0 else M[j+1]
def adm(M):
    L=len(M)-1; rngs=[range(admBound(M,j,L)+1) for j in range(L)]
    for T in itertools.product(*rngs):
        if all(T[i]>=T[j] for i in range(L) for j in range(L) if i<=j) and (L==0 or T[L-1]==0): yield T
def Mval(M,T):
    L=len(M)-1; tot=0
    for j in range(L):
        tprev=M[0] if j==0 else T[j-1]; tot+=(tprev-T[j])*(M[j+1]-T[j])
    return tot
def minAdm(M): return min(Mval(M,T) for T in adm(M))
def redM(M): return [M[s]-1 if s<=1 else M[s] for s in range(len(M))]
print("  per-node true increment d vs cover's n=M_last:")
for M in [[3,3,3,3],[2,2,2,3],[3,3,3]]:
    d=minAdm(M)-minAdm(redM(M)); print(f"    M={M}: d=minAdm-minAdm(red)={d}, n=M_last={M[-1]}, equal? {d==M[-1]}")
