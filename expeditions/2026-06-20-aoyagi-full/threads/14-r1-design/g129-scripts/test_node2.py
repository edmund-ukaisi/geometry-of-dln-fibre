import sympy as sp, numpy as np
# SECOND NODE: a reduced node with a 4x3 hard-pivot factor  Â (4 rows, 3 cols, Â[0,0]=1 hard),
# times A2 (3 x N). This is the (4,3,2)-ish reduced shape (non-square Â). Test the SAME squeeze.
# Â = [[1, a01, a02],[a10..],[a20..],[a30..]] (12 entries, [0,0]=1). A2 = 3x2 (6 entries).
m_rows, k_inner, n_cols = 4, 3, 2
Ahat = sp.Matrix(m_rows, k_inner, lambda i,j: 1 if (i,j)==(0,0) else sp.Symbol(f'a{i}{j}', real=True))
A2   = sp.Matrix(k_inner, n_cols, lambda i,j: sp.Symbol(f'b{i}{j}', real=True))
M = sp.expand(Ahat*A2)
def fro2(X): return sp.expand(sum(X[i,j]**2 for i in range(X.rows) for j in range(X.cols)))
F = fro2(M)
# Regular gens E = row0 of M (n_cols of them). Schur core: clear col0 of Â via R (col ops) and row0 of Â via L.
a = sp.Matrix(1, k_inner-1, lambda i,j: Ahat[0,j+1])      # a = Â[0,1:]  (1 x (k-1))
bvec = sp.Matrix(m_rows-1, 1, lambda i,j: Ahat[i+1,0])    # b = Â[1:,0]  ((m-1) x 1)
D = Ahat[1:,1:]                                            # (m-1)x(k-1)
Sm = sp.expand(D - bvec*a)                                 # Schur complement (m-1)x(k-1)
A2red = A2[1:,:]                                           # rows 1.. of A2 ((k-1) x n)
E = [M[0,j] for j in range(n_cols)]
G2 = fro2(sp.expand(Sm*A2red))
Phi = sp.expand(sum(e**2 for e in E) + G2)
allv = sorted(F.free_symbols, key=lambda s:str(s))
fF=sp.lambdify(allv,F,'numpy'); fP=sp.lambdify(allv,Phi,'numpy')
nv=len(allv)
print(f"(4,3,2)-shape reduced node: Â {m_rows}x{k_inner} (pivot hard), A2 {k_inner}x{n_cols}; #vars={nv}")
print("Squeeze F/Φ near 0:")
rng=np.random.default_rng(3)
for scale in [0.3,0.1,0.03,0.01]:
    X=rng.uniform(-scale,scale,(40000,nv)); args=[X[:,i] for i in range(nv)]
    Fv=fF(*args); Pv=fP(*args); msk=np.abs(Pv)>1e-16; ratio=Fv[msk]/Pv[msk]
    print(f"  scale={scale}: min={ratio.min():.4f} max={ratio.max():.4f}")
# structural: F-Φ ∈ ideal(E)?  set E=0 (b0j = -(a01 b1j + a02 b2j)) and check F-Φ -> 0.
subE={}
for j in range(n_cols):
    subE[A2[0,j]] = -sum(Ahat[0,kk]*A2[kk,j] for kk in range(1,k_inner))
FmP = sp.expand(F-Phi)
print("(F-Φ)|{E=0} =", sp.simplify(FmP.subs(subE)), " (0 ⟹ structural squeeze, F-Φ ∈ ideal(E))")
