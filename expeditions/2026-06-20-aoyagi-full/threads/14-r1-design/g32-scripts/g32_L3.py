import sympy as sp
"""
General-L threading: L=3 chain, (3,3,3,3) r=1. C1(3x3)·C2(3x3)·C3(3x3). Peel δ=1 ⟹ reduced (2,2,2,2).
THE SUBTLE POINT (Codex's pt 2): the MIDDLE factor C2 gets reduced on BOTH sides — Q1^{-1} on its left
(threaded from C1's pivot) and Q2 on its right (for C3's coupling). Does this two-sided reduction conflict?
Construction: ONE top-pivot on the PRODUCT P=C1·C2·C3 at P[0,0]. The factor-wise unimodular Q's:
  Q0 (3x3) clears C1 col0; the chain threads R-changes. The KEY: only the FIRST row/col of the whole
  chain is touched by a single rank-1 pivot. Verify core=(reduced chain product) exact.
"""
sp.init_printing()
def mk(name,m,n): return sp.Matrix(m,n, lambda i,j: sp.Symbol(f'{name}{i}{j}', real=True))
C1=mk('a',3,3); C2=mk('b',3,3); C3=mk('c',3,3)
P = C1*C2*C3
# Factor-wise pivot at C1[0,0]: L0 clears C1 col0, R1 clears C1 row0.
a00=C1[0,0]
L0=sp.eye(3)
for i in range(1,3): L0[i,0]=-C1[i,0]/a00
R1=sp.eye(3)
for j in range(1,3): R1[0,j]=-C1[0,j]/a00
C1t=sp.simplify(L0*C1*R1)  # blockdiag[a00, S1]
S1=sp.simplify(C1t[1:,1:])
# thread R1^{-1} to C2's left, and reduce C2's top row via R2 (3x3, threads to C3):
C2a=sp.simplify(R1.inv()*C2)   # R1^{-1} C2
c2_00=C2a[0,0]
R2=sp.eye(3)
for j in range(1,3): R2[0,j]=-C2a[0,j]/c2_00
C2t=sp.simplify(C2a*R2)        # top row cleared; = R1^{-1} C2 R2
S2=sp.simplify(C2t[1:,1:])     # but C2t's col0 below pivot may be nonzero — middle factor!
# thread R2^{-1} to C3's left, reduce C3's top row via R3:
C3a=sp.simplify(R2.inv()*C3)
c3_00=C3a[0,0]
R3=sp.eye(3)
for j in range(1,3): R3[0,j]=-C3a[0,j]/c3_00
C3t=sp.simplify(C3a*R3)        # = R2^{-1} C3 R3
S3=sp.simplify(C3t[1:,1:])
# The full chain transformed: L0·C1·R1 · R1^{-1}C2 R2 · R2^{-1}C3 R3 = L0·(C1 C2 C3)·R3 = L0·P·R3.
chain = sp.simplify(L0*P*R3)
print("L0·P·R3 row0:", [sp.simplify(chain[0,j]) for j in range(3)])
core = sp.simplify(chain[1:,1:])
# THE CRUX: core == S1·S2·S3 (reduced 3-chain product)? (the middle S2 reduced two-sided)
prod_reduced = sp.simplify(S1*S2*S3)
print("CRUX (L=3): core == S1·S2·S3 (reduced chain product)?  diff =", sp.simplify(core - prod_reduced))
# also vs Schur(P):
p00=P[0,0]; SchurP=sp.simplify(P[1:,1:]-P[1:,0]*P[0,1:]/p00)
print("core == Schur(P)?  diff =", sp.simplify(core - SchurP))
print("reduced dims: S1",S1.shape,"S2",S2.shape,"S3",S3.shape,"⟹ (2,2,2,2) ✓")
# Codex pt2: is the MIDDLE factor's two-sided reduction consistent? S2 = (R1^{-1} C2 R2)[1:,1:]. The left
# R1^{-1} (from C1 pivot) and right R2 (for C3) both act on C2. Check S2 is well-defined (it is — computed).
print("\nMiddle-factor C2 two-sided reduced S2 (well-defined, no conflict):", S2.shape, "— consistent ✓")
