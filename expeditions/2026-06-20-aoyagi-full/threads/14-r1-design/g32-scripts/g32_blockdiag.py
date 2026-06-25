import sympy as sp
"""
Refinement: G3.2 needs FULL block-diagonalization of the PRODUCT (blockdiag[E_1, ∏C']) + the additivity
split ‖∏C‖² = ‖reg‖² + ‖∏C'‖². The previous L1·P·R2 was block-TRIANGULAR (col0 not cleared).
Full Schur block-diag of P needs BOTH L (clear col0) and R (clear row0): L_P P R_P = blockdiag[P00, Schur(P)].
But the CHAIN constraint: the Q's act FACTOR-WISE (Q0 C1 Q1)(Q1^{-1} C2 Q2) — the inner Q1 Q1^{-1} cancels.
So the product transform is Q0 P Q2 (only the OUTER factors' Q's survive on the product!). 
⟹ the product is transformed by Q0 (left, 3x3 unimodular) and Q2 (right, 3x3 unimodular) ONLY.
Q0 P Q2 = blockdiag[P00, Schur(P)]: this is EXACTLY the single-matrix block_elimination on P, with
Q0=L_P, Q2=R_P. The inner Q1 is FREE (any unimodular) — it doesn't affect the product but reshapes C1,C2.

SO the product-level G3.2 = block_elimination applied to P (ALREADY DONE for single matrix). The genuinely
NEW content is: (a) the residual Schur(P) is a REDUCED CHAIN product C1'·C2' (the factor-wise reduction
threads), and (b) the additivity split. Let me verify (a) the FULL block-diag + (b) the residual factors.
"""
sp.init_printing()
C1 = sp.Matrix(3,3, lambda i,j: sp.Symbol(f'a{i}{j}', real=True))
C2 = sp.Matrix(3,3, lambda i,j: sp.Symbol(f'b{i}{j}', real=True))
P = C1*C2
p00 = P[0,0]
# FULL block-diag of P (both sides): L_P (clear col0), R_P (clear row0)
LP = sp.eye(3)
for i in range(1,3): LP[i,0] = -P[i,0]/p00
PR = LP*P  # col0 cleared below pivot
RP = sp.eye(3)
for j in range(1,3): RP[0,j] = -PR[0,j]/PR[0,0]
Pbd = sp.simplify(LP*P*RP)
print("Q0·P·Q2 (Q0=LP, Q2=RP) FULLY block-diag?")
print("  row0:", [sp.simplify(Pbd[0,j]) for j in range(3)], " col0:", [sp.simplify(Pbd[i,0]) for i in range(3)])
SchurP = sp.simplify(Pbd[1:,1:])
print("  residual 2x2 = Schur(P) ✓")

# (a) Does Schur(P) FACTOR as a reduced chain C1'·C2' (2x2 each)?
# Aoyagi: the SAME pivot, applied to the factors, gives C1' = Schur(C1 w.r.t the pivot col/row mapping),
# C2' = Schur(C2 ...). But the pivot is on the PRODUCT, not on C1 or C2 individually. The factor-wise
# reduction: choose the inner Q1 to align. Let me TEST whether Schur(P) = S1·S2thread for the factor
# reductions from the EARLIER run (S1=Schur(C1), and the threaded C2). From the prev run, core=Schur(P)
# was = (L1 P R2)[1:,1:] = the chain-reduced residual. Let me extract the FACTORED form:
#   L1 P R2 = (L1 C1 R1)(R1^{-1} C2 R2) = blockdiag[a00,S1] · (R1^{-1}C2 R2).
# For this to be blockdiag, need (R1^{-1}C2 R2) to have the right block structure on the 1: block.
a00=C1[0,0]
L1=sp.eye(3); 
for i in range(1,3): L1[i,0]=-C1[i,0]/a00
R1=sp.eye(3)
for j in range(1,3): R1[0,j]=-C1[0,j]/a00
C1red=sp.simplify(L1*C1*R1); S1=sp.simplify(C1red[1:,1:])  # Schur(C1) 2x2
C2t = sp.simplify(R1.inv()*C2)   # R1^{-1} C2
# clear top row of the chain L1·P via R2 (done before). The reduced C2' = the 1: block of C2t after its
# own top-row clear. C2t block: [c00 c0*; c*0 C2sub]. 
c00 = C2t[0,0]
R2c = sp.eye(3)
for j in range(1,3): R2c[0,j] = -C2t[0,j]/c00
C2red = sp.simplify(C2t*R2c)  # top row cleared
C2prime = sp.simplify(C2red[1:,1:])  # 2x2 reduced C2'
# Now: is Schur(P) = S1 · C2prime?  (the reduced chain product)
test = sp.simplify(S1 * C2prime - SchurP)
print("\nCRUX (a): Schur(P) == S1·C2' (reduced chain product)?  diff =", test)
