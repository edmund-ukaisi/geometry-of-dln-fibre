import sympy as sp
"""
G3.2 first non-trivial recursion step — (3,3,3) r=1, L=2 chain.
Chain C = (C1, C2), C1: 3x3, C2: 3x3. Product P = C1·C2 (3x3). Target B (rank r=1 ⟹ the SINGULAR core
is B=0 on the reduced widths; here we test the recursion on the PRODUCT structure directly).

THE CLAIM (G3.2): in a pivot chart where the leading 1x1 minor of the partial product C1 is a UNIT,
there are unimodular Q^(0) (3x3), Q^(1) (3x3), Q^(2) (3x3) with
   (Q0 C1 Q1) · (Q1^{-1} C2 Q2)  =  blockdiag[ E_1 (regular), C1'·C2' ]
where C1', C2' are 2x2 (the reduced chain, widths 3-1=2), AND
   ‖C1·C2‖²  =  ‖regular part‖² + ‖C1'·C2'‖².

The SUBTLE part (the open crux): the Schur reduction of the PRODUCT must equal the product of the
Schur-reduced FACTORS — i.e. peeling rank-1 from the chain gives a smaller CHAIN, not just a smaller matrix.

Construction (the pivot chart): pivot at C1[0,0]=unit. The standard Schur/Gaussian step:
  Row-reduce C1: left-multiply by L1 = I - (col 0 below pivot)/pivot  to clear C1[1:,0].
  Col-reduce C1: right-multiply by R1 = I - (row 0 right of pivot)/pivot to clear C1[0,1:].
  ⟹ L1 C1 R1 = blockdiag[ C1[0,0], S1 ],  S1 = Schur complement = C1[1:,1:] - C1[1:,0] C1[0,0]^{-1} C1[0,1:].
Now the chain: (L1 C1 R1)(R1^{-1} C2 ...). For the PRODUCT to block-diagonalize, we need the
inner R1^{-1} on C2 to ALSO clear C2's top row coupling. Let me TEST whether one pivot chart
(unimodular Q's) achieves blockdiag of the PRODUCT, and whether the residual = reduced-chain product.
"""
sp.init_printing()
# Symbolic C1, C2 (3x3), generic
C1 = sp.Matrix(3,3, lambda i,j: sp.Symbol(f'a{i}{j}', real=True))
C2 = sp.Matrix(3,3, lambda i,j: sp.Symbol(f'b{i}{j}', real=True))
P = C1*C2

# Pivot at the PRODUCT P[0,0] (the leading 1x1 minor of the partial product). Assume P[0,0] unit.
# G3.2 acts on the PRODUCT: block-diagonalize P via Schur at P[0,0].
# L (clear P[1:,0]), R (clear P[0,1:]): L P R = blockdiag[P[0,0], Schur(P)].
p00 = P[0,0]
# Schur complement of P[0,0] in P:
P_11 = P[1:,1:]; P_10 = P[1:,0]; P_01 = P[0,1:]
SchurP = sp.simplify(P_11 - P_10 * (P_01) / p00)  # 2x2
print("Schur complement of the PRODUCT P at P[0,0] is 2x2. Shape:", SchurP.shape)

# THE CRUX: is Schur(P) = (reduced C1')·(reduced C2') for SOME reduced 2x2 chain?
# i.e. does the product's Schur complement FACTOR as a product of reduced factors?
# Aoyagi's claim: YES, via the SAME pivot applied factor-wise. Let me test the factor-wise reduction:
# Pivot C1 at C1[0,0] (assume unit): L1 C1 R1 = blockdiag[C1[0,0], S1], S1 = Schur(C1).
# Then C2 reduces by R1^{-1} ... the chain (L1 C1 R1)(R1^{-1} C2 Q2). For block-diag of the chain we need
# the (0, 1:) and (1:, 0) couplings of the chain to vanish. Let me COMPUTE the factor-wise reduced chain
# and compare its product to Schur(P).
a00 = C1[0,0]
L1 = sp.eye(3); 
for i in range(1,3): L1[i,0] = -C1[i,0]/a00
R1 = sp.eye(3)
for j in range(1,3): R1[0,j] = -C1[0,j]/a00
C1red = sp.simplify(L1*C1*R1)   # should be blockdiag[a00, S1]
print("L1 C1 R1 block-diag? top row/col after pivot (should be [a00,0,0] / [a00;0;0]):")
print("  row0:", [sp.simplify(C1red[0,j]) for j in range(3)])
print("  col0:", [sp.simplify(C1red[i,0]) for i in range(3)])
S1 = sp.simplify(C1red[1:,1:])  # Schur(C1), 2x2

# The chain after the C1 pivot: C1red · (R1^{-1} C2). The R1^{-1} threads to C2.
C2thread = sp.simplify(R1.inv() * C2)   # R1^{-1} C2 (3x3)
chain_after = sp.simplify(C1red * C2thread)  # = L1 C1 R1 R1^{-1} C2 = L1 (C1 C2) = L1 P
# block structure of chain_after:
print("\nchain_after = C1red·(R1^{-1}C2) = L1·P. Its [0,1:] coupling (need to clear via Q2 on the right):")
print("  row0[1:]:", [sp.simplify(chain_after[0,j]) for j in range(1,3)])
# Now clear the top row of chain_after with a right unimodular R2 (col ops on C2's right):
cf00 = chain_after[0,0]
R2 = sp.eye(3)
for j in range(1,3): R2[0,j] = -chain_after[0,j]/cf00
chain_final = sp.simplify(chain_after * R2)
print("\nchain_final = L1·P·R2. Block-diag?  row0:", [sp.simplify(chain_final[0,j]) for j in range(3)],
      " col0:", [sp.simplify(chain_final[i,0]) for i in range(3)])
core = sp.simplify(chain_final[1:,1:])  # the 2x2 residual core
# THE TEST: is core (the chain-reduced residual) = Schur(P)?
diff = sp.simplify(core - SchurP)
print("\nCORE (chain-reduced residual 2x2) == Schur(P)?  diff =", diff)
