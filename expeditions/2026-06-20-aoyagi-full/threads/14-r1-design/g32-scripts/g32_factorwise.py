import sympy as sp
"""
Verify the FACTOR-WISE chain form (the spec's ∏(Q^s C^s Q^{s+1}) = blockdiag[E_t, ∏C']) and the (3,2,3) case.
Factor-wise: Q0 C1 Q1 and Q1^{-1} C2 Q2 each block-structure, product block-diagonalizes, residual = C1'·C2'.
The inner Q1 (and Q1^{-1}) must be the SAME unimodular — it threads C1's right-reduction into C2's left.
"""
def test_chain(m0,m1,m2,label):
    print(f"\n=== {label}: chain C1({m0}x{m1})·C2({m1}x{m2}), pivot peels δ=1 (reduce to ({m0-1}x{m1-1})·({m1-1}x{m2-1})) ===")
    C1 = sp.Matrix(m0,m1, lambda i,j: sp.Symbol(f'a{i}{j}', real=True))
    C2 = sp.Matrix(m1,m2, lambda i,j: sp.Symbol(f'b{i}{j}', real=True))
    P = C1*C2
    # Factor-wise pivot: pivot C1[0,0]=unit. L0 (m0xm0) clears C1 col0; R1 (m1xm1) clears C1 row0.
    a00 = C1[0,0]
    L0 = sp.eye(m0)
    for i in range(1,m0): L0[i,0] = -C1[i,0]/a00
    R1 = sp.eye(m1)
    for j in range(1,m1): R1[0,j] = -C1[0,j]/a00
    C1t = sp.simplify(L0*C1*R1)   # blockdiag[a00, S1], S1 = (m0-1)x(m1-1)
    # row0/col0 of C1t should be cleared:
    r0 = [sp.simplify(C1t[0,j]) for j in range(m1)]; c0 = [sp.simplify(C1t[i,0]) for i in range(m0)]
    print(f"  C1t=L0·C1·R1 cleared? row0={r0}  col0={c0}")
    S1 = sp.simplify(C1t[1:,1:])   # (m0-1)x(m1-1)
    # Thread Q1 = R1 to C2's left: C2t = R1^{-1} C2. Then reduce C2t top row via R2 (m2xm2).
    C2t = sp.simplify(R1.inv()*C2)
    c2_00 = C2t[0,0]
    R2 = sp.eye(m2)
    for j in range(1,m2): R2[0,j] = -C2t[0,j]/c2_00
    C2red = sp.simplify(C2t*R2)
    # We also need C2red's col0 (below pivot) to be irrelevant to the core block — but the chain product is
    # C1t·C2t = L0·P, and the core is the (1:,1:) block. The reduced chain C2' = C2red[1:,1:]? Let me check
    # the chain block-diag: chain = C1t·C2t, then ·R2 on the right.
    chain = sp.simplify(C1t*C2t*R2)   # = L0·P·R2
    cr0 = [sp.simplify(chain[0,j]) for j in range(m2)]; cc0 = [sp.simplify(chain[i,0]) for i in range(m0)]
    print(f"  chain=L0·P·R2: row0={cr0}")
    # The CRUX: core = chain[1:,1:] should = S1 · C2'block. What's the right C2'? 
    # chain[1:,1:] = (C1t·C2t·R2)[1:,1:]. Since C1t=blockdiag[a00,S1], C1t·X picks the lower block:
    # (C1t·C2t·R2)[1:,:] = S1·(C2t·R2)[1:,:] (lower rows). So core = S1·(C2t·R2)[1:,1:].
    C2prime = sp.simplify((C2t*R2)[1:,1:])  # (m1-1)x(m2-1)
    core = sp.simplify(chain[1:,1:])
    # factorization test:
    fact = sp.simplify(core - S1*C2prime)
    print(f"  CRUX: core == S1·C2'  ?  diff = {fact}")
    # also: core == Schur(P)?
    p00=P[0,0]; SchurP = sp.simplify(P[1:,1:] - P[1:,0]*P[0,1:]/p00)
    print(f"  core == Schur(P) ?  diff = {sp.simplify(core - SchurP)}")
    # dims of reduced chain:
    print(f"  reduced chain dims: C1' = {S1.shape}, C2' = {C2prime.shape}  ⟹ ({m0-1},{m1-1},{m2-1}) ✓")
    return fact == sp.zeros(*core.shape)

ok1 = test_chain(3,3,3, "(3,3,3) r=1")
ok2 = test_chain(3,2,3, "(3,2,3) r=1 [non-square middle]")
ok3 = test_chain(4,3,2, "(4,3,2) r=1 [strictly decreasing]")
print(f"\nALL factor-wise factorizations exact: {ok1 and ok2 and ok3}")
