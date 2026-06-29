import sympy as sp
# Settle: within the chart, does the chaining at boundary k use N_k, and does the Schur frame at boundary k
# also use N_k? If YES (same N_k in both schur_k's KN block AND chain_k's shear), they share the slot.
# Chart: C_k = Bmat_k chainQ(N_k) + u Rmat_k.  chainQ(N_k)=[I|N_k] so C_k = [K_k | K_k N_k]+...(the KN block uses N_k).
#   A_k = [C_{k+1} - N_k W_k ; W_k].  So A_k uses N_k in the chaining (C_{k+1}-N_k W_k).
# So N_k appears in: (1) C_k's KN block (the Schur frame of boundary k), AND (2) A_k's chaining (- N_k W_k).
# BUT note: C_k feeds A_{k-1} (the PREVIOUS layer's kept rows: A_{k-1}=[C_k - N_{k-1}W_{k-1}; W_{k-1}]).
#   And A_k's chaining uses C_{k+1} (the NEXT boundary's frame) and N_k.
# So at the LAYER level, N_k is shared between schur (building C_k's KN) and chain (A_k's -N_k W_k).
# => schur_k and chain_k DO share N_k. Codex is RIGHT: chain_k must read raw N_k; if schur_k's map 
#    overwrites the N-slot with K_k N_k, chain must precede schur in the de-radialized B's factor order.
# Let me CONFIRM the |det| is order-independent regardless (the deliverable), and the map-order is [schur,chain,ldu].
x = sp.symbols('x0:27', real=True); u=x[0]
# Verify N1 (x7,x8) appears in BOTH the KN-block of C1 and the chaining -N1 W1 of A1.
B1=sp.Matrix([[x[1],x[1]*x[2]],[x[1]*x[3],x[1]*x[2]*x[3]+x[4]],[x[1]*x[3]*x[6]+x[1]*x[5],x[1]*x[2]*x[5]+x[6]*(x[1]*x[2]*x[3]+x[4])]])
N1=sp.Matrix([[x[7]],[x[8]]]);W1=sp.Matrix([[x[15],x[16],x[17]]])
qN1=sp.Matrix.hstack(sp.eye(2),N1)
C1=B1*qN1  # the Schur frame; its last col is the KN block, uses x7,x8
print("C1 (Schur frame) uses N1 coords x7,x8?", (x[7] in C1.free_symbols) or (x[8] in C1.free_symbols))
# chaining at boundary 1: -N1*W1 (part of A1 kept rows)
chain1 = N1*W1
print("chain1 = N1*W1 uses N1 coords x7,x8?", (x[7] in chain1.free_symbols))
print()
print("CONFIRMED: N_k is SHARED between schur_k (KN block) and chain_k (the -N_k W_k shear).")
print("=> Codex's ordering is correct: within boundary k, evaluate chain_k BEFORE schur_k (so chain reads raw N_k).")
print("   composeFold list (outermost first): [schur_s, chain_s, ldu_s] per boundary => eval ldu->chain->schur.")
print("   For the DET: |det| product COMMUTES, so the engine product is order-independent (deliverable safe).")
print("   For the MAP IDENTITY: the [schur,chain,ldu] order is the faithful one.")
