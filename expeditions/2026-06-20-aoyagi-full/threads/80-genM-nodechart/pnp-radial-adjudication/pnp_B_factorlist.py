import sympy as sp
# Understand B's factor structure at (3,3,3,3) by examining how B's outputs depend on the boundary roles.
# B (de-radialized): the SAME chain but C_L = Rfin (no u), C_k = Bmat*chainQ(N) + Rmat (no u), with
#   the bare-pivot anchor reading y_p. From RouteMFactorMaps, the per-boundary factor maps are:
#   - schurFrameMap: (X,K,N,E) -> (K, KN, XK, XKN+E)  [the Schur frame, E un-scaled]
#   - lduCoreMap: (l,q,u) -> the K-core matrix in LDU coords  [coordinatizes K = LDU]
#   - chainUnitCLM N: (W,C) -> (W, C - N W)  [the det-1 chaining shear]
# The CHART's per-boundary block C_k = Bmat_k chainQ(N_k) + Rmat_k = [[K,KN],[XK,XKN+E]] (Schur frame),
#   and A_k = chainA(N_k, W_k, C_{k+1}) = [C_{k+1} - N_k W_k ; W_k] (the chaining of the NEXT C).
# So per boundary the composition is: lduCore (coordinatize K) THEN schurFrame (build [[K,KN],[XK,XKN+E]])
#   THEN chainUnit (the chaining of C into the next layer's kept rows). Order within a boundary:
#   ldu (innermost, makes K) -> schur (frame) -> chain (lift into next).
# Across boundaries: boundary s feeds boundary s-1 (the chain goes deepest-first). 
# Let me VERIFY the engine-det PRODUCT structure: |det DB| should = prod over boundaries of
#   |det schur_s| * |det ldu_s| * |det chain_s| = prod_s |K_s|^{r_s+c_s} * prod_i|q_{s,i}|^{2(t-1-i)} * 1.
# This I already verified = y1^4 y4^2 y9^3 at 3333. Now map to per-boundary:
#   bd s=1: t=2,r=1,c=1: |K_1|^{r+c}=|detK_1|^2, ldu t=2: |q_{1,0}|^2 (q_{1,1} exp 0). detK_1 = y1*y4, q_{1,0}=y1.
#     => schur_1 contributes |y1 y4|^2 = y1^2 y4^2 ; ldu_1 contributes y1^2 ; chain_1 = 1. Total y1^4 y4^2.
#   bd s=2: t=1,r=1,c=2: |K_2|^{r+c}=|y9|^3 ; ldu t=1: q-prod=1 ; chain=1. Total y9^3.
# product = y1^4 y4^2 y9^3. MATCHES |det DB|. 
print("Per-boundary factor decomposition of |det DB| at (3,3,3,3):")
print("  bd s=1 (t=2,r=1,c=1): schur |detK_1|^2=|y1 y4|^2=y1^2 y4^2 ; ldu |q_{1,0}|^2=y1^2 ; chain=1  -> y1^4 y4^2")
print("  bd s=2 (t=1,r=1,c=2): schur |detK_2|^3=|y9|^3=y9^3 ; ldu=1 ; chain=1                        -> y9^3")
print("  product = y1^4 y4^2 y9^3  ==  |det DB|  ✓")
print()
print("So B = composeFold of, PER BOUNDARY s (deepest first), the triple [chain_s, schur_s, ldu_s]")
print("  (ldu innermost: coordinatize K; schur: build the frame [[K,KN],[XK,XKN+E]]; chain: lift into next layer).")
print("  identity boundary s=0 contributes NOTHING (Bmat=I, no E, no K-core, det 1).")
