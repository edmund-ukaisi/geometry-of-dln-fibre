import sympy as sp
# THE QUESTION: does the cascade/hnode resolve the FULL loss at a general optimal v (nonzero linear part),
# OR only the HOMOGENEOUS core (downstream of the split)?
#
# Setup: at an optimal v (C_L···C_1 = B, rank r), the loss F = ‖C_L···C_1 − B‖². Near v, write
# C_s = v_s + δ_s (perturbation). The product P = ∏(v_s + δ_s) = B + dP(δ) + (higher order).
# dP(δ) = Σ_s (downstream)·δ_s·(upstream) = the LINEAR part. F = ‖dP(δ) + O(δ²)‖².
# The linear part dP is NONZERO (generic v) — F has a regular (Morse) block in the dP-image directions.
#
# The CASCADE tuples C_s = diag(1^{t_{s+1}},0): these have product = diag(1^{t_L},0) = diag(1^0,0)=0
# (since t_L=0 on the core). So the cascade lives where the product = 0 — the CORE's deepest point,
# NOT a general optimal v (where product = B ≠ 0). Confirm:
def cascade_product(tt, W):
    import numpy as np
    L = len(tt)-1
    P = np.eye(W)
    for s in range(1, L+1):
        C = np.zeros((W,W))
        for i in range(tt[s]): C[i,i]=1.0
        P = P @ C
    return P
import numpy as np
tt = [3,3,3,2,2,2,0]; W=3
P = cascade_product(tt, W)
print(f"cascade product (t_L=0): \n{P}")
print(f"  ⟹ cascade product = 0 (the CORE deepest point), NOT a general optimal v (where product=B≠0). [FACT]")
print()
# So the cascade/hnode INPUT is the homogeneous core at its deepest point (product 0, no linear part).
# The L2-at-v split is UPSTREAM: it takes the full loss F=‖∏C−B‖² at optimal v (linear part ≠0) and
# peels the nReg regular directions, leaving the homogeneous core that the cascade/hnode then resolves.
print("STRUCTURAL CONCLUSION (the dependency):")
print("  L2-at-v split:  F=‖∏C−B‖² at optimal v (LINEAR part ≠0)  →  [reg quadratic, nReg] ⊞ [homog core]")
print("  R1 §4 hnode:    [homog core at deepest point (product 0, NO linear part)]  →  monomial resolution")
print("  The cascade/hnode INPUT = the homogeneous core. It does NOT see the linear part — that's peeled")
print("  by L2-at-v FIRST. So the split is LOGICALLY UPSTREAM of the resolution. [FACT from the inputs]")
print()
# Can the hnode peel the regular block as a byproduct? The hnode's Schur step assumes a HOMOGENEOUS node
# (G²=‖SΓ‖², no linear part). Applied to F WITH a linear part, the Schur step would need to handle the
# linear term — which is exactly the Morse/unit-pivot peel, NOT the hnode's homogeneous Schur. Verify:
print("Can the hnode peel the regular block? The hnode (schur_node_squeeze_unif) form is")
print("  flatCore = Σreg² + Σ(b·E+SΓ)², where Σreg² is ALREADY the regular block (assumed split off).")
print("  The hnode CONSUMES a form that already HAS the regular block separated (the Σreg² term). It does")
print("  NOT PRODUCE that separation from a loss with an unstructured linear part. The peeling of the")
print("  linear part into Σreg² is the L2-at-v Morse/unit-pivot step — UPSTREAM, a DIFFERENT mechanism. [INFERENCE, strong]")
