import sympy as sp
from sympy import Rational as Q
from adv_dln import nReg, jacobian_rank_at_deepest, full_hessian_rank, build_chain_symbols, product, report

# ---------------------------------------------------------------------------
# Helper: build an "aligned identity-ish" deepest factorization for a chain H, rank r.
# Idea: C_k base = the (H_k x H_{k+1}) matrix with the top-left r x r block = I_r, else 0
#   ("rectangular identity"). The product of these is the (H_0 x H_L) rectangular identity of rank r.
#   This is a rank-r product that passes through EVERY layer at rank exactly min(r, H_k).
#   It is a valid deepest point for B = top-left r x r identity embedded in H0 x HL.
# ---------------------------------------------------------------------------
def rect_identity(rows, cols, r):
    M = sp.zeros(rows, cols)
    for i in range(min(r, rows, cols)):
        M[i, i] = 1
    return M

def aligned_base(H, r):
    L = len(H) - 1
    return [rect_identity(H[k], H[k+1], r) for k in range(L)]

def aligned_B(H, r):
    return rect_identity(H[0], H[-1], r)

# sanity: product of aligned_base == aligned_B
def check_aligned(H, r):
    base = aligned_base(H, r)
    P = base[0]
    for M in base[1:]:
        P = P * M
    return P == aligned_B(H, r), P

print("="*72)
print("BATCH 1 — replicate pp2's configs with my INDEPENDENT machinery (cross-check)")
print("="*72)
# pp2 used B=e0 e0^T and aligned factorization. With aligned (top-left I_r) base, same orbit.
for (H, r) in [((3,1,3),1),((1,1),1),((2,1,2),1),((2,2),2),((3,1,1,3),1)]:
    ok, P = check_aligned(H, r)
    assert ok, (H, r, P)
    report(f"[B1] aligned", H, r, aligned_base(H, r), aligned_B(H, r), check_full=True)
    print()

print("="*72)
print("BATCH 2 — PARTIAL DEGENERACY, r>=2 (flagged untested): interior width = r, others > r")
print("="*72)
# (4,2,3,2,4) r=2  -> M=(2,0,1,0,2): TWO interior bottlenecks at width 2=r, an interior width-3 layer between
report("[B2a] (4,2,3,2,4) r=2  M=(2,0,1,0,2)", (4,2,3,2,4), 2, aligned_base((4,2,3,2,4),2), aligned_B((4,2,3,2,4),2))
print()
# (3,2,3) r=2 -> M=(1,0,1): single interior bottleneck at width 2, ends width 3
report("[B2b] (3,2,3) r=2  M=(1,0,1)", (3,2,3), 2, aligned_base((3,2,3),2), aligned_B((3,2,3),2))
print()
# (4,2,4) r=2 -> M=(2,0,2)
report("[B2c] (4,2,4) r=2  M=(2,0,2)", (4,2,4), 2, aligned_base((4,2,4),2), aligned_B((4,2,4),2))
print()
# (5,3,2,4) r=2 -> only last-but interior width 2 = r; width 3 interior > r (PARTIAL)
report("[B2d] (5,3,2,4) r=2  M=(3,1,0,2)  PARTIAL: one bottleneck, one wide interior", (5,3,2,4), 2, aligned_base((5,3,2,4),2), aligned_B((5,3,2,4),2))
print()

print("="*72)
print("BATCH 3 — ASYMMETRIC / NON-MONOTONE (flagged)")
print("="*72)
report("[B3a] (4,2,3,2,4) r=2 (non-monotone valley)", (4,2,3,2,4), 2, aligned_base((4,2,3,2,4),2), aligned_B((4,2,3,2,4),2))
print()
report("[B3b] (3,1,2,1,3) r=1 (non-monotone, two bottlenecks, wide between)", (3,1,2,1,3), 1, aligned_base((3,1,2,1,3),1), aligned_B((3,1,2,1,3),1))
print()
report("[B3c] (5,1,3) r=1 asymmetric ends", (5,1,3), 1, aligned_base((5,1,3),1), aligned_B((5,1,3),1))
print()
report("[B3d] (2,1,5) r=1 asymmetric ends reversed", (2,1,5), 1, aligned_base((2,1,5),1), aligned_B((2,1,5),1))
print()
report("[B3e] (4,3,1,3,4) r=1 deep valley", (4,3,1,3,4), 1, aligned_base((4,3,1,3,4),1), aligned_B((4,3,1,3,4),1))
