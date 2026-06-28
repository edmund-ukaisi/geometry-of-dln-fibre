# genm-l2fin (2026-06-28): sub-3 framed-{12} move-invariance KILL-CONDITION witness.
#
# deepestEFull (DeepestGaugeConstruction:419) reads the FRAMED product
# `framedParamsPivot J Pf Qf q` reg blocks {11,12,21}.  The joint move psiSplitRawL2Core edits the
# last-layer reads Y->Y1', T->T1' with Y1' = Y1 + A0^{-1} Y0 (T1 - T1'), A0 = 1 + readX_0 (RAW).
# e2_regPreserve kills the RAW combination A0*ΔY + Y0*ΔT.  But the framed top row carries
# p11 := reindex(endpointP0).toBlocks₁₁ = invOf A11 (blockLower_left_normalizer), NOT 1.
#
# RESULT: framed {11},{21} are move-invariant under ANY block-triangular frame, but framed {12} =
# (1 - p11)*ΔY*d'  (d' := reindex(endpointQL).toBlocks₂₂), which is 0 IFF the frame is UNIPOTENT
# (p11 = 1 AND d' = 1).  hPtri/hQtri give only block-TRIANGULARITY; the producer's B-normalizing frame
# is NOT unipotent (p11 = invOf A11).  So the agreement lemma as stated is FALSE; sub-3's geometric core
# needs a STRONGER (unipotent-frame) hypothesis — a controller/expedition decision.
import numpy as np
np.random.seed(1)
r = m1 = m2 = 1  # all blocks 1x1

X0, Y0, Z0, T0 = (np.random.randn(1, 1) for _ in range(4))   # raw layer-0 blocks
X1, Z1, Y1, T1 = (np.random.randn(1, 1) for _ in range(4))   # raw layer-1 blocks
A0 = np.eye(r) + X0
T1p = np.random.randn(1, 1)
Y1p = Y1 + np.linalg.inv(A0) @ Y0 @ (T1 - T1p)               # the move's Y1'


def full(p11, dpr, Yv, Tv):
    p21 = np.random.randn(m1, r); d11 = np.random.randn(r, r); d12 = np.random.randn(r, m2)
    corner = np.block([[np.eye(r), np.zeros((r, m1))], [np.zeros((m1, r)), np.zeros((m1, m1))]])
    Pf = np.block([[np.array([[p11]]), np.zeros((r, m1))], [p21, np.eye(m1)]])    # block-LOWER, Qf0=1
    L0 = corner + Pf @ np.block([[X0, Y0], [Z0, T0]])
    Qf = np.block([[d11, d12], [np.zeros((m2, r)), np.array([[dpr]])]])           # block-UPPER, Pf1=1
    L1 = corner + np.block([[X1, Yv], [Z1, Tv]]) @ Qf
    return L0 @ L1


for (p11, dpr, label) in [(2.5, 1.7, "non-unipotent (p11=2.5, d'=1.7)"),
                          (1.0, 1.0, "unipotent     (p11=1,   d'=1)  ")]:
    np.random.seed(7); Po = full(p11, dpr, Y1, T1)            # fix p21/d11/d12 across both move evals
    np.random.seed(7); Pm = full(p11, dpr, Y1p, T1p)
    D = Pm - Po
    print(f"{label}: {{11}}={abs(D[:r,:r]).max():.3g}  "
          f"{{12}}={abs(D[:r,r:]).max():.3g}  {{21}}={abs(D[r:,:r]).max():.3g}")
# Expected: non-unipotent -> {12} != 0 (leak);  unipotent -> all 0.

# ---------------------------------------------------------------------------------------------------
# The CONSTRUCTIVE resolution: a FRAME-AWARE Y1' exists that preserves the FRAMED reg energy at a
# generic non-unipotent frame.  P01 (framed {12}) is AFFINE in the raw Y1, so for any T1' we can solve
# Y1' making the framed P01 invariant -> the bridge is salvageable by re-pointing the move's Y1' to the
# FRAMED A0 (resolution #1).  Verified: framed reg energy unchanged.
def L0f(p11, p21, X, Y, Z, T):
    c = np.block([[np.eye(r), 0 * Y], [0 * Z, 0 * T]]); Pf = np.block([[np.array([[p11]]), 0 * Y], [p21, np.eye(m1)]])
    return c + Pf @ np.block([[X, Y], [Z, T]])
def L1f(d11, d12, dpr, X, Y, Z, T):
    c = np.block([[np.eye(r), 0 * Y], [0 * Z, 0 * T]]); Qf = np.block([[d11, d12], [0 * Z, np.array([[dpr]])]])
    return c + np.block([[X, Y], [Z, T]]) @ Qf
np.random.seed(3)
p21 = np.random.randn(1, 1); d11 = np.random.randn(1, 1); d12 = np.random.randn(1, 1)
p11v, dprv = 2.5, 1.7
L0 = L0f(p11v, p21, X0, Y0, Z0, T0)
def reg_energy(L1):
    P = L0 @ L1
    return ((P[:r, :r] - np.eye(r)) ** 2).sum() + (P[:r, r:] ** 2).sum() + (P[r:, :r] ** 2).sum()
def P01(Yraw, Traw): return (L0 @ L1f(d11, d12, dprv, X1, Yraw, Z1, Traw))[:r, r:]
target = P01(Y1, T1)
b = P01(np.ones((1, 1)), T1p) - P01(np.zeros((1, 1)), T1p)   # P01 affine in Yraw
a = P01(np.zeros((1, 1)), T1p)
Y1p_fa = (target - a) / b
print("frame-aware Y1' (resolution #1): reg energy orig "
      f"{reg_energy(L1f(d11, d12, dprv, X1, Y1, Z1, T1)):.5f}  moved "
      f"{reg_energy(L1f(d11, d12, dprv, X1, Y1p_fa, Z1, T1p)):.5f}  (equal => bridge salvageable)")
