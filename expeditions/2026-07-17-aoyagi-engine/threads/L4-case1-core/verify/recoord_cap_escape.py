"""
DECISIVE TRACE (seat-L3T2 def-level finding): the faithful deeper recoord A_{S+1} -> A_{S+1}*Q1^{-1}
writes layer S+1 at col = pivot-ROW index (Fin d_{S+1}, the UNCAPPED raw remnant of the column-remnant
transpose). On a WIDE branch d_{S+1} > widthMinUpto(S) (whence widthMinUpto(S+1)=widthMinUpto(S) < d_{S+1})
that write can land OUTSIDE blockCoords(S+1) (which caps col < widthMinUpto(S+1)).

QUESTION: does foldResid(child) at a descent step genuinely DEPEND on the out-of-cap layer-(S+1)
coordinate, or does it cancel / never enter?

VERDICT (computed below): **OUT-OF-CAP — it PROPAGATES.**  Even though the wide layer-S remnant ROW clears
to zero, the row-op that clears it recoordinatizes the deeper factor's out-of-cap COLUMN into the in-cap
columns; the residual reads those in-cap columns, so it depends LINEARLY (support, not coefficient) on the
out-of-cap coordinate.  The carried support cap blockCoords(S+1) is FALSE on wide branches; the residual
support is the full layerCoords(S+1).

Smallest wide witness: d=(2,3,2,2) (the escape is at the layer-0 clear; (3,3,4) has NO recoord escape —
its d_2=4 is the ROW axis, not the recoord COL axis).  A_0=3x2, A_1=2x3 (COLS = Fin d_1 = 3), A_2=2x2;
coreGen = A_2 A_1 A_0.  widthMinUpto(1)=min(2,3)=2, so A_1 col 2 is OUT-OF-CAP.
"""
import sympy as sp

A0 = sp.Matrix(3, 2, sp.symbols('p0(0:3)(0:2)'))   # layer-0 block u_(0,row,col), row in Fin d_1=3
A1 = sp.Matrix(2, 3, sp.symbols('q1(0:2)(0:3)'))   # layer-1 u_(1,row,col), COL in Fin d_1=3 (recoord axis)
A2 = sp.Matrix(2, 2, sp.symbols('r2(0:2)(0:2)'))   # layer-2
outcap = [A1[r, 2] for r in range(2)]              # A_1 col 2 = OUT-OF-CAP (widthMinUpto(1)=2)

# --- the faithful clear of layer 0: canonical pivots (0,0) then (1,1) (the running-min corners),
#     each row-op recoordinatizes the deeper factor A_1 (A_1 -> A_1 * L^{-1}). ---
L0 = sp.eye(3)                                      # clear col 0 in rows 1,2 using pivot row 0
for i in (1, 2):
    L0[i, 0] = -A0[i, 0] / A0[0, 0]
A0a = sp.simplify(L0 * A0)
A1a = sp.simplify(A1 * L0.inv())                    # deeper recoord (Lean coreGen order)
L1 = sp.eye(3)                                      # clear col 1 in rows 0,2 using pivot row 1
for i in (0, 2):
    L1[i, 1] = -A0a[i, 1] / A0a[1, 1]
A0b = sp.simplify(L1 * A0a)
A1b = sp.simplify(A1a * L1.inv())

print("A_0 after clearing both running-min pivots (row 2 = the wide raw remnant, d_1=3 > wMU(0)=2):")
print("  row 2 of cleared A_0 =", [sp.simplify(A0b[2, j]) for j in range(2)], " (the remnant row clears to 0)")
print("\nRecoordinatized A_1'' column 0 (the IN-CAP col that the residual reads):")
col0 = [sp.simplify(A1b[r, 0]) for r in range(2)]
for r in range(2):
    print(f"  A_1''[{r},0] =", col0[r])
print("  => A_1''[:,0] = A_1[:,0] + w10*A_1[:,1] + w20*A_1[:,2]  — the OUT-OF-CAP col 2 is MIXED IN")
print("     (w20 = A_0[2,0]/A_0[0,0] = the wide remnant-row entry; clearing row 2 recoords col 2).")

# --- the residual foldResid(child) = A_2 * A_1'' * A_0''  — does it depend on the out-of-cap coords? ---
resid = sp.expand(A2 * A1b * A0b)
print("\nfoldResid(child) dependence on out-of-cap A_1 col-2 coords", [str(x) for x in outcap], ":")
allcoords = list(A0) + list(A1) + list(A2)
for i in range(2):
    for j in range(2):
        f = sp.expand(resid[i, j])
        dep = f.free_symbols & set(outcap)
        # is it LINEAR (support) — degree 1 in the out-of-cap coord?
        linear = all(sp.Poly(f, x).degree() == 1 for x in dep) if dep else False
        print(f"  resid[{i},{j}]: depends={bool(dep)}  linear-in-outcap(support, not coeff)={linear}")
# exhibit ONE surviving out-of-cap monomial (coefficient of q102 in resid[0,0])
q102 = A1[0, 2]
coeff = sp.simplify(sp.expand(resid[0, 0]).coeff(q102, 1))
print(f"\nSurviving out-of-cap SUPPORT monomial:  coeff of {q102} in resid[0,0] = {coeff}")
print("  (nonzero => the out-of-cap coord q102 is a genuine SUPPORT coordinate of foldResid(child)).")

print("\nVERDICT: OUT-OF-CAP. blockCoords(S+1) is FALSE as the residual support on wide branches;")
print("         the residual support is layerCoords(S+1). The recoord clearing the wide remnant row")
print("         injects the out-of-cap layer-(S+1) column into the in-cap columns the residual reads.")


# ============================================================================
# ROBUSTNESS: OUT-OF-CAP is INHERENT to the wide block (not a recoord artifact).
# ============================================================================
print("\n=== robustness: does the residual read out-of-cap col 2 WITHOUT the recoord? ===")
# Plain coreGen reads sum_k A_1[i,k]*A_0[k,j]; the k=2 term A_1[i,2]*A_0[2,j] reads the out-of-cap col 2
# via A_0's WIDE remnant row 2 (row >= widthMinUpto(0)=2). canonShearOf/N_p clears only widthMinUpto(0)=2
# pivots (rows 0,1), so A_0 row 2 col 0 = p020 stays LIVE and the col-2 read survives the clear.
c_inherent = sp.expand((A2 * A1 * A0)[0, 0]).coeff(A1[0, 2], 1)
print("  coeff of out-of-cap q102 in coreGen[0,0] =", c_inherent,
      "(via A_0 remnant row 2 col 0 = p020)")
print("  => the residual reads the deeper column paired with the wide layer-S remnant row REGARDLESS of")
print("     the recoord — the recoord (my main trace) relocates the same dependence into the in-cap col.")
print("     So OUT-OF-CAP is inherent to the wide block; blockCoords(S+1) is too small on wide branches.")
