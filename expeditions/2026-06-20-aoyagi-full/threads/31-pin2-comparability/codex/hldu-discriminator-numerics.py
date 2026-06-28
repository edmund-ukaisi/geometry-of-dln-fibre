# hLDUtie discriminator — the numerical falsification (genm-l2wire, 2026-06-28).
# Shows: LHS (bare 1+readX l2* dict) ≠ RHS (Score = framed/unframed Schur, A11+readX) at the boundary.
# r=1, H=[2,2,2] (scalars). deepest boundary leading block A11=3 (a unit ≠ 1) is the cause.
import numpy as np
X0,Y0,Z0,T0 = 0.2,0.3,0.5,0.7          # layer-0 deviation reads
X1,Y1,Z1,T1 = 0.11,0.13,0.17,0.19      # layer-1 deviation reads
A11,A21,B11,B12 = 3.0,0.9,2.0,0.6      # deepest boundary blocks (A11,B11 units ≠ 1)
def block(a,y,z,t): return np.array([[a,y],[z,t]],float)
def schur22(M): return M[1,1]-M[1,0]*(1/M[0,0])*M[0,1]   # (2,2)-Schur over the (1,1) block

# LHS = Schur(C0·C1), l2* dict C_s = [[1+X_s, Y_s],[Z_s, T_s]]  (prod_absorbed_eq_schur_ldu form)
C0=block(1+X0,Y0,Z0,T0); C1=block(1+X1,Y1,Z1,T1)
LHS = schur22(C0@C1)

# RHS = Score = Schur of the FRAMED product. dp0/dpL = reindexed deepest boundary layers (tail vanish);
# decode_s = dp_s + dev_s; P0/QL = block-lower/upper normalizers (identity (2,2)). Pivot M̂₁₁ (= Mw₁₁+1).
dp0=np.array([[A11,0],[A21,0]],float); dpL=np.array([[B11,B12],[0,0]],float)
decode0=dp0+block(X0,Y0,Z0,T0); decode1=dpL+block(X1,Y1,Z1,T1)
P0=np.array([[1/A11,0],[-A21/A11,1]],float); QL=np.array([[1/B11,-B12/B11],[0,1]],float)
RHS_framed   = schur22(P0@(decode0@decode1)@QL)     # = the Score integrand
RHS_unframed = schur22(decode0@decode1)             # schur_frame_transform (DP=DQ=1): frames vanish

print(f"LHS  (bare 1+readX dict)      = {LHS:.6f}")     # 0.094195
print(f"RHS  (framed Score Schur)     = {RHS_framed:.6f}")   # 0.074052
print(f"RHS  (unframed, frames gone)  = {RHS_unframed:.6f}") # 0.074052  (= framed: schur_frame_transform)
print(f"LHS == RHS ? {np.isclose(LHS, RHS_framed)}")   # False  ⟹ hLDUtie FALSE as stated
# Equal ONLY when deepest boundary = pure corM (A11=1,A21=0,B11=1,B12=0): then LHS=RHS.
