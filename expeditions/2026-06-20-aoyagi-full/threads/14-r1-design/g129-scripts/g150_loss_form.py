import sympy as sp
# THE LOSS-FORM germ (sub-lemma 4): near the deepest point w0, is dlnLoss H B ∘ chart =ᶠ[𝓝 0]
# ∑reg² + dlnLoss M 0 (reduced)? The deepest point: B=0 (core), all regular blocks = 0 at w0.
# CRUX: the reduced block (1,1) = Z1 Y2 + T1 T2 has a CROSS term Z1·Y2 (regular×regular). Does it spoil
# the clean ∑reg² + ‖∏T‖²?  At the deepest point Z=Y=0, so Z1 Y2 vanishes to ORDER 2 (product of two
# regular coords). The loss ‖product blocks‖² — let me see if the germ separates.
r,m,n = 1,2,2
def blk(pref):
    X=sp.Matrix(r,r,sp.symbols(f'{pref}X0:{r*r}')); Y=sp.Matrix(r,n-r,sp.symbols(f'{pref}Y0:{r*(n-r)}'))
    Z=sp.Matrix(m-r,r,sp.symbols(f'{pref}Z0:{(m-r)*r}')); T=sp.Matrix(m-r,n-r,sp.symbols(f'{pref}T0:{(m-r)*(n-r)}'))
    return X,Y,Z,T
X1,Y1,Z1,T1=blk('a'); X2,Y2,Z2,T2=blk('b')
Ir=sp.eye(r)
C1=sp.Matrix(sp.BlockMatrix([[Ir+X1,Y1],[Z1,T1]])); C2=sp.Matrix(sp.BlockMatrix([[Ir+X2,Y2],[Z2,T2]]))
P=sp.expand(C1*C2)
# loss at the core B=0: ‖P‖² = Σ all entries². The "regular" generators are the (0,0),(0,1),(1,0) blocks
# (each = I_r + first-order regular, or first-order regular); the reduced is (1,1)=Z1Y2+T1T2.
# But B=0 means we want ‖P‖²... NO: at the deepest point the PRODUCT = B. For the CORE (the reduced
# widths M=H-r), B is the rank-r target and the deepest product has rank r. The regular block (0,0)→I_r
# (the rank-r part of B); the loss measures deviation. Let me model the loss as the deviation of the
# product from its deepest value: regular blocks → their B-values (I_r-ish), reduced block → 0.
# So the LOSS = ‖(0,0)-I_r‖² + ‖(0,1)‖² + ‖(1,0)‖² + ‖(1,1)‖²  (deviation from deepest product blockdiag[I_r,0]).
def fro2(*Ms): return sum(sum(M[i,j]**2 for i in range(M.rows) for j in range(M.cols)) for M in Ms)
reg00 = sp.expand(P[0:r,0:r] - Ir)
reg01 = sp.expand(P[0:r,r:]); reg10 = sp.expand(P[r:,0:r]); red11 = sp.expand(P[r:,r:])
loss = sp.expand(fro2(reg00,reg01,reg10,red11))
print("=== Loss = ‖(0,0)-I‖²+‖(0,1)‖²+‖(1,0)‖²+‖(1,1)‖² (deviation from deepest blockdiag[I_r,0]) ===")
print("reg00 =", reg00.tolist(), "  reg01 =", reg01.tolist(), "  reg10 =", reg10.tolist())
print("red11 (reduced block) =", red11.tolist())
print()
# Is the reduced block's CROSS term Z1 Y2 higher-order? At w0 all regular = 0. The reduced core dlnLoss M 0
# on the reduced widths M=(m-r) = the ‖T1 T2‖² chain. So red11 = T1 T2 + Z1 Y2; the Z1 Y2 is regular×regular
# (order 2 in regular coords). Check: red11 - T1 T2 = Z1 Y2 ∈ ideal(regular coords)?
TT = sp.expand(T1*T2)
cross = sp.expand(red11 - TT)
print("red11 - T1·T2 =", cross.tolist(), " (= Z1·Y2, the regular×regular cross term)")
# On the regular-zero locus {reg=0} i.e. {Z1=Y1=X1=Z2=Y2=X2=0}: red11 → T1 T2 (the reduced chain). ✓
subreg0 = {s:0 for s in (list(X1)+list(Y1)+list(Z1)+list(X2)+list(Y2)+list(Z2))}
print("red11 |{reg=0} =", sp.expand(red11.subs(subreg0)).tolist(), " = T1·T2 (the reduced dlnLoss M 0). ✓")
print()
print("⟹ loss-form germ: loss = ∑(reg residuals)² + ‖red11‖², and red11 = ‖T1 T2‖² + (cross ∈ ideal(reg)).")
print("Near w0 (reg→0), loss germ = ∑reg² + ‖T1 T2‖² = ∑reg² + dlnLoss M 0 (T-blocks). The cross Z1 Y2 is")
print("order-2 in reg, ABSORBED into the smooth-block ∑reg² (a bounded perturbation of the regular squares),")
print("NOT into the reduced core — so the SPLIT is clean at the germ level.")
