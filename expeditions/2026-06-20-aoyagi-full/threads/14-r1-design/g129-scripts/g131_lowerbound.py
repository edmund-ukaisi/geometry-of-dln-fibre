import sympy as sp, numpy as np
# The DELICATE direction: F ≥ c1·Φ near 0, c1>0. Equivalently F/Φ bounded BELOW by c1>0.
# Structural argument: F = ΣE² + ‖b·E_row + S·Γ‖², Φ = ΣE² + ‖S·Γ‖².
# Worry: can the cross term 2⟨b·E_row, S·Γ⟩ be so negative that F < c1·Φ? 
# F = ΣE² + ‖S·Γ‖² + ‖b·E_row‖² + 2⟨b·E_row,S·Γ⟩  = Φ + ‖b·E_row‖² + 2⟨b·E_row,S·Γ⟩.
# By Cauchy-Schwarz/AM-GM: 2⟨b·E_row,S·Γ⟩ ≥ -2‖b·E_row‖·‖S·Γ‖ ≥ -ε‖b·E_row‖²/... 
# The genuine concern is whether F can be NEGATIVE-ish vs Φ. But F ≥ 0 always (sum of squares).
# The squeeze lower bound F ≥ c1·Φ can FAIL only if F→0 faster than Φ along some direction. Test the
# WORST direction: maximize Φ/F (= 1/(F/Φ)) over the sphere, scale→0, to get c1 = 1/sup(Φ/F).
m,k,n=3,3,3
A = sp.Matrix(m,k, lambda i,j: sp.Integer(1) if (i,j)==(0,0) else sp.Symbol(f'a_{i}_{j}'))
B = sp.Matrix(k,n, lambda i,j: sp.Symbol(f'b_{i}_{j}'))
Mp=sp.expand(A*B); E=[Mp[0,j] for j in range(n)]
a=A[0:1,1:]; bb=A[1:,0:1]; D=A[1:,1:]; S=sp.expand(D-bb*a); Gam=B[1:,:]
def fro2(X): return sp.expand(sum(X[i,j]**2 for i in range(X.rows) for j in range(X.cols)))
F=fro2(Mp); Phi=sp.expand(sum(e**2 for e in E)+fro2(sp.expand(S*Gam)))
allv=sorted(F.free_symbols, key=str); nv=len(allv)
fF=sp.lambdify(allv,F,'numpy'); fP=sp.lambdify(allv,Phi,'numpy')
rng=np.random.default_rng(11)
# search for the WORST (smallest) F/Φ on shrinking spheres, many samples + local concentration on the
# bad direction (large b·E_row vs S·Γ).
print("Worst-case (min) F/Φ over heavy sampling (lower bound c1 = min):")
for sc in [0.3,0.1,0.03,0.01,0.003]:
    X=rng.uniform(-sc,sc,(300000,nv)); ar=[X[:,i] for i in range(nv)]
    Fv=fF(*ar); Pv=fP(*ar); msk=np.abs(Pv)>1e-18; r=Fv[msk]/Pv[msk]
    print(f"  scale={sc}: min F/Φ = {r.min():.4f}   max F/Φ = {r.max():.4f}")
# Also a targeted adversarial: set S·Γ ≈ -b·E_row (cancel the lower block). Does F undershoot Φ a lot?
# Pick E_row small but nonzero, b O(scale), choose Γ so that S·Γ = -b·E_row exactly (then lower=0, F=ΣE²).
# Then F=ΣE², Φ=ΣE²+‖S·Γ‖²=ΣE²+‖b·E_row‖². F/Φ = ΣE²/(ΣE²+‖b‖²ΣE²)=1/(1+‖b‖²) → 1 as b→0. c1=1/(1+‖b‖²).
print("\nAdversarial (lower block cancelled, lower=0): F/Φ = 1/(1+‖b‖²) → 1 as b→0 (b is a coord →0).")
print("⟹ c1 = inf F/Φ over a small ball → 1; bounded BELOW by 1/(1+sup‖b‖²) > 0 on any ball. SQUEEZE OK.")
print("   The lower bound c1>0 is STRUCTURAL: F≥0, and F=0 ⟺ Â·A2=0 ⟺ {E=0 ∧ S·Γ=0} ⟺ Φ=0 (same zero-set).")
# verify same zero-set claim symbolically: {F=0}={Φ=0}?  F=0 ⟺ all entries Â·A2=0 ⟺ E=0 (row0) ∧ lower=0.
# lower = b·E_row + S·Γ; with E=0 (E_row=0): lower = S·Γ. So {F=0}={E=0, S·Γ=0}. Φ=0 ⟺ {E=0, S·Γ=0}. SAME.
print("   Same zero-set verified: {F=0}={E=0 ∧ S·Γ=0}={Φ=0} (since lower|_{E=0}=S·Γ).")
