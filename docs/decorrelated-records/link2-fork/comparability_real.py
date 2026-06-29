import sympy as sp
print("="*78)
print("THE REAL COMPARABILITY: track ΔR vs Φ=∑R'² + C carefully (all directions).")
print("="*78)
# Full (2,2,2) r=1.  Coordinates (after split): reg = (X_first=:u, Y_last=:v, Z_first=:w),
# spec = (Y_first=:p, Z_last=:q, X_last=:x  [and possibly more]), core = (T0, T1).
# Build the layers EXACTLY with these role-assignments:
#   A0 = [[1+u, p],[w, T0]]      (X_first=u reg, Y_first=p spec, Z_first=w reg, core T0)
#   A1 = [[1+x, v],[q, T1]]      (X_last=x spec, Y_last=v reg, Z_last=q spec, core T1)
u,v,w, p,q,x, T0,T1 = sp.symbols('u v w p q x T0 T1', real=True)
reg = [u,v,w]; spec=[p,q,x]; core=[T0,T1]
A0=sp.Matrix([[1+u, p],[w, T0]])
A1=sp.Matrix([[1+x, v],[q, T1]])
P=sp.expand(A0*A1)
R = [P[0,0]-1, P[0,1], P[1,0]]   # deepestEFull reads {11-1,12,21}
print("R' (deepestEFull reads):")
for nm,e in zip(["P11-1","P12","P21"], R): print(f"   {nm} =", sp.expand(e))
print()
# Θ: core shift by delta(reg,spec).  delta_s = Schur-correction difference.  Model the boundary
# Schur correction: layer cores get -Z(1+X)^-1 Y type.  For the DIFFERENCE (conj-bare), at the
# deepest boundary the leading delta is O(2) in (reg,spec); model delta0 = c0*(combo), delta1 = c1*(combo).
# Use the ACTUAL Schur form per layer: s_s = -Z_s (1+X_s)^{-1} Y_s.
# layer0: Z=w(reg), X=u(reg), Y=p(spec) => s0 = -w(1+u)^{-1} p.  layer1: Z=q(spec),X=x(spec),Y=v(reg)
#   => s1 = -q(1+x)^{-1} v.   The conj-bare DIFFERENCE delta has the SAME read structure (shifts in
#   the deepBlk bases, which are O(1)); model delta_s = s_s (the schur correction itself, leading).
delta0 = -w*(1+u)**(-1)*p     # carries reg(w) * spec(p)
delta1 = -q*(1+x)**(-1)*v     # carries spec(q) * reg(v)
# Θ shifts core: T0->T0+delta0, T1->T1+delta1.  R'(Θq) = R' with T0,T1 shifted.
Rth = [e.subs({T0:T0+delta0, T1:T1+delta1}) for e in R]
dR = [sp.expand(rt-r) for rt,r in zip(Rth,R)]
print("ΔR = R'(Θq) - R'(q):")
for nm,e in zip(["Δ11","Δ12","Δ21"], dR): print(f"   {nm} =", sp.simplify(e))
print()
print("KEY observation: track the leading (lowest-degree) terms of ΔR and whether ∑R'² dominates them.")
# ΔR_12 leading = Y0 * delta1 = p * (-q(1+x)^-1 v) = -p*q*v/(1+x).  degree 3 (p spec, q spec, v reg).
# ΔR_21 leading = Z1 * delta0 = q * (-w(1+u)^-1 p) = -q*w*p/(1+u).  degree 3.
# So ΔR ~ p*q*(reg or spec)  -- degree-3, carrying p*q (TWO spec factors) * one more.
# Does Φ=∑R'² dominate p*q*v ?  R' contains P12 = p*T1 + v*(1+u) +... wait recompute:
print("Recompute R' leading structure (which coords appear linearly in R'):")
for nm,e in zip(["P11-1","P12","P21"], R):
    lin = [g for g in (reg+spec+core) if sp.diff(e,g).subs({k:0 for k in reg+spec+core})!=0]
    print(f"   {nm}: linear coords =", lin)

print()
print("="*78)
print("THE ACTUAL MECHANISM (FIX 4): ΔR carries (spec·spec) coeff × a reg coord that R' dominates.")
print("="*78)
# ΔR_12 = -(p*q)/(x+1) * v ,  v=Y_last appears LINEARLY in P12 (R').  => |ΔR_12| <= |p*q|/(1-δ) |v|.
# R' >= |P12| component... but we need |v| <= C*sqrt(Φ).  v appears in P12 = T1*p + v(1+u) [+...].
# So v = (P12 - T1*p)/(1+u), i.e. |v| <= (|P12| + |T1||p|)/(1-δ) <= (sqrt(Φ) + |T1||p|)/(1-δ).
# Hmm: v is NOT directly bounded by sqrt(Φ) because P12 also contains T1*p (core*spec).
# BUT: |ΔR_12| = |p*q*v/(x+1)|.  Substitute v from P12:  v(1+u) = P12 - T1*p, so
#   ΔR_12 = -(p*q)/(x+1) * (P12 - T1 p)/(1+u) = -(p q)/((x+1)(u+1)) * (P12 - T1 p).
# => |ΔR_12| <= |p q|/((1-δ)^2) * (|P12| + |T1||p|).
#   |P12| <= sqrt(Φ).  |T1| <= sqrt(C) <= sqrt(Φ).  |p| <= δ (small spec).
#   => |ΔR_12| <= |p q|/((1-δ)^2) * (sqrt(Φ) + δ sqrt(Φ)) = |p q|(1+δ)/(1-δ)^2 * sqrt(Φ).
#   |p q| <= δ^2 -> 0.  => |ΔR_12| <= eps * sqrt(Φ), eps=O(δ^2) -> 0.  DOMINATION HOLDS.
print("Substitute v from R': v(1+u) = P12 - T1*p  =>")
print("  ΔR_12 = -(p q)/((x+1)(u+1)) * (P12 - T1 p).")
print("  |P12| <= sqrt(Φ);  |T1| <= sqrt(C) <= sqrt(Φ);  |p| <= δ (spec small).")
print("  => |ΔR_12| <= |p q|(1+δ)/(1-δ)^2 * sqrt(Φ),   |p q| <= δ^2 -> 0.")
print("  => |ΔR| <= eps*sqrt(Φ), eps=O(δ^2)->0.  ==> (1-eps')Φ <= F <= (1+eps')Φ.  COMPARABILITY HOLDS.")
print()
print("MECHANISM = FIX 4 (the JOINT one): ΔR's coefficient is a PRODUCT of TWO spec reads (p,q),")
print("each ->0; and ΔR's reg/residual factor (v, or P12-T1 p) is bounded by sqrt(Φ) via R' itself")
print("(the v=Y_last term in P12 + the C-domination of T1).  C ENTERS as an UPPER bound on |T1|")
print("(|T1|<=sqrt C<=sqrt Φ) -- so C IS used (unlike my earlier claim), but only as |T1|<=sqrt(Φ).")
print()
# Verify the substitution identity exactly:
lhs = dR[1]  # ΔR_12
P12sym = R[1]
rhs = -(p*q)/((x+1)*(u+1))*(P12sym - T1*p)
print("Verify ΔR_12 == -(p q)/((x+1)(u+1))*(P12 - T1 p):", sp.simplify(lhs - rhs)==0)
lhs2 = dR[2]
P21sym = R[2]
rhs2 = -(p*q)/((u+1)*(x+1))*(P21sym - T0*q)
print("Verify ΔR_21 == -(p q)/((u+1)(x+1))*(P21 - T0 q):", sp.simplify(lhs2 - rhs2)==0)
