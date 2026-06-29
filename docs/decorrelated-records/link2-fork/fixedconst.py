import sympy as sp
print("="*78)
print("FIXED-CONSTANT comparability: is |ΔR| <= c*sqrt(Φ) for a FIXED c (not ->0)?")
print("  If yes, rlctAtOn_squeeze holds with c1=(1-c)², c2=(1+c)² -- NOT 1/2,3/2.")
print("="*78)
u,v,w,p,q,x,T0,T1 = sp.symbols('u v w p q x T0 T1', real=True)
Zbar0, Ybar_last = sp.symbols('Zbar0 Ybar_last', real=True)
A0=sp.Matrix([[1+u, p],[w, T0]]); A1=sp.Matrix([[1+x, v],[q, T1]])
P=sp.expand(A0*A1); R=[P[0,0]-1, P[0,1], P[1,0]]
delta0=-Zbar0*p/(1+u); delta1=-Ybar_last*q/(1+x)
Rth=[e.subs({T0:T0+delta0,T1:T1+delta1}) for e in R]
dR=[sp.simplify(rt-r) for rt,r in zip(Rth,R)]
print("ΔR_12 = -Ybar_last p q/(1+x),   ΔR_21 = -Zbar0 p q/(1+u),   ΔR_11=0.")
print()
# The exact identity (verified earlier): ΔR_12 = -(p q)/((1+x)(1+u)) ... no, recompute the clean form.
# ΔR_12 = Y0 * delta1 = p * (-Ybar_last q/(1+x)) = -Ybar_last p q/(1+x).
# Express via R': R'_21 = P21 = w(1+x) + q T0 ... and R'_11 = P11-1 = (1+u)(1+x)+pq-1 = u+x+ux+pq.
# Note p*q = R'_11 - (u + x + u x).  So ΔR_12 = -Ybar_last (R'_11 - u - x - ux)/(1+x).
# |ΔR_12| <= |Ybar_last|/(1-δ) * (|R'_11| + |u|+|x|+|ux|).  |R'_11| <= sqrt(Φ).  |u|,|x| are coords <= δ.
# So |ΔR_12| <= |Ybar_last|/(1-δ) (sqrt(Φ) + 3δ).  Near 0 this is ~ |Ybar_last| sqrt(Φ) + small.
# => |ΔR_12| <= (|Ybar_last|+o(1)) sqrt(Φ) + O(δ).  The O(δ) term: is it <= sqrt(Φ)?  δ ~ coords;
# sqrt(Φ) >= |R'_11| but R'_11 can be 0 while δ != 0 (e.g. u=x=pq=0 but... then δ from u,x =0 too).
# Cleanest: bound ΔR by R' DIRECTLY. ΔR_12 = -Ybar_last p q/(1+x). And R'_11 = u+x+ux+pq contains pq.
# Also R'_12 = P12 = (1+u)v + p T1 ; R'_21 = P21 = w(1+x) + q T0.
# The product p*q: p appears in R'_11 (as pq) and R'_12 (as p T1); q in R'_11 (pq) and R'_21 (q T0).
# Hmm p,q individually are NOT linearly in R' (only the PRODUCT pq is, via R'_11).
# So |p q| <= |R'_11| + |u+x+ux| <= sqrt(Φ) + (|u|+|x|+|ux|).
# The residual |u|,|x|: u=X_first (REG), x=X_last (SPEC).  u appears in R'_11 linearly (coeff 1+x).
#   x appears in R'_11 linearly too.  So |u|,|x| <~ sqrt(Φ)?  NO -- u,x appear as u+x+ux+pq TOGETHER;
#   can't separate u from x from pq by one equation R'_11.  Need more residual components.
print("Bounding |p q|:  p q = R'_11 - (u + x + u x).  Need |u|,|x| bounded by sqrt(Φ).")
print("  u = X_first (REG): PIN-1 says ∑R'² >= c‖reg‖² => |u| <= c^{-1/2} sqrt(Φ).  GOOD (u is reg).")
print("  x = X_last (SPEC): is |x| <= C0 sqrt(Φ)?  x appears in R'_11 = u+x+ux+pq linearly.")
print("    On ray u=pq=0: R'_11 = x(1+0)=x => |x| = |R'_11| <= sqrt(Φ).  But on ray with cancellation")
print("    u+x+ux+pq=0 (x = -(u+pq)/(1+u)), R'_11=0 yet x != 0 => |x| NOT bounded by R'_11 alone.")
print("    Need ANOTHER residual reading x.  R'_12=(1+u)v+pT1, R'_21=w(1+x)+qT0: x appears in R'_21")
print("    as w*x -- but multiplied by w (reg, ->0).  So x is WEAKLY read.  x = X_last is SPECTATOR.")
print()
print("CONCLUSION: x = X_last is a SPECTATOR direction (gauge), NOT dominated by ∑R'².  On the")
print("locus {R'=0} (the singular fibre), x can be free.  So |p q| is NOT bounded by sqrt(Φ)")
print("uniformly => the fixed-constant bound |ΔR| <= c sqrt(Φ) is NOT obvious either.")
print()
print("MUST re-examine on the FULL {R'=0} locus: there ΔR must ALSO vanish (else F != Φ where Φ's")
print("reg-energy part is 0 but C survives).  Check ΔR on {R'=0}.")
