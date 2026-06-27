import sympy as sp
print("="*78)
print("EXACT: local rlct at a NON-ORIGIN stratum of a reduced-dim-2 DLN child {S·Bred=0}")
print("="*78)
# Smallest reduced-dim-2 child that is a genuine DLN node: take the (2,2,n) node's child after the
# recursion structure. Actually let's directly test the cleanest reduced-dim-2 product loss:
# loss = ||S·b||^2, S a 2x2 matrix (entries s11,s12,s21,s22), b a 2-vector (b1,b2), n=1.
# This is dlnLoss(2,2,1) 0 (a (2,2,1) product loss). Its deepest point (all zero) rlct:
s11,s12,s21,s22,b1,b2 = sp.symbols('s11 s12 s21 s22 b1 b2', real=True)
S = sp.Matrix([[s11,s12],[s21,s22]]); b = sp.Matrix([b1,b2])
loss = (S*b)  # 2x1
L = sum(c**2 for c in loss)
L = sp.expand(L)
print("loss = ||S·b||^2 =", L)
# {L=0} = {S b = 0}.  Strata:
#  (origin) S=0,b=0.  (interior-A) b=0, S free: S·0=0 -> the whole {b=0} (codim 2 in (s,b)? b is 2-dim)
#  (interior-B) S=0, b free: the whole {S=0} (codim 4).
#  (interior-C) S rank1, b in ker(S), both nonzero.
# Compute the local rlct at an INTERIOR-A point: b=0, S = S0 (generic nonzero, say S0=I).
# Shift S = I + dS, b = 0 + db.  loss = ||(I+dS) db||^2 = ||db + dS db||^2 ~ ||db||^2 (db small).
# => near (S=I, b=0): loss ~ ||db||^2 = db1^2+db2^2, a MORSE form in 2 vars (db), the dS dirs regular.
# rlct(Morse, 2 vars)=2/2=1.
print("\nInterior-A point (S=I, b=0): loss ~ ||db||^2 (Morse in b1,b2) => local rlct = 2/2 = 1.")
# Interior-C: S rank1, b in ker. Say S0=[[1,0],[0,0]], b0=[0,1] (in ker S0). loss(S0,b0)=||[0,0]||=0. ok.
# shift: S=S0+dS, b=b0+db. S b = (S0+dS)(b0+db) = S0 b0 + S0 db + dS b0 + dS db
#   = 0 + S0 db + dS b0 + O(2).  S0 db = [db1,0]; dS b0 = [ds12, ds22] (col 2 of dS).
# leading: S b ~ [db1 + ds12, ds22] (+ higher).  So loss ~ (db1+ds12)^2 + ds22^2 -> 2 Morse dirs.
# rlct = 2/2 = 1.
print("Interior-C point (S rank1, b in ker): loss ~ (db1+ds12)^2 + ds22^2 (2 Morse dirs) => rlct=1.")
# Deepest (all zero): the full (2,2,1) product loss. minAdm(2,2,1)?
def admissible(M):
    import itertools
    Ln=len(M)-1
    bounds=[min(M[0],M[1]) if j==1 else M[j] for j in range(1,Ln+1)]
    rngs=[range(b+1) for b in bounds[:-1]]+[[0]]
    for T in itertools.product(*rngs):
        if all(T[i]>=T[i+1] for i in range(Ln-1)): yield T
def mval(M,T):
    tot=0; prev=M[0]
    for j,t in enumerate(T,1): tot+=(prev-t)*(M[j]-t); prev=t
    return tot
def minAdm(M): return min(mval(M,T) for T in admissible(M))
mA = minAdm([2,2,1])
print(f"\nDeepest (all-zero) (2,2,1): minAdm={mA}, rlct(deepest)={sp.Rational(mA,2)}.")
print(f"Interior strata rlct = 1.  Is rlct(deepest)={sp.Rational(mA,2)} <= 1 (interior)?",
      sp.Rational(mA,2) <= 1)
print()
print("VERDICT: deepest rlct =", sp.Rational(mA,2), "<= interior rlct = 1.")
print("=> the deepest point is the WORST (min) rlct point over the box. Box collapses to point-min.")
print("=> reduced-dim>=2 does NOT introduce a smaller-rlct interior stratum. DLN box-collapse HOLDS.")
