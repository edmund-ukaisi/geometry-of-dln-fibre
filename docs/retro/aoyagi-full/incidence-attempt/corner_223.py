"""
Exact verification of the binding corner M=(2,2,3), u=1, j=1 for the
integral-domination target (*_T1).  All exponent thresholds are exact rationals.

Objects (corner):
  chain widths (M0,M1,M2)=(2,2,3); peel outer layer A0 (2x2) at pivot rank u=1;
  a=M0-u=1, b=M1-u=1, ab/2 = 1/2.
  deep tail: A1 is 2x3, Z = I_3 (deepest, n=M2=3).
  hsQ = [Q_p ; Q_b], Q_p = 1x3 (pivot row), Q_b = A_cor (1x3).
  loss = ||A0 . A1||^2 = ||P Q_p + B12 Q_b||^2 + ||C Q_p + Gamma Q_b||^2   (M0 x n = 2x3)
  scalars p (unit ~1), beta=B12, c0=C, gam=Gamma.
  At corner z fixed so Q_p = e1 = (1,0,0); Q_b = (q1,t2,t3), incidence at t2=t3=0.
"""
import sympy as sp
from itertools import product

# ---------- 1. full (2,2,3) RLCT via Mval (codim) formula ----------
def Mval(Mw, t):
    # Mw = (M^1,...,M^{L+1}), t weakly decreasing length L, t[-1]=0
    L = len(Mw)-1
    val = (Mw[0]-t[0])*(Mw[1]-t[0])
    for j in range(2, L+1):
        val += (t[j-2]-t[j-1])*(Mw[j]-t[j-1])
    return val

def Mval_min(Mw):
    L=len(Mw)-1
    best=None; arg=None
    # t weakly decreasing, 0<=t_s<=min(M^1..M^{s+1}), t_L=0
    caps=[min(Mw[:s+2]) for s in range(L)]
    def rec(i,prev,cur):
        nonlocal best,arg
        if i==L:
            if cur[-1]!=0: return
            v=Mval(Mw,cur)
            if best is None or v<best: best=v; arg=tuple(cur)
            return
        hi = min(prev,caps[i])
        for ti in range(hi,-1,-1):
            rec(i+1,ti,cur+[ti])
    rec(0,max(Mw),[])
    return best,arg

Mw=(2,2,3)
mv,arg=Mval_min(Mw)
print("M=(2,2,3): Mval_min =",mv,"at t=",arg,"  RLCT T1 = 1/2 * Mval_min =",sp.Rational(mv,2))

# reduced chain redChain u=1 : (u, M2) = (1,3), a single 1x3 matrix
red=(1,3)
mvr,argr=Mval_min(red)
print("redChain 1 (2,2,3) = (1,3): Mval_min =",mvr,"  q_threshold = 1/2*that =",sp.Rational(mvr,2))
print("check additivity: ab + Mval_min(reduced) =",1*1,"+",mvr,"=",1*1+mvr," vs Mval_min(full)=",mv)

# ---------- 2. Newton-LP RLCT of a monomial sum-of-squares ----------
# lambda = min sum u_i  s.t. u>=0 and <u,alpha_k> >= 1/2 for each generator monomial alpha_k
from scipy.optimize import linprog
def newton_lp(gens, nvars, names=None):
    # minimize sum u_i  s.t.  <u,alpha_k> >= 1/2  (i.e. -<u,alpha_k> <= -1/2), u>=0
    c=[1.0]*nvars
    A_ub=[[-a[i] for i in range(nvars)] for a in gens]
    b_ub=[-0.5]*len(gens)
    res=linprog(c,A_ub=A_ub,b_ub=b_ub,bounds=[(0,None)]*nvars,method="highs")
    return res.fun, list(res.x)

# LHS integrand at incidence, EXPANDED AROUND THE WRONG (origin beta=0) point -- naive monomial read
# loss = x^2 + y^2 + (beta t2)^2+(beta t3)^2+(gamma t2)^2+(gamma t3)^2   (x=p+beta,y=c0+gam)
# vars order: x,y,beta,gamma,t2,t3
gens=[(1,0,0,0,0,0),(0,1,0,0,0,0),(0,0,1,0,1,0),(0,0,1,0,0,1),(0,0,0,1,1,0),(0,0,0,1,0,1)]
val,u=newton_lp(gens,6)
print("\nNaive monomial Newton-LP RLCT (origin expansion) =",val," (u=",u,")")

# ---------- 3. CORRECT local model: nondegenerate quadratic at the incidence locus ----------
# Near the true degenerate locus t2=t3=0, x=p+beta=0, y=c0+gam=0, with beta~-1,gamma~-c0 SPECTATORS:
#   loss ~ x^2 + y^2 + (beta^2+gamma^2)(t2^2+t3^2),  (beta^2+gamma^2) = K0 > 0 constant.
# => positive-definite quadratic in the 4 transverse coords (x,y,t2,t3).
# RLCT of int (pos-def quad in d vars)^{-c} = d/2.  Here d=4 => RLCT=2.
print("\nNondegenerate-quadratic model: 4 transverse dirs (x,y,t2,t3), RLCT = 4/2 =",sp.Rational(4,2))
print("  (beta,gamma are spectators: loss does NOT vanish along them at the locus)")

# ---------- 4. exact radial integral  int_0^delta r^{3-2c'} dr  ----------
r,cp=sp.symbols('r cprime',positive=True)
# converges near 0 iff exponent 3-2c' > -1  <=> c' < 2
print("\nRadial integral int_0^d r^(3-2c') dr converges iff 3-2c' > -1  <=>  c' <",sp.Rational(4,2))
for cc in [sp.Rational(3,2),sp.Rational(7,4),sp.Rational(2,1),sp.Rational(9,4)]:
    e=3-2*cc
    conv = (e> -1)
    print(f"   c'={cc}: exponent {e}  -> {'converges' if conv else 'DIVERGES'}")

# ---------- 5. RHS comparator: reduced 1x3 chain, ||Q_p||^2 with Q_p a 1x3 row ----------
# Q_p vanishes at 0 in R^3 -> ||Q_p||^2 = q1^2+q2^2+q3^2, RLCT 3/2; comparator exponent q=c'-ab/2=c'-1/2
# int_z (||Q_p||^2)^{-q} finite iff q < 3/2  <=> c'-1/2 < 3/2 <=> c' < 2 = T1
print("\nRHS comparator: reduced 1x3, int(||Q_p||^2)^{-q} finite iff q<3/2 <=> c'<2 = T1  (MATCH)")

# ---------- 6. where coupling bites: corank-2 corner e.g. (3,3,4) t=(1,0) ----------
print("\n--- corank>=2 probe: (3,3,4) ---")
mv334,arg334=Mval_min((3,3,4))
print("Mval_min(3,3,4)=",mv334," at t=",arg334," RLCT=",sp.Rational(mv334,2))
# peel at u=1: a=2,b=2? no: u is pivot rank. (M0,M1)=(3,3); cut u -> a=3-u,b=3-u.
for u_ in [0,1,2,3]:
    a_=3-u_; b_=3-u_
    red2=(u_,4) if u_>=1 else None
    print(f"  cut u={u_}: a*b=(3-u)^2={a_*b_}, (M0-u)(M1-u)={a_*b_}")
