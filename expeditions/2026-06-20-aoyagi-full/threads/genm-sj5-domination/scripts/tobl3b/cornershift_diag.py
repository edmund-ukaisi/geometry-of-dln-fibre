import numpy as np, sympy as sp
from itertools import combinations
np.random.seed(0)

print("="*74)
print("CORNER-SHRINK DIAGNOSTIC — where does (a,b)->(a-j,b-j) actually come from?")
print("Anchor (3,3,3)@t*=1: a=b=2, M2=3, r=2, shell j=1.")
print("="*74)

# ---------------------------------------------------------------------------
# FACT 1 (exact, symbolic exponent count).  Two candidate reduced weights.
#   detGram_lintegral over box(rows x cols) of det(X X^T)^(-e/2) converges iff e < cols-rows+1.
# ---------------------------------------------------------------------------
def conv(rows, cols, e):   # strict convergence condition e < cols-rows+1
    return e, cols-rows+1, (e < cols-rows+1)

a,b,M2,j = 2,2,3,1
print("\n[FACT 1] The reduced-weight convergence at the two candidate dims:")
# (A) weak-elim at the cut-t* level (b-corank, exponent a):  strong minor is b x (M2-j)
e,thr,ok = conv(b, M2-j, a)
print(f"  (A) cut-t*  : rows=b={b},  cols=M2-j={M2-j}, exponent=a={a}    -> {e} < {thr}? {ok}   (== 'crude'/OBSTR-3)")
# (B) weak-elim at the cut-(t*+j) level (b-j corank, exponent a-j): strong minor is (b-j)x(M2-j)
e,thr,ok = conv(b-j, M2-j, a-j)
print(f"  (B) cut-t*+j: rows=b-j={b-j}, cols=M2-j={M2-j}, exponent=a-j={a-j}  -> {e} < {thr}? {ok}   (== DESIGN)")
print("  => the design weight (B) is obtained ONLY if the corank-row count AND the exponent")
print("     BOTH drop by j.  Weak-direction elimination alone (M2->M2-j) does NOT do that;")
print("     it maps (A). The extra drop b->b-j, a->a-j is the DEEPER-CUT re-index, not a Jacobian.")

# ---------------------------------------------------------------------------
# FACT 2 (exact sympy).  What the det(Q Q^T) factorisation ACTUALLY yields at cut-t*.
#   Q_b = A_cor Z (b x n), det(Q Q^T)^(-a/2) -> |strong b-minor|^(-a) (s_strong)^(-a).
#   The strong minor is b x (M2-j); exponent a.  => weight (A), divergent.
# ---------------------------------------------------------------------------
print("\n[FACT 2] det(Q_b Q_b^T) factorisation at cut-t* (b=2 corank rows), exact:")
bb = sp.symbols('b11 b12 b13 b21 b22 b23', real=True)
B = sp.Matrix([[bb[0],bb[1],bb[2]],[bb[3],bb[4],bb[5]]])   # B = A_cor U, b x M2 = 2x3
s1,s2,t = sp.symbols('s1 s2 t', positive=True)             # t = weak sv (->0)
D = sp.diag(s1**2, s2**2, t**2)
detG = sp.expand((B*D*B.T).det())
strong_minor = (B[:,[0,1]]).det()                          # 2x2 strong minor  (b x (M2-j))
lead = sp.simplify(detG.subs(t,0) - strong_minor**2*s1**2*s2**2)
print(f"   det(Q Q^T)|_(t=0) - (strong 2-minor)^2 s1^2 s2^2 = {lead}   (==0 confirms leading term)")
print(f"   strong minor is {strong_minor.free_symbols} : a {B[:,[0,1]].shape} = b x (M2-j) block, exponent a={a}")
print("   => yields weight (A) rows=b, cols=M2-j, exp=a  -> the pin/reform cert's own minor route.")

# ---------------------------------------------------------------------------
# FACT 3 (MC guide).  Wenn(Z) blow-up at cut-t* vs cut-(t*+j) as sigma_min(Z) -> 0.
#   cut-t*    : Wenn  = int det((A_cor Z)(A_cor Z)^T)^(-a/2),   A_cor 2x3 (b=2 rows), a=2
#   cut-(t*+j): Wenn_u= int det((A_u Z)(A_u Z)^T)^(-(a-j)/2),   A_u   1x3 (b-j=1 row), a-j=1
# ---------------------------------------------------------------------------
def wenn(sig, rows, exp_over2, Nmc=600000, box=1.0):
    # int over A (rows x 3) in box of det((A Z)(A Z)^T)^(-exp_over2);  Z = diag(sig) (U=V=I wlog for scaling)
    A = np.random.uniform(-box,box,size=(Nmc,rows,3))
    Zc = A * (np.array(sig)[None,None,:])           # A Z  with Z=diag(sig): columns scaled
    G = np.einsum('nik,njk->nij', Zc, Zc)           # rows x rows
    d = np.linalg.det(G) if rows>1 else G[:,0,0]
    d = np.clip(d, 1e-300, None)
    vol = (2*box)**(rows*3)
    return (d**(-exp_over2)).mean()*vol

print("\n[FACT 3] Wenn blow-up as weak sv t->0 (MC guide, box=1):")
print("  t        Wenn_cut-t*(2x3,exp a/2=1)     Wenn_cut-(t*+j)(1x3,exp (a-j)/2=0.5)")
for t_ in [0.3,0.1,0.03,0.01,0.003]:
    sig=[1.0,1.0,t_]
    W  = wenn(sig, rows=2, exp_over2=1.0)          # cut-t*
    Wu = wenn(sig, rows=1, exp_over2=0.5)          # cut-(t*+j)
    print(f"  {t_:<8} {W:>14.4f}                 {Wu:>14.4f}")
print("  => cut-t* Wenn GROWS as t->0 (blows up: full a x b corner over-charged on the shell);")
print("     cut-(t*+j) Wenn_u is BOUNDED as t->0 (deeper cut is the correct, convergent object).")
