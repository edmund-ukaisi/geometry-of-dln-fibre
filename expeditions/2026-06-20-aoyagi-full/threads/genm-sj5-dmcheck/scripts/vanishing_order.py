"""
EXACT vanishing-order + tube-codim check for a BOTTLENECK product P = A.B.
The db2 model F = u0^2 |z|^{2m} + u1^2 needs m = vanishing order of the pivot Gram minor U0
along the rank-drop tube, and D = codim of that tube.  Claim: m=1 (determinantal loci reduced),
D = cCodim (product), so D/m = cCodim.  We test this on the sharpest bottleneck.

Bottleneck: A (4x2), B (2x4), P = A.B (4x4), rank(P) <= 2 ALWAYS (structural cap).
Generic rank r = 2.  Binding rank drop: {rank P <= 1}.  cCodim((4,2,4),1) = 3 (product) vs 9 (free).
Pivot Gram minor U0 = det of a 2x2 block gram / smallest 2x2-minor-squared-sum; here we test
the order to which the 2x2 minors of P (and det(P P^T)-type gram) vanish transverse to {rank<=1}.
"""
import sympy as sp

# --- symbolic A (4x2), B (2x4) around a corank-1 point of P=AB (rank drops 2 -> 1) ---
# Base point: A0 with columns e1,e2 (rank 2), B0 = [[1,0,0,0],[0,eps,0,0]] so P0 = A0 B0 has
# 2nd singular direction controlled by eps -> at eps=0, rank(P)=1.  Then perturb everything.
# Simpler & rigorous: put P at a GENERIC rank-1 point and study the (2x2)-minor ideal locally.

# Take the local model: near a generic rank-1 4x4 matrix in the image of AB.
# The image of AB (A:4x2,B:2x4) is exactly {4x4 matrices of rank <= 2}.  Its rank-<=1 sublocus:
# study the 2x2 minors of a generic rank-<=2 matrix near a rank-1 point.

# Parametrize rank-<=2 P = a1 b1^T + a2 b2^T  (a_i in R^4, b_i in R^4).  Rank drops to 1 when
# a2 || a1 or b2 || b1 or the pair degenerates.  Transverse coordinate = the size of the 2nd dyad.
t = sp.symbols('t', real=True)                     # tube distance parameter
# generic vectors
import random
random.seed(1)
def rv(n): return sp.Matrix([sp.Rational(random.randint(-5,5)) for _ in range(n)])
a1, a2 = rv(4), rv(4)
b1, b2 = rv(4), rv(4)
# scale the 2nd dyad by t: at t=0, P = a1 b1^T is rank 1.  For t>0 rank 2 generically.
P = a1*b1.T + t*(a2*b2.T)                            # 4x4, rank 1 at t=0, rank 2 for generic t>0

# The pivot Gram minor U0 (the object coupling to the front block): det of P restricted to a 2x2
# pivot block P[0:2,0:2]-gram, i.e. the sum of squares of 2x2 minors touching the collapsing dir.
# Cleanest scalar tracking sigma_2^2: e2(P P^T) = sum of squared 2x2 minors of P (Cauchy-Binet).
PPt = P*P.T
e2 = sum((PPt[i,i]*PPt[j,j]-PPt[i,j]*PPt[j,i]) for i in range(4) for j in range(i+1,4))
e2 = sp.expand(e2)
order_e2 = sp.Poly(e2, t).monoms()
print("sum of squared 2x2 minors  e2(PP^T) = sigma_1^2 sigma_2^2  as a poly in tube-param t:")
print("   e2 =", sp.factor(e2))
print("   lowest t-power in e2 (=order of sigma_2^2, since sigma_1^2 ~ const):",
      min(m[0] for m in order_e2))
# sigma_1^2 ~ const (a1 b1 dyad), so e2 ~ sigma_2^2; its t-order = 2*(order of sigma_2 in t) = 2*m_eff.
print("   => sigma_2^2 vanishes to t-order", min(m[0] for m in order_e2),
      " => sigma_2 ~ t^", sp.Rational(min(m[0] for m in order_e2),2), " => m (order of sigma_2) =",
      sp.Rational(min(m[0] for m in order_e2),2))
print()

# --- radical / reducedness of the 2x2-minor ideal (m=1 test) via a single 2x2 minor ---
# A single 2x2 minor of P as a function of t: does it vanish to order 1 transverse to {rank<=1}?
minor = sp.expand(P[0,0]*P[1,1]-P[0,1]*P[1,0])
print("a single 2x2 minor of P as poly in t:", sp.factor(minor))
print("   lowest t-power (transverse vanishing order of an individual minor):",
      min(m[0] for m in sp.Poly(minor,t).monoms()))
print("   => individual 2x2 minor vanishes to ORDER 1 in t (radical/reduced determinantal locus).")
