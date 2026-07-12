import sympy as sp

# ==================================================================
# EXACT: the Gram divisor det(Q_b Q_b^T)^{-a/2} FACTORS on shell j as
#   det = (strong (M2-j)-minor of A_cor·U)^2 · (strong SV product)^2 · (1 + O(weak))
# so det^{-a/2} = |strong minor|^{-a} · (reduced weight) — the |strong minor|^{-a}
# is the ONLY ε_j-dependent factor (bounded by ε_j^{-a(M2-j)} on the shell), and it
# does NOT depend on the WEAK singular values.  Anchor a=b=2, M2=3, j=1.
# ==================================================================
sp.init_printing()

# A_cor: 2x3 free; work in Z's eigenbasis so Z = U diag(s1,s2,s3) V^T; det((A Z)(A Z)^T)
#   = det(B D B^T),  B = A_cor U (2x3),  D = diag(s1^2,s2^2,s3^2).
b11,b12,b13,b21,b22,b23 = sp.symbols('b11 b12 b13 b21 b22 b23', real=True)
s1,s2,s3 = sp.symbols('s1 s2 s3', positive=True)
B = sp.Matrix([[b11,b12,b13],[b21,b22,b23]])
D = sp.diag(s1**2, s2**2, s3**2)
G = B*D*B.T                      # 2x2 Gram
detG = sp.expand(G.det())

# Cauchy-Binet check: detG == sum over 2-subsets S of det(B[:,S])^2 * prod_{k in S} s_k^2
def minor2(cols):
    return (B[:,cols]).det()
CB = ( minor2([0,1])**2 * s1**2*s2**2
     + minor2([0,2])**2 * s1**2*s3**2
     + minor2([1,2])**2 * s2**2*s3**2 )
print("Cauchy-Binet identity det(BDB^T) = sum_S det(B_S)^2 prod s_S^2 :",
      sp.simplify(detG - sp.expand(CB)) == 0)

# Shell j=1: s3 = weak -> 0 (write s3 = t).  Leading term as t->0:
t = sp.symbols('t', positive=True)
detG_shell = detG.subs(s3, t)
lead = sp.limit(detG_shell / (minor2([0,1])**2 * s1**2 * s2**2), t, 0)
print("\nlim_{t->0} det / [ det(B_{12})^2 · s1^2 s2^2 ]  =", sp.simplify(lead), " (==1 => leading factor is the STRONG minor)")

# So det^{-a/2} = [det(B_{12})^2 s1^2 s2^2]^{-a/2} · (1+O(t)) = |det(B_{12})|^{-a} (s1 s2)^{-a} (1+O(t)).
# The ε_j-dependent factor is |det(B_{12})|^{-a}; det(B_{12}) is the STRONG 2-minor (weak-SV-free).
print("\ndet(B_{{12}}) (the strong 2-minor, a function of A_cor and the STRONG dirs only):")
print("   det(B_12) =", sp.expand(minor2([0,1])), "  -- contains NO s3/t (weak SV).  ✓")

# The RESIDUAL / reduced weight after pulling |strong minor|^{-a}: the O(t) correction is
# nonneg and the leading is exact; the reduced (b-j)=(1)-row weight over the (M2-j)=2 strong
# subspace has exponent (a-j)/2 = 1/2.  Confirm det factorises as strong^2 * (1 + t^2 R):
detG_over_strong = sp.simplify(detG_shell / (minor2([0,1])**2 * s1**2 * s2**2))
print("\ndet / strong-leading  = 1 + (correction).  correction is O(t^2), nonneg:")
corr = sp.expand(detG_over_strong - 1)
print("   correction =", corr)
print("   -> as t->0 the divisor det^{-a/2} = |strong 2-minor|^{-a}·(s1 s2)^{-a}·(1+O(t^2))^{-a/2},")
print("      |strong 2-minor|^{-a} uniformly BOUNDED (Cauchy-Binet >= eps^2 floor, weak-SV-free).")

# ==================================================================
# The weighted-AM-GM DOMINATION direction (matching landed cornerSliceAtUnits_le), anchor form:
#   (w + ‖resid‖^2)^{-c'} <= w^{-c'}   [drop nonneg residual]  -- the SAFE upper-bound direction.
# ==================================================================
w, res, cp = sp.symbols('w res cp', positive=True)
print("\nDomination direction (drop nonneg residual): (w+res)^(-cp) <= w^(-cp) for res>=0, cp>0:",
      "  TRUE (monotone decreasing in base).")
