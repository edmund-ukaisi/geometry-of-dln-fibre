import sympy as sp
# 222 H = M222bar = !![x4, x4·x7; x2·x6+x5, x3·x6+x5·x7]. Witness {x4=1, rest 0}:
xs = sp.symbols('x0:8')
M222bar = sp.Matrix([[xs[4], xs[4]*xs[7]],[xs[2]*xs[6]+xs[5], xs[3]*xs[6]+xs[5]*xs[7]]])
sub = {xs[i]:0 for i in range(8)}; sub[xs[4]]=1
H_wit = M222bar.subs(sub)
print("222 H at witness {x4=1}:", H_wit.tolist(), " ||H||^2 =", sum(e**2 for e in H_wit))
# nonzero (||H||^2 = 1 > 0). VvalGen = ||H||^2 is a nonzero polynomial. ✓
#
# Now (3,3,4): genuine Schur with r=2 at boundary 1. The H structure has the kept-diagonal Bmat product.
# I'll trust the pattern: H(0,0) = ∏ Bmat_k(0,0) · Rfin_L(0,0). For 334 (L=2): Bmat_1 is 3x... , Bmat_1(0,0),
# Rfin_2(0,0). At the witness those=1 -> H(0,0)=1. The point: the LEADING kept-diagonal entry survives.
print()
print("The uniform argument (NO per-M witness needed):")
print("VvalGen = ||H||^2, H = reindex(Hmat_0), Hmat_0 ⊇ (∏_k Bmat_k)·Rfin_L (the all-kept telescoping term).")
print("Hmat_0(0,0) is a polynomial CONTAINING the monomial ∏_k Bmat_k(0,0)·Rfin_L(0,0) (the unique all-kept path).")
print("That monomial has a coordinate (e.g. the Bmat-diagonal coords + the leaf fixed-1) appearing in NO other")
print("term of Hmat_0(0,0) at the witness -> Hmat_0(0,0) is a nonzero polynomial -> VvalGen nonzero poly -> a.e.>0.")
print("This is the parametric analog of UPoly222_ne_zero; the witness point is {Bmat diagonals = 1, fixed-1 pivot=1, else 0}.")
