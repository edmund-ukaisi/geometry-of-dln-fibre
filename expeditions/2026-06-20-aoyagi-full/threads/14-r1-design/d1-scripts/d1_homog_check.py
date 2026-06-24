import sympy as sp

# D1 two-point domination, concretely: (2,1,2) r=0 — the smallest non-trivial case.
# L=2, widths H=(2,1,2): A1 is 2x1, A2 is 1x2. prod = A1*A2 (2x2, rank<=1). B=0 (r=0).
# dlnLoss = ||A1*A2||^2 = sum_{ij} (A1*A2)_{ij}^2.
# deepest point: all layers rank 0 => A1=0, A2=0 (the origin).
# An ARBITRARY optimal point v with prod=0: e.g. A1=0, A2 arbitrary; or A1 arbitrary, A2=0;
#   or A1, A2 both nonzero with A1*A2=0 (A1 col-space ⊥ A2 row-space).

# Question: at an arbitrary optimal v, is the loss germ F(v+w) such that the core generators
# are HOMOGENEOUS in the freed (rank-increasing) directions, so the Aoyagi blow-up applies?

a1_0, a1_1 = sp.symbols('a1_0 a1_1', real=True)   # A1 = [a1_0; a1_1] (2x1)
a2_0, a2_1 = sp.symbols('a2_0 a2_1', real=True)   # A2 = [a2_0, a2_1] (1x2)
A1 = sp.Matrix([[a1_0],[a1_1]])
A2 = sp.Matrix([[a2_0, a2_1]])
P = A1*A2   # 2x2
F = sum(P[i,j]**2 for i in range(2) for j in range(2))
F = sp.expand(F)
print("=== (2,1,2) r=0 ===")
print("loss F =", F)
print("F homogeneous degree?", sp.Poly(F, a1_0,a1_1,a2_0,a2_1).is_homogeneous, 
      "(total degree 4, but mixed: deg2 in A1 x deg2 in A2)")

# At deepest point (origin), F is already in 'core' form; generators (P_ij)=a1_i*a2_j are
# homogeneous BILINEAR (degree 1 in A1-vars, degree 1 in A2-vars) => degree-2 total, homogeneous.
gens = [P[i,j] for i in range(2) for j in range(2)]
print("generators P_ij:", gens)
print("each generator homogeneous total-degree?", 
      [sp.Poly(g, a1_0,a1_1,a2_0,a2_1).is_homogeneous for g in gens])

# Now take an ARBITRARY optimal v: A1=0, A2=(c0,c1) fixed nonzero. Local coords A1=w (2x1), A2=(c0,c1)+e.
# prod(v+w) = w * ((c0,c1)+e).  The generators at v: P_ij(v+w) = w_i*(c_j + e_j) = w_i*c_j + w_i*e_j.
c0, c1 = sp.symbols('c0 c1', real=True)  # the fixed A2 at v
w0, w1 = sp.symbols('w0 w1', real=True)  # A1 local (was 0)
e0, e1 = sp.symbols('e0 e1', real=True)  # A2 local perturbation
A1v = sp.Matrix([[w0],[w1]])
A2v = sp.Matrix([[c0+e0, c1+e1]])
Pv = A1v*A2v
print("\n=== arbitrary optimal v: A1=0, A2=(c0,c1) ; local (w,e) ===")
for i in range(2):
    for j in range(2):
        g = sp.expand(Pv[i,j])
        print(f"  P_{i}{j}(v+w) =", g, "  -- linear in w (leading), plus w*e")
print("Leading (lowest-degree) part in (w,e): the w_i*c_j terms (degree 1 in w).")
print("=> at v, the generators are NOT homogeneous in ALL local vars: w_i*c_j (deg1) + w_i*e_j (deg2).")
print("   The lowest-order form is LINEAR in w (c_j != 0). => v is a SMOOTH point of the variety")
print("   in the w-directions (the loss looks like sum (w_i)^2 * |c|^2 + higher) => RLCT contribution")
print("   from the w-block is the REGULAR n/2 (a nondegenerate quadratic), NOT the deep core.")
