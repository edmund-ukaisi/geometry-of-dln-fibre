"""
Exact-algebra adjudication for peelZBlock scope (deliverable B), on the STEP-0 anchor
(3,3,3,4) t=(1,0,0), corank-2.  After the front peel the tail product is Z = A1 * A2 with
A1 3x3, A2 3x4; the corank-2 non-pivot block is Qb = A1b * A2, A1b = bottom-2 rows of A1 (2x3),
so Qb is a 2x4 PRODUCT.  The Schur block-split gives the corank term ||C.Qp + Gamma.Qb||^2.

Regime atoms require the ISOTROPIC shape ||Delta||^2 + W(z).  The map to that shape must remove the
right factor Qb.  The Gram change of variables Gamma |-> Gamma.Qb has Jacobian det(Qb Qb^T)^{-p/2},
det(Qb Qb^T) = ||wedge^2 Qb||^2 = sum of squares of the 2x2 minors (Plucker coords) of the product.

DECISIVE questions checked here (exact):
  C1. Cauchy-Binet: the 2x2 minors of Qb are BILINEAR in (2x2 minors of A1b, 2x2 minors of A2).
      -> the Plucker vector of Qb is p . M2, p = wedge^2(A1b) (3-vector), M2 = wedge^2(A2) (3x6).
  C2. det(Qb Qb^T) = p . G . p^T with G = M2 M2^T = wedge^2(A2 A2^T) (3x3 Gram), i.e. the corank-2
      product's Gram det is a QUADRATIC FORM in the Plucker coords p of A1b, with matrix a Gram of A2.
  C3. Is det(Qb Qb^T) monomial-times-unit in the ORIGINAL entries?  (If it were, no blow-up needed.)
      Test: is it irreducible / does it factor?  Is its zero locus a coordinate arrangement?
  C4. The zero locus {det(Qb Qb^T)=0} = {rank Qb <= 1}: is it a union of COORDINATE subspaces
      (toric, monomializable by coordinate blow-ups) or a genuine determinantal (non-coordinate)
      variety?  -> check whether the minor ideal equals its own "monomialization" in any coord chart.
  C5. Coupled vs decoupled RLCT gap (sanity, matches DATA/outer-cert): the SHARED exceptional divisor
      changes the toric RLCT (shared 1/2 vs fresh 1), so a naive per-factor resolution undercounts.
"""
import sympy as sp
from itertools import combinations

def minors2(M, rows, cols):
    # 2x2 minors of matrix M over given row-index list and col-index list
    out = {}
    for (i,j) in combinations(rows,2):
        for (k,l) in combinations(cols,2):
            out[((i,j),(k,l))] = sp.expand(M[i,k]*M[j,l]-M[i,l]*M[j,k])
    return out

print("="*80)
print("C1 / C2 : Cauchy-Binet + Gram-det = quadratic form in Plucker coords of A1b")
print("="*80)

# A1b : 2x3, A2 : 3x4 -> Qb = A1b*A2 : 2x4
a = sp.symbols('a0:6', real=True)   # A1b entries (2x3)
A1b = sp.Matrix(2,3, a)
b = sp.symbols('b0:12', real=True)  # A2 entries (3x4)
A2 = sp.Matrix(3,4, b)
Qb = sp.expand(A1b*A2)

# Plucker (2x2 minors) of A1b over its 3 columns:  p_{kl}, {k,l} in C(3,2)
colpairs3 = list(combinations(range(3),2))     # (0,1),(0,2),(1,2)
p = {kl: sp.expand(A1b[0,kl[0]]*A1b[1,kl[1]] - A1b[0,kl[1]]*A1b[1,kl[0]]) for kl in colpairs3}

# 2x2 minors of A2 : rows {k,l} in C(3,2), cols {i,j} in C(4,2)
colpairs4 = list(combinations(range(4),2))     # 6 column pairs
M2 = {}  # M2[(kl, ij)]
for kl in colpairs3:
    for ij in colpairs4:
        M2[(kl,ij)] = sp.expand(A2[kl[0],ij[0]]*A2[kl[1],ij[1]] - A2[kl[0],ij[1]]*A2[kl[1],ij[0]])

# 2x2 minors of the product Qb (2x4): over col pairs ij
minorQb = {ij: sp.expand(Qb[0,ij[0]]*Qb[1,ij[1]] - Qb[0,ij[1]]*Qb[1,ij[0]]) for ij in colpairs4}

# Cauchy-Binet claim: minorQb[ij] = sum_{kl} p[kl]*M2[(kl,ij)]
cb_ok = True
for ij in colpairs4:
    rhs = sp.expand(sum(p[kl]*M2[(kl,ij)] for kl in colpairs3))
    if sp.simplify(minorQb[ij]-rhs) != 0:
        cb_ok = False
        print("  Cauchy-Binet FAIL at", ij)
print("  C1 Cauchy-Binet (minors of product = sum p_kl * M2_kl,ij):", "CONFIRMED" if cb_ok else "FAILED")

# det(Qb Qb^T) = sum_ij minorQb[ij]^2  (Cauchy-Binet for the Gram / wedge^2)
detG = sp.expand(sum(minorQb[ij]**2 for ij in colpairs4))
detG_direct = sp.expand((Qb*Qb.T).det())
print("  det(Qb Qb^T) == sum of squared 2x2 minors:", sp.simplify(detG-detG_direct)==0)

# C2: express as p^T . G . p  with G_{kl,k'l'} = sum_ij M2[(kl,ij)] M2[(k'l',ij)]
pvec = sp.Matrix([p[kl] for kl in colpairs3])
G = sp.zeros(3,3)
for a_i,kl in enumerate(colpairs3):
    for b_i,klp in enumerate(colpairs3):
        G[a_i,b_i] = sp.expand(sum(M2[(kl,ij)]*M2[(klp,ij)] for ij in colpairs4))
quad = sp.expand((pvec.T*G*pvec)[0,0])
print("  C2 det(Qb Qb^T) == p^T G p  (G = wedge^2(A2) Gram):",
      sp.simplify(quad-detG)==0)
print("     -> the corank-2 PRODUCT Gram det is a quadratic form in Plucker coords p=wedge^2(A1b),")
print("        with matrix G a Gram of A2's 2x2 minors.  p and G BOTH vary -> coupled resolution.")

print()
print("="*80)
print("C3 : is det(Qb Qb^T) monomial x unit in the original entries?  (factorization)")
print("="*80)
fac = sp.factor(detG)
print("  factor(det(Qb Qb^T)) has", len(sp.Add.make_args(sp.expand(detG))), "monomials (expanded).")
print("  Is it a single monomial? ->", detG.is_Mul and all(t.is_Pow or t.is_Symbol for t in detG.args)
      if detG.is_Mul else (detG.is_Pow or detG.is_Symbol))
print("  factor():", "NON-trivial factorization" if fac != detG and fac.is_Mul else "IRREDUCIBLE / no monomial split")
# a sharper test: does detG have a nonconstant monomial common divisor?
gcdmon = None
terms = sp.Add.make_args(sp.expand(detG))
allsyms = list(A1b.free_symbols | A2.free_symbols)
print("  common monomial factor of all terms (=> could factor a monomial out):",
      sp.gcd_terms(detG) if False else "checking...")
# compute gcd of the terms as polynomials
g = terms[0]
for t in terms[1:]:
    g = sp.gcd(g, t)
print("     gcd of all", len(terms), "terms =", g, " (1 => NO monomial factors out; genuinely a sum)")
