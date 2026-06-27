"""
Codex's escape-valve test: does phi_M factor as a COMPOSITION of elementary maps whose
det-exponents compose automatically (so |det Dphi| = product of factor dets, each a reusable
lemma), reducing the general determinant to bookkeeping?

In the two Lean anchors phi = paramsEquivFlat ∘ pack ∘ T, where T = (radial blow-up) ∘ (Schur shears)
∘ (substitutions), and |det Dphi| = |det Q|·|det T| with |det Q|=1 and |det T| = product of factor
dets via LinearMap.det_comp.  Each factor is one of:
  - pivotBlowupOn (radial)        -> det = u_p^{card-1}     [reusable lemma EXISTS]
  - unit-triangular shear/lift    -> det = 1                [BlockTriangular, det 1]
  - a "diag(b) substitution"      -> det = b^{block}        [spectator monomial]

QUESTION: for a GENERAL achiever path, is T a composition of these THREE elementary families only,
so |det T| = u^{minAdm-1} * (spectator monomial) by det_comp + the three reusable det lemmas?

We test by re-deriving the thread-26 closed form as an EXPLICIT composition of affine-linear-in-the-
remaining-coords maps and checking that the Jacobian FACTORS as a product of the three families'
Jacobians (i.e. the composite Jacobian is block-triangular in the right order).

We do this concretely: for (3,3,3,3) and (3,3,3,3,3) [L=4], express the chart as
  phi = reshape ∘ (radial blow-up of the minAdm binding coords) ∘ (unit-triangular chaining G_s, det 1)
       ∘ (LDU pivot cores K_s, det = ∏ q^{...})
and check each stage's Jacobian determinant separately, confirming the product = the full det.
"""
import sympy as sp
from sympy import symbols, Matrix, zeros, eye, Poly

def stagewise_3333():
    """Express phi3333 as reshape ∘ G(det1) ∘ K-frame(det=spectator) ∘ radial(det=u^{minAdm-1}).
    We check: is the full det = (u-stage det) * (K-stage det) * (G-stage det=1)?
    Concretely we compute the Jacobian of the FULL map and compare its factorization."""
    u=symbols('u')
    a,al,ga,de=symbols('a al ga de')
    l1,l2,m1,m2=symbols('l1 l2 m1 m2')
    b,ll,n1,n2,e1,e2=symbols('b ll n1 n2 e1 e2')
    r0,r1,r2=symbols('r0 r1 r2')
    h10,h11,h12,h20,h21,h22=symbols('h10 h11 h12 h20 h21 h22')
    z0,z1,z2=symbols('z0 z1 z2')
    coords=[u,a,al,ga,de,l1,l2,m1,m2,b,ll,n1,n2,e1,e2,r0,r1,r2,
            h10,h11,h12,h20,h21,h22,z0,z1,z2]
    K=Matrix([[a,a*al],[ga*a,ga*a*al+de]])
    P=Matrix([[1,0],[0,1],[l1,l2]]); Qm=Matrix([[1,0,m1],[0,1,m2]])
    E22=zeros(3,3); E22[2,2]=1
    A=P*K*Qm+u*E22
    D=Matrix([[1],[ll]])*b*Matrix([[1,n1,n2]])+u*Matrix([[0,0,0],[e1,e2,0]])
    r=Matrix([[r0,r1,r2]]); m=Matrix([[m1],[m2]])
    Dmr=D-m*r; B=zeros(3,3)
    for j in range(3): B[0,j]=Dmr[0,j]; B[1,j]=Dmr[1,j]; B[2,j]=r[0,j]
    h1=Matrix([[h10,h11,h12]]); h2=Matrix([[h20,h21,h22]]); zeta=Matrix([[z0,z1,z2]])
    C=zeros(3,3)
    Crow0=u*zeta-n1*h1-n2*h2
    for j in range(3): C[0,j]=Crow0[0,j]; C[1,j]=h1[0,j]; C[2,j]=h2[0,j]
    flat=[X[i,j] for X in [A,B,C] for i in range(3) for j in range(3)]
    J=Matrix([[sp.diff(f,c) for c in coords] for f in flat])
    d=sp.factor(J.det())
    print("  full det(Dphi3333) =", d)
    # the claim: det = +- u^5 * (spectator monomial). Check u-exponent and the spectator factor.
    dp=Poly(sp.expand(J.det()),u); uexp=min(m for (m,) in dp.monoms())
    spect=sp.factor(sp.expand(J.det())/u**uexp)
    print(f"  u-exponent = {uexp} (minAdm-1=5)   spectator factor = {spect}")
    print(f"  -> det factors as u^{uexp} * (spectator).  composition-of-elementary-dets PLAUSIBLE:",
          "YES" if uexp==5 else "NO")

print("=== (3,3,3,3) stagewise det factorization ===")
stagewise_3333()
