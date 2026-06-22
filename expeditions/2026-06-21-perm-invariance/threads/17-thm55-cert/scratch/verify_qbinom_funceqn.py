#!/usr/bin/env python3
"""
verify_qbinom_funceqn.py — pin the q-difference functional equations that give the
CLEANEST self-contained Lean proof of ORTH (the convolution inverse B = A^{-1}),
where  A(Y)=sum_s P_s Y^s,  B(Y)=sum_s altP(s) Y^s,  altP(s)=(-1)^s q^{C(s,2)} P_s.

The classical q-binomial theorem (Andrews 10.2.2) is, with our P_s:
    A(Y) = sum_s P_s Y^s = 1/((Y;q)_inf with shift) ;  B(Y)=(Y;q)_inf-shift = A(Y)^{-1}.

Per-COEFFICIENT recurrences to verify (each provable in Lean from P_succ +
geomFactor_mul_one_sub, NO Gaussian binomial), which DRIVE the inductive proof of ORTH:

  (cA)  P_s - q^s P_s = P_{s-1}        i.e. P_s (1 - q^s) = P_{s-1}     [s>=1]   (already R1)
  (cB)  altP_s (1-q^s) = -q^{s-1} altP_{s-1}                            [s>=1]   (already AA)

The convolution-inverse  f_u := sum_{k} altP_k P_{u-k} = [u=0]  then follows from a
SINGLE recurrence in u using (cA),(cB).  We pin the EXACT recurrence:
  multiply f_u by (1-q^u)?  No -- use a WEIGHTED convolution.  The genuine driver is
  the "q-Pascal for the convolution":  consider
     f_u  and  apply (cA) to P_{u-k} (k<u) and isolate.
  We already have (I): f_u - f_{u-1} = altP_u + T_u,  T_u=sum_{k<u} altP_k q^{u-k} P_{u-k}.
  Apply (cA)-inverse to T_u:  q^{u-k} P_{u-k} = P_{u-k} - P_{u-k-1}  [since P_j(1-q^j)=P_{j-1}
     => P_j - P_{j-1} = q^j P_j, with j=u-k].  So
     T_u = sum_{k=0}^{u-1} altP_k ( P_{u-k} - P_{u-k-1} )
         = [sum_{k=0}^{u-1} altP_k P_{u-k}]  -  [sum_{k=0}^{u-1} altP_k P_{u-k-1}]
         = (f_u - altP_u P_0)  -  f_{u-1}
         = f_u - altP_u - f_{u-1}.
  Plug into (I):  f_u - f_{u-1} = altP_u + (f_u - altP_u - f_{u-1})  =>  0 = 0.  TAUTOLOGY.
  So (cA) alone gives a tautology -- need (cB).  Use (cB) to shift altP:
     T_u = sum_{k=0}^{u-1} altP_k q^{u-k} P_{u-k}.  Reindex via (cB): altP_k(1-q^k)=-q^{k-1}altP_{k-1}.
  TEST the (cB)-shifted closed form of altP_u + T_u and confirm it equals -f_{u-1} WITHOUT
  circular ref, i.e. as a consequence of a recurrence on a DIFFERENT convolution g_u:=sum altP_k P_{u-k} q^{?}.
"""
import sympy as sp
from verify_s3 import q, P, altP, DEG

def cap(poly, deg=DEG):
    p = poly if isinstance(poly, sp.Poly) else sp.Poly(sp.expand(poly), q)
    return sp.Poly({m: c for m, c in p.terms() if m[0] <= deg}, q)
def E(poly, deg=DEG-2):
    return cap(poly, deg).as_expr()
def iszero(poly, deg=DEG-3):
    return sp.expand(E(poly, deg)) == 0

def conv(coefA, coefB, u):
    """sum_{k=0}^u coefA(k) coefB(u-k)."""
    acc = sp.Integer(0)
    for k in range(0, u+1):
        acc = E(acc + E(coefA(k)*coefB(u-k)))
    return acc

Pf = lambda s: P(s).as_expr()
Af = lambda s: altP(s).as_expr()

if __name__ == '__main__':
    UMAX = 12
    # CLEANEST DRIVER (the q-binomial-theorem coefficient recurrence):
    # Claim the convolution h_u := sum_{k=0}^{u} altP_k P_{u-k} satisfies, for u>=1,
    #   h_u = q^{u-1} * h_{u-1}     ???  test
    print("test h_u = q^{u-1} h_{u-1} (u>=1)?  [h_u=ORTH conv]")
    def h(u): return conv(Af, Pf, u)
    t1 = True
    for u in range(1, UMAX+1):
        if not iszero(E(h(u)) - (q**(u-1))*E(h(u-1))):
            t1 = False
    print(f"  => {'PASS (h_u=q^{{u-1}}h_{{u-1}} => h_u=0 for u>=1 since h_1=0)' if t1 else 'FAIL (not this recurrence)'}")

    # test h_u = - q^{?} h_{u-1} forms
    for power_expr, name in [(lambda u: q**u, "q^u"), (lambda u: -q**(u-1), "-q^{u-1}"),
                             (lambda u: q, "q"), (lambda u: sp.Integer(0), "0")]:
        ok = all(iszero(E(h(u)) - power_expr(u)*E(h(u-1))) for u in range(1, UMAX+1))
        print(f"  test h_u = {name} * h_{{u-1}}: {'PASS' if ok else 'no'}")
    print()

    # The truly clean statement: h_u = 0 for u>=1, h_0=1. Since each h_u is INDEPENDENTLY
    # computable, the cleanest Lean proof is the q-binomial theorem as the Y-series inverse.
    # Pin the q-difference functional equation of A(Y)=sum P_s Y^s:
    Y = sp.symbols('Y')
    print("q-difference functional equation candidates for A(Y)=sum_s P_s Y^s (truncated):")
    MM = 10
    Aser = lambda M: sum(E(Pf(s))*Y**s for s in range(0, M+1))
    # candidate: (1-Y) A(Y) = A(qY)  ?  i.e. P_s - P_{s-1} = q^s P_s  <=> (cA). YES expected.
    print("  (1-Y) A(Y) ≡ A(qY) mod Y^{M+1} (i.e. P_s - P_{s-1} = q^s P_s):")
    okfe = True
    for M in range(0, MM+1):
        lhs = sp.expand((1-Y)*Aser(M))
        rhsA = sum(E(Pf(s))*(q*Y)**s for s in range(0, M+1))
        rhs = sp.expand(rhsA)
        for j in range(0, M+1):
            if sp.expand(E(lhs.coeff(Y,j)) - E(rhs.coeff(Y,j))) != 0:
                okfe = False
    print(f"    => {'PASS' if okfe else 'FAIL'}")
    # B(Y)=sum altP_s Y^s functional eqn: B(Y) = (1-Y) B(qY)?  <=> altP_s = altP_s? test
    Bser = lambda M: sum(E(Af(s))*Y**s for s in range(0, M+1))
    print("  B(Y) ≡ (1 - qY... ) -- test  B(qY)(1-Y) ≡ B(Y)?  [from altP_s(1-q^s)=-q^{s-1}altP_{s-1}]")
    # altP_s(1-q^s)=-q^{s-1}altP_{s-1}; the matching Y-functional eqn is B(Y)=(1-Y)... let's just test A*B=1 driven by both FEs.
    print("    (the two coefficient recurrences (cA),(cB) are the Lean targets; both PASS as R1/AA earlier.)")
