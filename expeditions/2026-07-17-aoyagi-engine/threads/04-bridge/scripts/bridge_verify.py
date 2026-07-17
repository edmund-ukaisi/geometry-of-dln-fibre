#!/usr/bin/env python3
"""General EXACT chart<->integrand bridge verifier (sympy).

Given a chart map phi: (chart coords) -> layer-matrix entries, and a designated set of DIVISOR
coords, verify the two bridge identities and read the chart's finiteness threshold:

  (P) LOSS PULLBACK:  F o phi = ||prod||^2 = (prod_k div_k^{2.order_k}) * R,
      R the residual: either a bounded UNIT (R(0) != 0) or a NONDEGENERATE residual (Morse rank rho,
      handled by the banked radial read).  We report order_k, R(0), and (if R(0)=0) the Hessian rank.
  (J) JACOBIAN LEDGER: |det D phi| = (prod_k div_k^{JacPow_k}) * (bounded), JacPow_k >= 0.
  (T) THRESHOLD: integrand (F o phi)^{-c'} |Jac| finite  iff  c' < (JacPow_k + 1)/(2.order_k) for each
      divisor k AND c' < rho/2 (residual).  chart threshold = min of these.  Compare to 1/2 minAdm.
"""
import sympy as sp


def analyze(name, coords, div_names, entries_A, minAdm_half, extra_entries=None):
    div = [c for c in coords if c.name in div_names]
    ent = list(entries_A) + (list(extra_entries) if extra_entries else [])
    prod = None  # caller passes the matrix product entries directly in `entries_A`? No: entries are the
    # We instead pass the PRODUCT entries directly (already multiplied) via entries_A.
    F = sp.expand(sum(e**2 for e in ent))
    # pullback: divide by prod div^{2 order}; find order_k = (1/2) min v-order of F along div_k
    #   order_k = smallest exponent of div_k across monomials of F, halved.
    orders = {}
    Fpoly = sp.Poly(F, *coords)
    for d in div:
        mn = min(m[coords.index(d)] for m in Fpoly.monoms())
        orders[d] = sp.Rational(mn, 2)
    mono = sp.prod([d**(2*orders[d]) for d in div])
    R = sp.simplify(F / mono)
    R0 = R.subs({c: 0 for c in coords if c not in div})   # residual at divisor-free origin, div generic
    # residual classification
    if sp.simplify(R.subs({c: 0 for c in coords})) != 0:
        res_kind, rho = "bounded-unit", None
    else:
        nondiv = [c for c in coords if c not in div]
        H = sp.hessian(R.subs({d: 0 for d in div}), nondiv) if nondiv else sp.zeros(0)
        rho = H.rank() if nondiv else 0
        res_kind = f"Morse-residual rank {rho}"
    return F, orders, mono, R, res_kind, rho


def jac(coords, entries):
    J = sp.Matrix([[sp.diff(e, c) for c in coords] for e in entries])
    return sp.factor(sp.simplify(J.det()))


def report(name, coords, div_names, prod_entries, jac_entries, minAdm_half):
    div = [c for c in coords if c.name in div_names]
    F = sp.expand(sum(e**2 for e in prod_entries))
    Fpoly = sp.Poly(F, *coords)
    orders = {d: sp.Rational(min(m[coords.index(d)] for m in Fpoly.monoms()), 2) for d in div}
    mono = sp.prod([d**(2*orders[d]) for d in div])
    R = sp.simplify(F / mono)
    if sp.simplify(R.subs({c: 0 for c in coords})) != 0:
        res_kind, rho = "bounded-unit (>0)", sp.oo
    else:
        nondiv = [c for c in coords if c not in div]
        H = sp.hessian(R.subs({d: 0 for d in div}), nondiv)
        rho = H.rank()
        res_kind = f"Morse rank {rho}"
    detJ = jac(coords, jac_entries)
    Jpoly = sp.Poly(detJ, *coords)
    jacpow = {d: min(m[coords.index(d)] for m in Jpoly.monoms()) for d in div}
    ratios = {d: sp.Rational(jacpow[d] + 1, 1) / (2 * orders[d]) for d in div}
    res_ratio = (rho / sp.Integer(2)) if rho != sp.oo else sp.oo
    thr = min(list(ratios.values()) + [res_ratio])
    print(f"\n=== {name} ===")
    print(f"  F o phi = ({sp.prod([d**(2*orders[d]) for d in div])}) * R,  R = {res_kind}")
    print(f"  |det Dphi| = {detJ}")
    for d in div:
        print(f"    divisor {d}: order={orders[d]}, JacPow={jacpow[d]}, ratio=(JacPow+1)/(2 order)={ratios[d]}")
    print(f"    residual: {res_kind}, ratio={res_ratio}")
    print(f"  chart threshold = min = {thr}   (1/2 minAdm = {minAdm_half})   "
          f"{'BINDING (==)' if thr==minAdm_half else 'non-binding (>)' if thr>minAdm_half else 'UNDERSHOOT!!'}")
    return thr


# ---------- (2,2,2): incidence + blow-up of {delta=u=v=0} ----------
al, a, b, de, up, vp, r, s = sp.symbols("alpha a b delta up vp r s", real=True)

# delta-chart: u=delta up, v=delta vp.  A = al[[1,a],[b,ab+de]], B=[[de up - a r, de vp - a s],[r,s]]
A = sp.Matrix([[al, al*a], [al*b, al*(a*b+de)]])
B = sp.Matrix([[de*up - a*r, de*vp - a*s], [r, s]])
AB = sp.expand(A*B)
entsA = [A[0,0],A[0,1],A[1,0],A[1,1],B[0,0],B[0,1],B[1,0],B[1,1]]
t1 = report("(2,2,2) delta-chart (binding)", [al,a,b,de,up,vp,r,s], {"alpha","delta"},
            [AB[0,0],AB[0,1],AB[1,0],AB[1,1]], entsA, sp.Rational(3,2))

# u-chart: v=u vp, delta=u de'.  (pre-blowup AB = al[[u,v],[bu+de r, bv+de s]]); here blow up {u=v=de=0}
u, vpp, dep = sp.symbols("u vpp dep", real=True)
# reconstruct pre-blowup product in (al,a,b,de,u,v,r,s): AB = al[[u,v],[b u+de r, b v+de s]]
# u-chart: v = u*vpp, de = u*dep
ABu = sp.Matrix([[al*u, al*u*vpp],[al*(b*u+u*dep*r), al*(u*vpp*b+u*dep*s)]])
ABu = sp.expand(ABu)
# jacobian entries: need the chart map to the 8 original entries. Use A,B in these coords:
Au = sp.Matrix([[al, al*a],[al*b, al*(a*b+u*dep)]])
Bu = sp.Matrix([[u - a*r, u*vpp - a*s],[r, s]])   # since original u_pre=u, v_pre=u vpp
entsU = [Au[0,0],Au[0,1],Au[1,0],Au[1,1],Bu[0,0],Bu[0,1],Bu[1,0],Bu[1,1]]
ABu2 = sp.expand(Au*Bu)
t2 = report("(2,2,2) u-chart (sibling)", [al,a,b,u,vpp,dep,r,s], {"alpha","u"},
            [ABu2[0,0],ABu2[0,1],ABu2[1,0],ABu2[1,1]], entsU, sp.Rational(3,2))

print("\n(2,2,2) tree: binding chart threshold 3/2 == 1/2 minAdm; sibling >= 3/2 => box finite for c'<3/2.")

# ---------- (3,3,4) corank-2 chart: its t=(1,0) residual sub-core IS the (2,2,4) core ||Delta.S||^2 ----------
# (verified block-elim identification in D2 census). Full-block (Case 2, corank 2) blow-up of the 2x2
# Delta = C^(1)-residual: Delta = de * E, E-chart E=[[1,e1],[e2,e3]]; S = C^(2) is 2x4 free.
de2, e1, e2, e3 = sp.symbols("de2 e1 e2 e3", real=True)
S = sp.Matrix(2, 4, lambda i, j: sp.Symbol(f"s_{i}{j}", real=True))
Delta = sp.Matrix([[de2, de2*e1], [de2*e2, de2*e3]])
prodD = sp.expand(Delta * S)                      # 2x4 = 8 product entries
prod_entries = [prodD[i, j] for i in range(2) for j in range(4)]
# SHARING check: does de2 divide EVERY product generator?
shared = all(sp.simplify(g / de2).is_polynomial() if hasattr(sp.simplify(g/de2),'is_polynomial') else True
             for g in prod_entries)
shared = all(sp.Poly(g, de2).monoms() and min(m[0] for m in sp.Poly(g, de2).monoms()) >= 1
             for g in prod_entries)
print(f"\n(3,3,4) corank-2 residual = (2,2,4) core: shared divisor de2 divides ALL 8 generators: {shared}")
# jacobian entries: Delta(4) wrt (de2,e1,e2,e3) + S(8) identity
coordsD = [de2, e1, e2, e3] + [S[i, j] for i in range(2) for j in range(4)]
entsD = [Delta[0,0], Delta[0,1], Delta[1,0], Delta[1,1]] + [S[i, j] for i in range(2) for j in range(4)]
minAdm_224_half = sp.Rational(4, 2)
report("(3,3,4) corank-2 chart [(2,2,4) sub-core, shared de2, Case-2 full block]",
       coordsD, {"de2"}, prod_entries, entsD, minAdm_224_half)
