#!/usr/bin/env python3
"""
FAITHFUL loss-pullback toggle (exact, uses the Lean chart maps verbatim).

Builds the ACTUAL (3,3,4) loss  K = sum_{i,j} P[i,j]^2 ,  P = A1.A0  (A0,A1 = Corank2CoreGenWrap),
pulls it back through gWrap = sigmaPiv o gFaithful, and TOGGLES each shear support to find which is
LOAD-BEARING for the survivor (the residual generator = 1 at the center).

Shear supports in gFaithful (Corank2FaithfulComposite / Corank2GWrapDecomp shearH):
  (a) within-layer Schur cross-terms  : +u8*u10, +u9*u10, +u8*u11, +u9*u11   (in g[4..7])
  (b) recoord (Q2^{-1} against S)     : -u8*u12-u9*u16, ...                  (in g[8..11])

For each toggle we divide K.g by (dominant monomial E=u0)^2 and read the 12 residual quotients at 0.
A SURVIVOR (some quotient(0) != 0) => the survivor sandwich fires (SMOOTH-with-that-shear-dropped).
"""
import sympy as sp

u = sp.symbols('u0:21')

def A0(u):
    return sp.Matrix([[u[20],u[2],u[3]],[u[0],u[4],u[6]],[u[1],u[5],u[7]]])
def A1(u):
    return sp.Matrix(4,3, lambda a,b: u[8+4*b+a])

def gFaithful(u, schur=True, recoord=True):
    g = list(u)
    g[0]=u[8]; g[1]=u[9]; g[2]=u[10]; g[3]=u[11]
    sA = 1 if schur else 0
    rA = 1 if recoord else 0
    g[4]=u[0]*u[1]      + sA*(u[8]*u[10])
    g[5]=u[0]*u[1]*u[5] + sA*(u[9]*u[10])
    g[6]=u[0]*u[1]*u[6] + sA*(u[8]*u[11])
    g[7]=u[0]*u[1]*u[7] + sA*(u[9]*u[11])
    g[8]=u[0]           - rA*(u[8]*u[12]+u[9]*u[16])
    g[9]=u[0]*u[2]      - rA*(u[8]*u[13]+u[9]*u[17])
    g[10]=u[0]*u[3]     - rA*(u[8]*u[14]+u[9]*u[18])
    g[11]=u[0]*u[4]     - rA*(u[8]*u[15]+u[9]*u[19])
    return g

def sigmaPiv(w):
    # blockBlowupMap {0..7,20} pivot 20 : coords 0..7 -> w20*wk ; 20 -> w20 ; else fixed
    S = set(range(8)) | {20}
    return [ (w[20] if k==20 else (w[20]*w[k] if k in S else w[k])) for k in range(21) ]

def loss_generators(chart):
    """12 entries of P=A1.A0 pulled back through `chart` (a list-valued map ℝ^21->ℝ^21)."""
    g = chart(u)
    P = sp.expand(A1(g)*A0(g))
    return [sp.expand(P[i,j]) for i in range(4) for j in range(3)]

def gWrap(u, schur=True, recoord=True):
    return sigmaPiv(gFaithful(u, schur, recoord))

def div_by_monomial(e, mono):
    """exact divide poly e by a monomial mono; return (quotient, is_polynomial)."""
    q = sp.together(sp.expand(e) / mono)
    q = sp.cancel(q)
    is_poly = q.is_polynomial(*u)
    return sp.expand(q), is_poly

def residual_report(name, chart, mono):
    gens = loss_generators(chart)
    quots, ok_poly = [], True
    for e in gens:
        q, ip = div_by_monomial(e, mono)
        ok_poly &= ip
        quots.append(q)
    at0 = [sp.expand(q).subs({s:0 for s in u}) for q in quots]
    survivor = any(v != 0 for v in at0)
    print(f"\n[{name}]  monomial b1 = {mono}")
    print(f"   every entry divisible by b1 : {ok_poly}")
    print(f"   residual quotients at center: {at0}")
    print(f"   SURVIVOR present            : {survivor}  ({'SMOOTH' if survivor else 'SINGULAR/vanishes'})")
    return survivor, at0

if __name__ == '__main__':
    mono = u[0]*u[20]     # dominant b1 for gWrap = c11 * E  (Corank2CoreGenWrap)
    print("="*90); print("CANONICAL gWrap : all shears ON  (the proven done-leaf)"); print("="*90)
    residual_report("gWrap FULL (schur+recoord)", lambda w: gWrap(w, True, True), mono)
    print("="*90); print("TOGGLE the S=2 recoord shear OFF (drop support (b))"); print("="*90)
    residual_report("gWrap, recoord OFF", lambda w: gWrap(w, True, False), mono)
    print("="*90); print("TOGGLE the within-layer Schur shear OFF (drop support (a))"); print("="*90)
    residual_report("gWrap, schur OFF", lambda w: gWrap(w, False, True), mono)
    print("="*90); print("TOGGLE BOTH shears OFF (blow-up only)"); print("="*90)
    residual_report("gWrap, BOTH OFF (blow-up only)", lambda w: gWrap(w, False, False), mono)
