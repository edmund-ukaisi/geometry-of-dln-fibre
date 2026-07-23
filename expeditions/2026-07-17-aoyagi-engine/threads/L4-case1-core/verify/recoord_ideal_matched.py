"""
RECOORD IDEAL — MATCHED-NODE Gröbner comparison on the BAKED def (elder §7(1), corrected).

Supersedes recoord_adjudication.py (1b): that compared baked (3 edges) vs an honest 1-edge clear —
a NODE MISMATCH, so its "both inclusions FALSE" conflated the mismatch with the recoord defect.
This is the like-for-like matched comparison, in ONE common polynomial ring, at the SAME node (ed1
child), for (2,2,2,2), (2,3,2) [wide], (2,3,2,2) [wide].

Structure (re-derived, exact): at the ed1 clear of pivot (0,0) at layer S=0, δ=1 (pivot->1), BOTH the
baked shear (canonNormalizationOf) and the faithful full Schur peel produce
  - the SAME recoordinatized deeper factor  W = A_{S+1}·Q1^{-1}   (baked writes exactly this, layer S+1),
  - the SAME Schur exceptional  e2 = u011 - u010·u001  (and e3 = u021 - u020·u001 for a 3-row block).
They differ ONLY in the layer-0 residual block B (the pivot-column entries u_{0,r,0}, r>0):
  - baked keeps them:   B_baked[r][0] = u_{0,r,0}   (guard row!=a excludes the pivot cross => uncleared)
  - faithful clears them (Q1 row-op):  B_faithful[r][0] = 0
The pivot ROW entry u001 sits in B[0][1] in BOTH baked (phi=0 on the pivot row) and faithful-with-U (the
input change U puts u001 there) — so baked == faithful-with-U EXCEPT the single pivot-COLUMN clear.

Because {A2, W, u001, u010, u020, e2, e3} is an invertible relabel of the original entries, they are
algebraically independent => treat as free vars => a legitimate common ring for the ideal comparison.
"""
import sympy as sp


def blocks(d):
    """Return (M_baked, M_faithfulU, M_faithful0, ring_syms, note) at the ed1 child node for dim vector d.
    d = (d0, d1, ...). Pivot (0,0) at layer 0; recoord at layer 1 (=W); deeper layers untouched (A2...)."""
    N = len(d) - 1
    d0, d1 = d[0], d[1]
    # layer-0 residual block B is d1 x d0 (rows d1, cols d0); pivot at (0,0).
    u001 = sp.Symbol("u001")                       # pivot ROW entry (col 0..? here col 1). general: pivot row
    # pivot-column entries u_{0,r,0}, r=1..d1-1  (the UNCLEARED-in-baked coords)
    col = {r: sp.Symbol(f"u0{r}0") for r in range(1, d1)}
    # Schur exceptionals e_r = u_{0,r,1} - u_{0,r,0}·u001   (interior, col 1), r=1..d1-1
    #   (d0=2 here for all witnesses => single interior column col=1)
    assert d0 == 2, "this common-ring build assumes d0=2 (single interior residual column)"
    e = {r: sp.Symbol(f"e{r+1}") for r in range(1, d1)}   # e2,e3,...
    # pivot ROW entries u_{0,0,c}, c=1..d0-1 => here just u001 (c=1)
    # Build B (d1 x d0):
    def B_of(mode):
        B = sp.zeros(d1, d0)
        B[0, 0] = 1                                # pivot -> 1
        B[0, 1] = u001                             # pivot row entry (kept in baked; put by U in faithful-with-U; 0 in faithful-0)
        if mode == "faithful0":
            B[0, 1] = 0
        for r in range(1, d1):
            B[r, 1] = e[r]                         # Schur exceptional (interior)
            if mode == "baked":
                B[r, 0] = col[r]                   # UNCLEARED pivot column
            else:                                  # faithfulU / faithful0: cleared
                B[r, 0] = 0
        return B
    Bb, BfU, Bf0 = B_of("baked"), B_of("faithfulU"), B_of("faithful0")
    # deeper factor W = A_{1}·Q1^{-1}  (layer 1): shape d2 x d1
    d2 = d[2]
    W = sp.Matrix(d2, d1, lambda r, c: sp.Symbol(f"w{r}{c}"))
    # layers >=2 untouched
    def core(B):
        P = W * B                                  # (d2 x d1)(d1 x d0) = d2 x d0
        for L in range(2, N):
            AL = sp.Matrix(d[L + 1], d[L], lambda r, c: sp.Symbol(f"u{L}{r}{c}"))
            P = AL * P
        return [sp.expand(P[i, j]) for i in range(P.rows) for j in range(P.cols)]
    Mb, MfU, Mf0 = core(Bb), core(BfU), core(Bf0)
    # ring
    syms = set()
    for M in (Mb, MfU, Mf0):
        for g in M:
            syms |= g.free_symbols
    return Mb, MfU, Mf0, sorted(syms, key=str), f"d={d}: block {d1}x{d0}, deeper W {d2}x{d1}"


def ideal_equal(gensA, gensB, ring, label):
    A = [g for g in map(sp.expand, gensA) if g != 0]
    Bg = [g for g in map(sp.expand, gensB) if g != 0]
    GA = sp.groebner(A, *ring, order="grevlex")
    GB = sp.groebner(Bg, *ring, order="grevlex")
    a_sub_b = all(GB.reduce(g)[1] == 0 for g in A)
    b_sub_a = all(GA.reduce(g)[1] == 0 for g in Bg)
    print(f"  [{label}]  <baked> ⊆ <ref>: {a_sub_b}   <ref> ⊆ <baked>: {b_sub_a}   EQUAL: {a_sub_b and b_sub_a}")
    return a_sub_b and b_sub_a


for d in [(2, 2, 2, 2), (2, 3, 2), (2, 3, 2, 2)]:
    print("=" * 78)
    Mb, MfU, Mf0, ring, note = blocks(d)
    print(note, "  |ring| =", len(ring))
    print("  baked M entries:")
    for i, g in enumerate(Mb):
        print(f"    M[{i}] =", g)
    print("  faithful-with-U M entries:")
    for i, g in enumerate(MfU):
        print(f"    M[{i}] =", g)
    print(" GRÖBNER ideal-equality (grevlex):")
    ideal_equal(Mb, MfU, ring, "baked vs faithful-with-U")
    ideal_equal(Mb, Mf0, ring, "baked vs faithful-no-U ")
    # structural: is the difference EXACTLY the u010-leakage (baked - faithfulU in col-0 residual)?
    diff = [sp.expand(a - b) for a, b in zip(Mb, MfU)]
    print("  baked - faithfulU (entrywise):", diff)


print("=" * 78)
print("RADICAL / VARIETY SEPARATION (closes the decorrelated-Codex flag: 'equal radicals not ruled out')")
print("=" * 78)
# (2,3,2): a concrete point in V(<baked>) \ V(<faithful>) => the varieties (hence radicals) DIFFER.
# baked M = [u010 w01 + u020 w02 + w00, e2 w01+e3 w02+u001 w00, u010 w11+u020 w12+w10, e2 w11+e3 w12+u001 w10]
w00, w01, w02, w10, w11, w12 = sp.symbols("w00 w01 w02 w10 w11 w12")
u001, u010, u020, e2, e3 = sp.symbols("u001 u010 u020 e2 e3")
pt = {u010: 1, u020: 0, u001: 0, e2: 0, e3: 0, w01: 1, w02: 0, w00: -1, w11: 0, w12: 0, w10: 0}
Mb = [u010 * w01 + u020 * w02 + w00, e2 * w01 + e3 * w02 + u001 * w00,
      u010 * w11 + u020 * w12 + w10, e2 * w11 + e3 * w12 + u001 * w10]
Mf = [w00, e2 * w01 + e3 * w02 + u001 * w00, w10, e2 * w11 + e3 * w12 + u001 * w10]
bv = [sp.expand(g.subs(pt)) for g in Mb]
fv = [sp.expand(g.subs(pt)) for g in Mf]
print(f"  point makes ALL baked entries 0: {bv}  (all zero: {all(v == 0 for v in bv)})")
print(f"  same point on faithful entries:  {fv}  (some NONZERO: {any(v != 0 for v in fv)})")
print(f"  => the point is in V(<baked>) but NOT V(<faithful>): "
      f"{all(v == 0 for v in bv) and any(v != 0 for v in fv)}")
print("  => V(<baked>) ≠ V(<faithful>) set-theoretically => the RADICALS DIFFER (Codex flag CLOSED).")
print("  NOTE: this does NOT contradict RLCT-preservation — baked is RLCT-equivalent to the ORIGINAL")
print("  via its OWN invertible shear (recoord_path_unipotency.py), NOT to the faithful CHART; the two")
print("  are genuinely different residual presentations of the same original resolution problem.")
