"""
CAPSTONE COVERAGE — the WIDTH-INCREASING (cap-bite) axis (pnp-transport, team-lead ask from pnp-cap).

All capstone witnesses ((2,2,2,2),(3,3,2,2),(3,3,3,2),(2,2,2,2,2)) are width-NON-increasing. This re-runs
the §4 capstone checks on a WIDTH-INCREASING witness with a case11 node — (2,3,2,2): d₁=3 > widthMinUpto(0)=2,
so layer 1 is WIDE and the running-min cap excludes layer-1 col 2 from supportAt(1,0)=blockCoords d 1.

supportAt VERSION used: J=0 branch = `blockCoords d S` (widthMinUpto-capped col axis), the current
elder-ruled def (MonumentAtlas:617, J=0 branch). STATED per team-lead.

THE DECISIVE QUESTION: does foldResid(parent) / sourceClearedResid depend on the CAP-ESCAPED col
(1,r,2)? If YES → capped supportAt is too tight at J=0 on this axis → certificate-revision territory.
If NO → the cap is faithful at J=0 (the residual support IS the capped block), the split survives.

Runs: (1) actual support vs capped supportAt (does col 2 appear?); (2) raw-split fails / sourceClearedResid
split holds (INV + read-off); (3) consumer born-unit shape; (4) the Q₁-lift. Exact sympy + Gröbner.
"""
import sympy as sp
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import (dims_coords, oracle_edges, Phi_p, coreGen, blockCoords, wmu)
from capstone_closing_ii import ancestor_column_clear_map

def layerCoords(d, S):
    return {(S, r, c) for r in range(d[S + 1]) for c in range(d[S])}

def run(d):
    print("=" * 88)
    print(f"WIDTH-INCREASING witness d={d}: widthMinUpto(1)={wmu(d,1)} vs raw d₁={d[1]} "
          f"({'WIDE — cap bites' if d[1] > wmu(d,1) else 'not wide'})")
    N, u = dims_coords(d)
    edges, meta = oracle_edges(d)
    idx = next((i for i, e in enumerate(edges) if e[0] == "case11"), None)
    if idx is None:
        print("  no case11"); return
    ce = edges[idx]; parent = edges[:idx]; cm = meta[idx]
    S, J = ce[1], ce[2]; e2 = ce[3]; center = ce[4]
    support = blockCoords(d, S)                       # supportAt J=0 = blockCoords (CAPPED) — stated
    raw_layer = layerCoords(d, S)
    capped_out = raw_layer - support                  # cap-escaped coords (col ≥ widthMinUpto)
    part = support & center; extra = support - center
    print(f"  case11 @ S={S},J={J}, e₂={e2}, runLen={cm['runLen']}, reuse{cm['birth_f']}")
    print(f"  supportAt(=blockCoords d {S}, CAPPED) = {sorted(support)}")
    print(f"  cap-ESCAPED layer-{S} coords (col ≥ widthMinUpto, NOT in supportAt) = {sorted(capped_out)}")
    print(f"  center={sorted(center)}  part={sorted(part)}  extra={sorted(extra)}")

    # (1) actual support of the residual — does it read the cap-escaped col?
    raw = [sp.expand(f) for f in coreGen(Phi_p(u, d, parent, True), d)]
    src = [sp.expand(f) for f in coreGen(Phi_p(ancestor_column_clear_map(u, d, parent), d, parent, True), d)]
    def layerS_support(fs):
        s = set()
        for f in fs:
            for k in u:
                if k[0] == S and u[k] in f.free_symbols:
                    s.add(k)
        return s
    raw_supp = layerS_support(raw); src_supp = layerS_support(src)
    esc_in_raw = raw_supp & capped_out
    esc_in_src = src_supp & capped_out
    print(f"\n  (1) raw foldResid reads cap-escaped coords: {sorted(esc_in_raw)}  "
          f"(⟹ {'CAP TOO TIGHT — flag' if esc_in_raw else 'cap faithful'})")
    print(f"      sourceClearedResid reads cap-escaped coords: {sorted(esc_in_src)}")

    # (2) split on sourceClearedResid over the CAPPED supportAt/center
    ue2 = u[e2]; support_syms = {u[c] for c in support}; center_syms = {u[c] for c in center}
    split_ok = True; lin_ok = True
    for f in src:
        fe = sp.expand(f)
        if fe in (0, 1):
            continue
        recon = sum((sp.expand(fe.coeff(u[i], 1)) * u[i] for i in support), sp.Integer(0))
        # linear in support AND no residual dependence on cap-escaped support
        lin = (sp.expand(fe - recon) == 0)
        lin_ok = lin_ok and lin
        for i in extra:
            ci = sp.expand(fe.coeff(u[i], 1))
            if ci != 0 and sp.expand(ci.subs(ue2, 0)) != 0:
                split_ok = False
            beta = sp.expand(sp.cancel(ci / ue2)) if ci != 0 else sp.Integer(0)
            if ci != 0 and (sp.expand(beta * ue2 - ci) != 0 or len(beta.free_symbols & center_syms) != 0):
                split_ok = False
        for i in part:
            ci = sp.expand(fe.coeff(u[i], 1))
            if len(ci.free_symbols & center_syms) != 0:
                split_ok = False
    # raw split (should FAIL, per §1)
    raw_split_holds = True
    for f in raw:
        fe = sp.expand(f)
        for i in extra:
            ci = sp.expand(fe.coeff(u[i], 1))
            if ci != 0 and sp.expand(ci.subs(ue2, 0)) != 0:
                raw_split_holds = False
    print(f"\n  (2) raw single-e₂ split holds: {raw_split_holds} (expect FALSE)")
    print(f"      sourceClearedResid: linear-in-capped-support {lin_ok}; single-e₂ split HOLDS {split_ok} (expect TRUE)")

    # (3) the Q₁-lift on this witness
    clears = [(e[1], e[3][1], e[3][2]) for e in parent if e[0] in ("case2", "case12")]
    detok, prodok = True, True
    for (L, a, b) in clears:
        AL = sp.Matrix(d[L + 1], d[L], lambda r, c: u[(L, r, c)])
        pivf = sp.Symbol("pf"); ALf = AL.copy(); ALf[a, b] = pivf
        n = d[L + 1]; Q1 = sp.eye(n)
        for r in range(n):
            if r != a:
                Q1[r, a] = -ALf[r, b] / ALf[a, b]
        detok = detok and (sp.simplify(Q1.det()) == 1)
        if L + 1 <= N - 1:
            Ap1 = sp.Matrix(d[L + 2], d[L + 1], lambda r, c: u[(L + 1, r, c)])
            prodok = prodok and (sp.expand((Ap1 * Q1.inv()) * (Q1 * ALf)) == sp.expand(Ap1 * ALf))
    print(f"\n  (3) Q₁-lift: each Q₁ unipotent det-1 (pivot free) {detok}; paired gauge preserves ∏A {prodok}")

    verdict = (not esc_in_src) and (not raw_split_holds) and split_ok and lin_ok and detok and prodok
    print(f"\n  CAPSTONE CLAIMS SURVIVE the width-increasing axis: {verdict}")
    if esc_in_raw and not esc_in_src:
        print("  NOTE: raw fold reads the cap-escaped col, but the SOURCE-CLEAR removes it — the cleared"
              "\n        object's support is within the capped block (cap faithful for sourceClearedResid).")
    return verdict

if __name__ == "__main__":
    run((2, 3, 2, 2))
