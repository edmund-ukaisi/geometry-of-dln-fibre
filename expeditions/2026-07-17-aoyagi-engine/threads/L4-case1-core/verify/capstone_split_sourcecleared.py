"""
CAPSTONE SPLIT — the FIX object (pnp-transport, task #68 follow-on).

The obstruction (capstone-obstruction-note.md): Deg1SupportedOn (foldResid p) ed.center FAILS on
the RAW shears-only foldResid because the input layer's un-cleared below-pivot coupling survives.
Codex Q3/Q4: the split-carrying object is the SOURCE-cleared residual — zero the cleared columns'
below-pivot input entries BEFORE the shears.

This script turns the obstruction into an ACTIONABLE fix-certificate: on the real oracle case11
branches (2,2,2,2) and (3,3,2,2), build foldResid(parent) with the source-clear applied, and verify
the FULL single-e₂ MergeBoostSplit holds across ALL slots (each slot ∈ ⟨ed.center⟩, extra coeffs
divisible by u_{e₂}, coefficients center-ignoring). Two clear variants tested:
  (C1) column-clear only: zero (L,r,J) for r>J at each ancestor clear (L,J)  [Q₁ column-clear];
  (C2) column+row clear:  additionally zero (L,J,c) for c>J                  [Q₁ AND Q₂].
Reports which variant delivers the clean split (Codex: C1 suffices for (2,2,2,2)).

Exact (sympy + grevlex Gröbner). Reports; asserts nothing about the Lean statement.
"""
import sympy as sp
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_split_oracle import (dims_coords, oracle_edges, supportAt,
                                    canonNormalizationOf, coreGen)

def apply_edge_srcclear(u, d, case, sL, sC, piv, cen, delta, clear_rows):
    """apply one ancestor edge; if a δ=1/δ=0 case2/case12 clear, FIRST zero the cleared column's
       below-pivot input entries (and pivot row if clear_rows) at the SOURCE (before the shear)."""
    v = dict(u)
    if case in ("case2", "case12"):
        a, b = piv[1], piv[2]
        for (L, r, c) in list(v.keys()):
            if L == sL:
                if c == b and r > a:            # Q₁ column-clear: below-pivot in cleared column
                    v[(L, r, c)] = sp.Integer(0)
                if clear_rows and r == a and c > b:   # Q₂ row-clear: right-of-pivot in cleared row
                    v[(L, r, c)] = sp.Integer(0)
    # now the usual shear + blowup
    if case in ("case11", "rollover"):
        w = dict(v)
    else:
        phi = canonNormalizationOf(v, d, sL, sC, piv, True)
        w = {k: v[k] + phi[k] for k in v}
    out = {}
    for k in v:
        if case == "rollover":
            out[k] = w[k]
        elif delta == 1:
            out[k] = sp.Integer(1) if k == piv else w[k]
        else:
            out[k] = (w[piv] if k == piv else (w[piv] * w[k] if k in cen else w[k]))
    return out

def foldResid_srcclear(u, d, parent, clear_rows):
    v = dict(u)
    for e in reversed(parent):
        v = apply_edge_srcclear(v, d, *e, clear_rows)
    return coreGen(v, d)

def check_full_split(fr, u, d, support, part, extra, center, e2):
    ue2 = u[e2]
    support_syms = {u[c] for c in support}
    center_syms = {u[c] for c in center}
    ok = True; notes = []
    for j, f in enumerate(fr):
        fe = sp.expand(f)
        if fe in (0, 1):
            continue
        recon = sum((sp.expand(fe.coeff(u[i], 1)) * u[i] for i in support), sp.Integer(0))
        lin = sp.expand(fe - recon) == 0
        c = {i: sp.expand(fe.coeff(u[i], 1)) for i in support}
        cfree = all(len(c[i].free_symbols & support_syms) == 0 for i in support)
        divB = all(sp.expand(c[i].subs(ue2, 0)) == 0 for i in extra)
        # center-ignoring: α_i=c_i (part) free of center; β_i=c_i/ue2 (extra) free of center
        cign = True
        for i in part:
            if len(c[i].free_symbols & center_syms) != 0:
                cign = False
        for i in extra:
            beta = sp.expand(sp.cancel(c[i] / ue2)) if c[i] != 0 else sp.Integer(0)
            if sp.expand(beta * ue2 - c[i]) != 0 or len(beta.free_symbols & center_syms) != 0:
                cign = False
        slot_ok = lin and cfree and divB and cign
        ok = ok and slot_ok
        if not slot_ok:
            notes.append((j, dict(lin=lin, cfree=cfree, divB=divB, cign=cign)))
    return ok, notes

def run(d):
    print("=" * 84)
    print(f"d = {d}")
    N, u = dims_coords(d)
    edges, meta = oracle_edges(d)
    idx = next((i for i, e in enumerate(edges) if e[0] == "case11"), None)
    if idx is None:
        print("  no case11"); return
    ce = edges[idx]; parent = edges[:idx]
    S, J = ce[1], ce[2]; e2 = ce[3]; center = ce[4]
    support = supportAt(d, S, J); part = support & center; extra = support - center
    print(f"  e₂={e2}  center={sorted(center)}  part={sorted(part)}  extra={sorted(extra)}")
    for label, clear_rows in [("C1 column-clear only", False), ("C2 column+row clear", True)]:
        fr = foldResid_srcclear(u, d, parent, clear_rows)
        ok, notes = check_full_split(fr, u, d, support, part, extra, center, e2)
        print(f"  [{label}] single-e₂ MergeBoostSplit holds (ALL slots): {ok}"
              + ("" if ok else f"  fails: {notes}"))

if __name__ == "__main__":
    for d in [(2, 2, 2, 2), (3, 3, 2, 2)]:
        run(d)
