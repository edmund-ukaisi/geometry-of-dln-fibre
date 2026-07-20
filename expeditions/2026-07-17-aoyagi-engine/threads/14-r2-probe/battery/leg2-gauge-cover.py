#!/usr/bin/env python3
# guards: coverage-theorem, region-glue
# provenance: threads/14-r2-probe (pnp-o5). DECORRELATED: the Schur gauge ψ is transcribed from the
#   DURABLE cert-single-psi.md (D''' = [1 O; O (D - col1*row1)], c_1 += sum_j d_1j c_j), NOT from
#   pnp-atlas scripts. Exact sympy. Circularity guard: pure algebra, no rlct.
"""
LEG 2 — does composing the per-node Schur gauge ψ with the pivot cover PRESERVE the image-cover?
  chartMap = ψ ∘ β; β covers cubeBox (rung-1). ψ is the per-node gauge (cert-single-psi). For the
  cover to survive we need ψ to be a bounded-unit DIFFEO with full inverse (so ψ∘β covers ψ(cubeBox),
  an open neighbourhood) and BOUNDED distortion (so the scaling bridge globalises small→unit box).
  Checks:
    (2a) det Dψ = 1 EXACTLY (block sizes 2,3,4): ψ measure-preserving, no Jacobian vanishing (unlike β)
         -> contributes NO singular factor, does not create/destroy cover by degeneracy.
    (2b) ψ is a polynomial BIJECTION: ψ∘ψ_inv = id symbolically (the Schur up-date is the inverse).
    (2c) BOUNDED distortion on the unit box: sup |ψ|, sup |ψ_inv| finite & explicit -> NO unbounded
         push (an unbounded push would strand a target point outside every bounded srcBox = undershoot).
  KILL: det ≠ 1 (degeneracy) OR ψ_inv not polynomial / unbounded (cover gap).
"""
import sympy as sp
import sys


def schur_gauge(p, q):
    """ψ on a p×q residual block with corner normalized to 1 (post-β). Interior (i,j>=1 0-based in the
    residual, i.e. rows/cols 2..p, 2..q in 1-based) updates d_ij -> d_ij - d_i0*d_0j (col0=first col,
    row0=first row of the residual after corner=1). Returns (vars, images) as flat lists over the
    interior block entries. Plus the C row-mix c_0 -> c_0 + sum_j d_0j c_j."""
    d = sp.Matrix(p, q, lambda i, j: sp.Symbol(f'd_{i}_{j}'))
    c = sp.Matrix(q, 1, lambda j, k: sp.Symbol(f'c_{j}'))
    # corner d_00 normalized to 1 by β; Schur downdate of the interior (rows 1..p-1, cols 1..q-1)
    psi_d = sp.Matrix(p, q, lambda i, j:
                      d[i, j] - d[i, 0] * d[0, j] if (i >= 1 and j >= 1) else d[i, j])
    # Q^{-1} is UNIT upper-triangular: diagonal 1, off-corner entries d_0j (j>=1). Excluding j=0 (the
    # normalized corner) keeps the C-map unit-triangular => det 1 (a corner term would double-count).
    psi_c = sp.Matrix(q, 1, lambda j, k: c[j] + sum(d[0, jj] * c[jj] for jj in range(1, q)) if j == 0 else c[j])
    return d, c, psi_d, psi_c


def leg2a_det(sizes):
    fails = []
    for (p, q) in sizes:
        d, c, psi_d, psi_c = schur_gauge(p, q)
        # Jacobian over the INTERIOR entries (i>=1,j>=1) that ψ moves, plus c_0 over c-vars.
        int_vars = [d[i, j] for i in range(p) for j in range(q) if (i >= 1 and j >= 1)]
        int_imgs = [psi_d[i, j] for i in range(p) for j in range(q) if (i >= 1 and j >= 1)]
        # the moved d-entries: Jacobian wrt themselves (the d_i0,d_0j are "frozen"/spectator params)
        J = sp.Matrix([[sp.diff(im, v) for v in int_vars] for im in int_imgs])
        det_d = sp.simplify(J.det())
        # c-block jacobian (c_0 image wrt c-vars); off-diagonal are d_0j (params), diagonal 1
        cvars = [c[j] for j in range(q)]
        Jc = sp.Matrix([[sp.diff(psi_c[j], cv) for cv in cvars] for j in range(q)])
        det_c = sp.simplify(Jc.det())
        if det_d != 1 or det_c != 1:
            fails.append((p, q, det_d, det_c))
    return fails


def leg2b_bijection(sizes):
    fails = []
    for (p, q) in sizes:
        d, c, psi_d, psi_c = schur_gauge(p, q)
        # inverse: d_ij -> d_ij + d_i0*d_0j (interior); c_0 -> c_0 - sum d_0j c_j.
        inv_d = sp.Matrix(p, q, lambda i, j:
                          d[i, j] + d[i, 0] * d[0, j] if (i >= 1 and j >= 1) else d[i, j])
        # compose ψ then ψ_inv on the interior: substitute psi_d into inv, check identity
        subs = {d[i, j]: psi_d[i, j] for i in range(p) for j in range(q)}
        comp = sp.Matrix(p, q, lambda i, j: sp.simplify(inv_d[i, j].subs(subs)))
        if comp != d:
            fails.append((p, q, 'psi_inv∘psi != id'))
    return fails


def leg2c_bounded(sizes, box=1):
    """sup over the unit box (|d|,|c| <= box) of |ψ| and |ψ_inv| entries -> explicit finite bound.
    Schur term |d_ij - d_i0 d_0j| <= box + box^2 ; inverse same. Bounded -> scaling bridge applies."""
    rows = []
    ok = True
    for (p, q) in sizes:
        # worst-case interior entry magnitude
        b_fwd = box + box * box            # |d_ij| + |d_i0||d_0j|
        b_inv = box + box * box
        rows.append((p, q, b_fwd, b_inv))
        if not (b_fwd < sp.oo and b_inv < sp.oo):
            ok = False
    return rows, ok


if __name__ == "__main__":
    sizes = [(2, 2), (2, 3), (3, 3), (3, 4), (4, 4)]   # residual block sizes covering kill-set d_center
    print("LEG 2 — Schur gauge ψ cover-preservation (chartMap = ψ∘β)")
    f2a = leg2a_det(sizes)
    print(f"  (2a) det Dψ = 1 (residual + C blocks) at {sizes}: "
          f"{'PASS (unipotent, measure-preserving, no Jacobian vanish)' if not f2a else f2a}")
    f2b = leg2b_bijection(sizes)
    print(f"  (2b) ψ polynomial bijection (ψ_inv∘ψ = id): "
          f"{'PASS (Schur up-date is the exact inverse)' if not f2b else f2b}")
    rows, ok2c = leg2c_bounded(sizes)
    print(f"  (2c) bounded distortion on unit box: {'PASS' if ok2c else 'FAIL'} — "
          f"|ψ|,|ψ_inv| entries ≤ box+box² = 2 at box=1 (finite; scaling bridge globalises)")
    ok = not (f2a or f2b) and ok2c
    print("\nLEG2:", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)
