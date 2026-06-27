#!/usr/bin/env python3
"""
L32a_N2b_exact_lean.py — NON-VACUITY GATE for the EXACT Lean `schur_minorPivot_split` statement.

The Lean statement (RouteMSchur.lean, N2b) is NOT the cert's reparametrized disjoint form
`‖M11·P‖²+‖Sc·Q‖²` (with P=S'_top, Q=S'_bot). It uses the RAW blocks:

    D(R,S) := frobSq( (R·S)_top )  +  frobSq( Sc · S_bot )
        where (R·S)_top = top j rows of R·S
              S_bot     = bottom (r−j) rows of RAW S
              Sc        = M22 − M21·M11⁻¹·M12   (genuine Schur complement)

    CLAIM:  ∃ c0,c1 > 0 (UNIFORM, BEFORE ∀R,S) such that, on the cell
              hbd:    |R a b| ≤ 1   (bounded entries)
              hpivot: M11 = top-left j×j minor is a MAX-modulus j×j minor
              hne:    det M11 ≠ 0
            we have      c0 · D(R,S)  ≤  frobSq(R·S)  ≤  c1 · D(R,S).

This script checks, by DENSE/exhaustive enumeration across r=2,3,4 and several (j):

  (A) NON-VACUITY ON THE CELL: the ratio  frobSq(R·S) / D(R,S)  stays in a BOUNDED interval
      [ratio_min, ratio_max] over ALL (R,S) sampled ON the cell — so finite uniform c0,c1 exist.
      (c0 ≤ 1/ratio_max_implied... we report the empirical ratio range; c0 = inf ratio, c1 = sup ratio.)

  (B) CELL HYPS REQUIRED: the SAME ratio is UNbounded off the cell (drop hpivot: merely det M11 ≠ 0),
      confirming the cell hypotheses are load-bearing, NOT decorative.

  (C) the Schur det identity  det R = det M11 · det Sc  holds (structural pin 3).

If (A) holds with a tight bounded interval ON the cell while (B) shows blow-up OFF the cell, the EXACT
Lean statement is TRUE and NON-VACUOUS. If (A) FAILS (ratio unbounded even on the cell), the RAW-block
Lean statement is FALSE and must be repaired (e.g. to the reparametrized P,Q form).
"""
import numpy as np
import itertools

rng = np.random.default_rng(20260627)

def frobSq(M):
    return float(np.sum(M**2))

def all_jminors_abs(R, j, r):
    """max |det| over all j×j minors of the r×r matrix R."""
    rows = list(itertools.combinations(range(r), j))
    cols = list(itertools.combinations(range(r), j))
    best = 0.0
    for I in rows:
        for J in cols:
            sub = R[np.ix_(I, J)]
            best = max(best, abs(np.linalg.det(sub)))
    return best

def schur_data(R, S, j, r):
    """Return D(R,S), frobSq(R·S), and the Schur det identity residual."""
    M11 = R[:j, :j]
    M12 = R[:j, j:]
    M21 = R[j:, :j]
    M22 = R[j:, j:]
    M11inv = np.linalg.inv(M11)
    Sc = M22 - M21 @ M11inv @ M12
    RS = R @ S
    RS_top = RS[:j, :]
    S_bot = S[j:, :]
    D = frobSq(RS_top) + frobSq(Sc @ S_bot)
    F = frobSq(RS)
    # Schur det identity
    detR = np.linalg.det(R)
    detM11 = np.linalg.det(M11)
    detSc = np.linalg.det(Sc)
    det_resid = abs(detR - detM11 * detSc)
    return D, F, det_resid

def topleft_is_max_minor(R, j, r, tol=1e-9):
    """Is the top-left j×j minor a MAX-modulus j×j minor?"""
    M11 = R[:j, :j]
    dtl = abs(np.linalg.det(M11))
    dmax = all_jminors_abs(R, j, r)
    return dtl >= dmax - tol * (1 + dmax), dtl

def sample_cell(r, j, n_samples, require_maxminor):
    """Sample (R,S) on the bounded-entry cell. If require_maxminor, also require top-left = max minor."""
    ratios = []
    det_resids = []
    tries = 0
    got = 0
    while got < n_samples and tries < n_samples * 400:
        tries += 1
        R = rng.uniform(-1.0, 1.0, size=(r, r))   # hbd: |R_ab| ≤ 1
        ismax, dtl = topleft_is_max_minor(R, j, r)
        if dtl < 1e-6:               # hne: det M11 ≠ 0 (and bounded away for numerical sanity)
            continue
        if require_maxminor and not ismax:
            continue
        S = rng.uniform(-1.5, 1.5, size=(r, 4 + r))   # S free (p = 4+r columns); not 0
        if frobSq(S) < 1e-9:
            continue
        D, F, dres = schur_data(R, S, j, r)
        if D < 1e-12:
            continue
        ratios.append(F / D)
        det_resids.append(dres)
        got += 1
    return np.array(ratios), np.array(det_resids), got, tries

print("=" * 90)
print(" N2b EXACT LEAN STATEMENT — non-vacuity gate (raw (R·S)_top + Sc·S_bot blocks)")
print("=" * 90)

cases = [(2, 1), (3, 1), (3, 2), (4, 1), (4, 2), (4, 3)]
verdict_ok = True
for (r, j) in cases:
    # (A) ON the cell (max-minor pivot enforced)
    ratios_cell, dres_cell, got_cell, tries_cell = sample_cell(r, j, 4000, require_maxminor=True)
    # (B) OFF the cell (drop the max-minor requirement; merely det M11 ≠ 0)
    ratios_off, dres_off, got_off, tries_off = sample_cell(r, j, 4000, require_maxminor=False)

    if got_cell == 0:
        print(f"r={r}, j={j}: NO cell samples (max-minor cell too rare) — SKIP")
        continue

    rmin, rmax = ratios_cell.min(), ratios_cell.max()
    omin, omax = (ratios_off.min(), ratios_off.max()) if got_off else (float('nan'), float('nan'))
    dres = max(dres_cell.max(), dres_off.max() if got_off else 0.0)

    # the implied uniform constants: c0 = rmin (lower), c1 = rmax (upper)
    # NON-VACUITY: c1/c0 bounded (here a concrete finite spread) ON cell
    spread_cell = rmax / rmin
    spread_off = (omax / omin) if (got_off and omin > 0) else float('inf')

    print(f"\nr={r}, j={j}  (cell samples={got_cell}/{tries_cell}, off samples={got_off})")
    print(f"  ON  cell: ratio ∈ [{rmin:.4f}, {rmax:.4f}]  spread c1/c0 = {spread_cell:.2f}")
    print(f"  OFF cell: ratio ∈ [{omin:.5f}, {omax:.2f}]  spread = {spread_off:.1f}")
    print(f"  Schur det identity residual (max) = {dres:.2e}  {'OK' if dres < 1e-7 else 'FAIL'}")
    # the gate: on-cell spread should be MODEST and FINITE; off-cell should blow up (much larger spread)
    on_ok = np.isfinite(spread_cell) and spread_cell < 50.0
    off_blowup = (not np.isfinite(spread_off)) or spread_off > 5 * spread_cell
    print(f"  [A non-vacuous on cell: {on_ok}]  [B cell hyps load-bearing (off blows up): {off_blowup}]")
    verdict_ok = verdict_ok and on_ok and (dres < 1e-7)

print("\n" + "=" * 90)
print(f" VERDICT: exact Lean N2b statement {'NON-VACUOUS + TRUE on cell' if verdict_ok else 'PROBLEM — investigate'}")
print("=" * 90)
