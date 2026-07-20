#!/usr/bin/env python3
# guards: coverage-theorem
# provenance: threads/19-loss-factorization (loss-t15). The elder's GATE for the ratified prefix
# re-base of InvValC (2026-07-20). The entry-wise "cleared row = diagonal" claim on the FULL product
# prod M (acc w) is FALSE at intermediate states; it is TRUE only on the PREFIX (front) block
# diag(b)·[[E_J,O],[O,D_J]] (worked.tex:479-482). This battery runs the elder's two legs, sympy-exact,
# at an intermediate state with a NONEMPTY trailing factor (the structural point the leaf never sees).
#
# The abstract model (value_threaded_verify.py's b-chain), minimally extended to expose the front vs
# full split. Structural bridge to OUR construction (that layer-S charts write only layer-≤S flat
# coordinates, so prod = prefix · RAW trailing by prodAux associativity) is the CITED code read, below.
#
#   prod M (acc w)  =  [prodPrefix : layers ≤ S at acc w]  ·  [layers > S at RAW w]      (associativity)
#                   =  diag(b)·[[E_J,O],[O,D_J]]          ·  ∏_{s>S} C^{(s)}  (RAW, non-diagonal rows)
#
# LEG (i)  : cleared rows of the PREFIX are diagonal (= b_i e_i)                 -> re-base is SOUND
# LEG (ii) : cleared rows of the FULL product are NOT diagonal                   -> the catch is REAL
# One leg alone is inconclusive (elder). If LEG (i) fails, STOP -> three-factor-matrix invariant.
import sympy as sp


def build_front(bvals, Jcleared):
    """The prefix/front block diag(b)·[[E_J,O],[O,D_J]] at an intermediate state (worked.tex:479).
       bvals = the b-chain diagonal (length m = M(S)); Jcleared = # cleared pivots.
       Cleared rows i<J: E_J corner -> row i = b_i e_i (diagonal). Residual rows i>=J: D_J (dense).
       Returns the m x m front block (M(0)=M(S)=m for this square abstract instance)."""
    m = len(bvals)
    D = sp.Matrix(m, m, lambda r, c:
                  (1 if r == c else 0) if (r < Jcleared or c < Jcleared)
                  else sp.Symbol(f'd_{r}_{c}'))            # D_J residual on the un-cleared sub-block
    return sp.diag(*bvals) * D


def leg_i(front, Jcleared):
    """Prefix cleared rows (i<J) are diagonal: off-diagonal entries vanish."""
    m = front.rows
    offdiag = [sp.simplify(front[i, c]) for i in range(Jcleared) for c in range(m) if c != i]
    return all(e == 0 for e in offdiag), offdiag


def leg_ii(front, Jcleared):
    """FULL product = front · RAW trailing (generic un-processed layer). Cleared rows NOT diagonal."""
    m = front.rows
    T = sp.Matrix(m, m, lambda r, c: sp.Symbol(f't_{r}_{c}'))   # the raw trailing layer(s)
    full = sp.expand(front * T)
    # a cleared row i<J of the full product: off-diagonal entries generically NONZERO
    witnesses = []
    for i in range(Jcleared):
        for c in range(m):
            if c != i:
                witnesses.append((i, c, sp.simplify(full[i, c])))
    not_diag = any(e != 0 for (_, _, e) in witnesses)
    return not_diag, witnesses, full


def run():
    print("=" * 78)
    print("PREFIX RE-BASE GATE (elder) — two legs at an intermediate state, nonempty trailing")
    print("=" * 78)
    # Intermediate state: m = M(S) = 3, J = 2 cleared pivots (rows 0,1 diagonal-final; row 2 residual).
    # b-chain b_i = ∏_{t̃_k < i} u_k (squarefree; value_threaded_verify.py PART A).
    u0, u1, u2 = sp.symbols('u0 u1 u2', positive=True)
    bvals = [u0, u0 * u1, u0 * u1 * u2]        # a monotone b-chain (b_0 | b_1 | b_2)
    Jcleared = 2
    front = build_front(bvals, Jcleared)
    print(f"  b-chain (bmon) = {bvals} ; J cleared = {Jcleared}")
    print(f"  PREFIX/front block diag(b)·[[E_J,O],[O,D_J]] =\n{sp.pretty(front)}")

    ok_i, offdiag_i = leg_i(front, Jcleared)
    print()
    print(f"  LEG (i)  prefix cleared rows (i<{Jcleared}) diagonal — off-diagonals = {offdiag_i}")
    print(f"           => {ok_i}  (prefix cleared rows ARE b_i e_i — the re-base is SOUND)")

    ok_ii, wit, _ = leg_ii(front, Jcleared)
    print()
    print(f"  LEG (ii) FULL = front · RAW trailing; cleared-row off-diagonals:")
    for (i, c, e) in wit:
        print(f"           full[{i},{c}] = {e}")
    print(f"           => NOT diagonal: {ok_ii}  (full cleared rows carry b_i·(raw trailing row) — the catch is REAL)")

    # Sanity: the off-diagonal is EXACTLY b_i · (trailing entry) — the contamination is the raw factor.
    contamination_ok = all(e.has(sp.Symbol(f't_{i}_{c}')) for (i, c, e) in wit if e != 0)
    print()
    print(f"  contamination is the RAW trailing (each full[i,c] carries a t_i_c factor): {contamination_ok}")

    ok = ok_i and ok_ii and contamination_ok
    print()
    print("VERDICT:", "PASS — prefix cleared rows diagonal (i); full cleared rows NOT diagonal, "
          "contaminated by the raw trailing (ii). The prefix re-base is the faithful object; the "
          "entry-wise-on-full statement is false at intermediate states." if ok else "FAIL")
    return ok


# ---------------------------------------------------------------------------------------------------
# STRUCTURAL BRIDGE to OUR construction (the cited code read; no conOracle port per elder).
# A chart geoChartMapNorm alphaGauge at a node in layer S writes ONLY flat coordinates of layers <= S:
#   - flatCoordOf M s i j has s : Fin L = the LAYER                         (CenterIndices.lean:30-32)
#   - the d-block center cells are resBlockCenterIndices at node.layer      (CenterIndices.lean:52-58)
#   - the case-1 u-corner is uCornerSel at the merged divisor's BIRTH layer (node.divBirthCoord f).1,
#     which is <= node.layer (born at/before the merge)                     (QNodeCarrier.lean:438-484)
#   - the alpha gauge schurCells is all at <node.layer, ...>                (GeoAlphaGauge.lean:135)
#   - non-center cells are FIXED spectators                                 (GeoFoldRegroup.lean:135)
# Hence prod M (acc w) = prodPrefix(layers <= S at acc w) · (layers > S at RAW w), by prodAux
# associativity (Loss.lean:33). The case-11 u-corner touch of an earlier layer is pivot-FREE
# (z_mu(Bw)=z_mu(w), t14's case-11 read), so it does NOT disturb the already-cleared earlier-layer
# prefix rows. This is the abstract-to-construction bridge for the two legs above.
# ---------------------------------------------------------------------------------------------------

if __name__ == "__main__":
    import sys
    sys.exit(0 if run() else 1)
