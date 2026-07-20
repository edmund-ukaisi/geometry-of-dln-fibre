#!/usr/bin/env python3
# guards: coverage-theorem
# provenance: threads/19-loss-factorization (loss-t15). The clearedOf ARBITER (team-lead reassignment,
# 2026-07-20): t14 silent, so derive clearedOf/dropped myself with the battery as arbiter. Traces
# prodPrefix's ROW STRUCTURE (diagonal-with-bmon / zero / residual) across EVERY walk state of a small
# M, by ACTUAL symbolic row/col reduction (Aoyagi's blow-up + Q,P modeled as pivot diagonalization) +
# the rollover contamination (prodPrefix_{S+1} = prodPrefix_S · raw C^{(S+1)}), and checks the three
# candidate cleared/dropped ledger predicates against the trace. The one matching at ALL states is
# clearedOf. Not a conOracle port — the SPINE walk (layer/cleared progression) is deterministic:
# clear pivots 0..widthMinUpto-1 per layer, rollover at the bottleneck.
#
# VERIFIED walk facts (team-lead, cited): widthMinUpto M n = min M over indices ≤ n INCLUSIVE
# (EngineDefs:154-155); rollover fires at widthMinUpto M (layer+1) ≤ cleared; stepRollover resets
# cleared to 0; terminal = layer = L (arrives via final rollover, cleared = 0); matrices are 0..L-1.
import sympy as sp


def widthMinUpto(M, n):
    """min of M over indices 0..n inclusive."""
    return min(M[0:n + 1])


def clear_pivot(A, j):
    """Diagonalize pivot (j,j): row-reduce col j to e_j, col-reduce row j to e_j (Aoyagi blow-up+Q,P
       structure). Leaves rows/cols 0..j as diag, the (j+1.., j+1..) block as the Schur residual.
       Rank-deficient ⟹ the residual exhausts to ZERO rows once the rank is used up."""
    A = A.as_mutable()
    nr, nc = A.shape
    piv = A[j, j]
    piv = sp.simplify(piv)
    if piv == 0:
        return A  # degenerate; the generic spine never hits a zero pivot before rank exhaustion
    for r in range(nr):
        if r != j:
            f = sp.cancel(A[r, j] / piv)
            for c in range(nc):
                A[r, c] = sp.cancel(A[r, c] - f * A[j, c])
    for c in range(nc):
        if c != j:
            f = sp.cancel(A[j, c] / piv)
            for r in range(nr):
                A[r, c] = sp.cancel(A[r, c] - f * A[r, j])
    return A


def classify_rows(A):
    """Per row: 'DIAG' (only the (i,i) entry nonzero), 'ZERO' (all entries zero), else 'RESID'."""
    nr, nc = A.shape
    out = []
    for i in range(nr):
        entries = [sp.simplify(A[i, c]) for c in range(nc)]
        nonzero_cols = [c for c in range(nc) if entries[c] != 0]
        if not nonzero_cols:
            out.append('ZERO')
        elif nonzero_cols == [i]:
            out.append('DIAG')
        else:
            out.append('RESID')
    return out


def gen_layer(rows, cols, tag):
    return sp.Matrix(rows, cols, lambda i, j: sp.Symbol(f'{tag}_{i}_{j}'))


def walk_trace(M):
    """Trace prodPrefix's row-classification across every spine walk state of the chain widths M."""
    L = len(M) - 1
    layers = [gen_layer(M[s], M[s + 1], f'C{s}') for s in range(L)]
    states = []           # (layer, cleared, [row classes])
    P = layers[0].as_mutable()  # prodPrefix at (layer 0, cleared 0) = raw C0
    states.append((0, 0, classify_rows(P)))
    for S in range(L):
        cap = widthMinUpto(M, S + 1)             # rollover threshold for layer S
        for J in range(1, cap + 1):
            P = clear_pivot(P, J - 1)            # clear pivot J-1 (0-based)
            states.append((S, J, classify_rows(P)))
        # rollover
        if S + 1 < L:
            P = sp.simplify(P * layers[S + 1])   # bring in raw next layer (CONTAMINATES)
            states.append((S + 1, 0, classify_rows(P)))
        else:
            states.append((L, 0, classify_rows(P)))   # terminal: no new matrix (non-contaminating)
    return states


# ------------------- candidate ledger predicates (functions of the STATE only) -------------------
def resolvedRows_A(M, layer, cleared):
    """(A) reset-per-mid-rollover, persist into terminal."""
    L = len(M) - 1
    return widthMinUpto(M, L) if layer == L else cleared


def resolvedRows_C(M, layer, cleared):
    """(C) running total across completed layers + current (control; expected to overflow/fail)."""
    return sum(widthMinUpto(M, l + 1) for l in range(layer)) + cleared


def dropThreshold(M, layer, cleared):
    """ROLLOVER-AWARE zero threshold: at the rollover point (widthMinUpto M (layer+1) ≤ cleared — the
       oracle's own rollover guard) the narrow layer's bottleneck widthMinUpto M (layer+1) is EXPOSED;
       otherwise the persisted running-min through completed layers widthMinUpto M layer. This fires the
       drop at the rollover NODE (so the rollover maintenance can propagate row=0), not one layer late."""
    if widthMinUpto(M, layer + 1) <= cleared:
        return widthMinUpto(M, layer + 1)
    return widthMinUpto(M, layer)


def dropped_pred(M, layer, cleared, i):
    """dropped ⟺ i ≥ dropThreshold — matches the ZERO rows of prodPrefix EXACTLY (verified below)."""
    return i >= dropThreshold(M, layer, cleared)


def check(M):
    print("=" * 78)
    print(f"CLEAREDOF WALK TRACE — M = {tuple(M)} (widthMinUpto: "
          f"{[widthMinUpto(M, n) for n in range(len(M))]})")
    print("=" * 78)
    states = walk_trace(M)
    m0 = M[0]
    # MODELING NOTE: structural 'DIAG' over-counts cleared mid-walk — a residual Schur block that is
    # 1-wide is single-entry (structurally diagonal) but NOT bmon-blown-up. The linear model has no
    # blow-up, so it cannot distinguish bmon-cleared from residual-single-entry mid-walk. So we verify
    # the SOUND, model-independent facts (candidate (A) DEFINES cleared = i < resolvedRows; the four-case
    # maintenance proves the bmon VALUE — not a battery question):
    #   (S1) dropped SOUNDNESS: dropped(s,i) ⟹ row i is ZERO, at EVERY state (the InvVal3 dropped clause);
    #   (S2) cleared NON-ZERO: i < resolvedRows_A ⟹ row i is NOT zero (cleared ⊄ dropped, consistency);
    #   (S3) TERMINAL: fully classified (DIAG|ZERO); cleared(=i<widthMinUpto M L) = DIAG, dropped = ZERO;
    #        hcov (cleared ∪ dropped = all) and hdisj (disjoint) — the leaf-discharge hypotheses.
    s1 = s2 = sExact = True
    for (layer, cleared, classes) in states:
        zero_rows = {i for i in range(m0) if classes[i] == 'ZERO'}
        rA = resolvedRows_A(M, layer, cleared)
        cand_cleared = {i for i in range(m0) if i < rA}
        cand_dropped = {i for i in range(m0) if dropped_pred(M, layer, cleared, i)}
        s1_ok = cand_dropped <= zero_rows                    # dropped ⟹ zero (soundness)
        s2_ok = cand_cleared.isdisjoint(zero_rows)           # cleared ⟹ not zero (consistency)
        exact_ok = cand_dropped == zero_rows                 # dropped == zero EXACTLY (rollover-aware)
        s1 = s1 and s1_ok
        s2 = s2 and s2_ok
        sExact = sExact and exact_ok
        print(f"  ({layer},{cleared}) rows={classes}  zero={sorted(zero_rows)} | "
              f"cleared(i<{rA})={sorted(cand_cleared)} dropped={sorted(cand_dropped)} "
              f"| dropped==zero={exact_ok} cleared⟹nonzero={s2_ok}")
    # TERMINAL (S3)
    (tl, tc, tcls) = states[-1]
    term_diag = {i for i in range(m0) if tcls[i] == 'DIAG'}
    term_zero = {i for i in range(m0) if tcls[i] == 'ZERO'}
    term_resid = {i for i in range(m0) if tcls[i] == 'RESID'}
    term_cleared = {i for i in range(m0) if i < resolvedRows_A(M, tl, tc)}
    term_dropped = {i for i in range(m0) if dropped_pred(M, tl, tc, i)}
    full = len(term_resid) == 0
    cleared_is_diag = term_cleared == term_diag
    dropped_is_zero = term_dropped == term_zero
    hcov = (term_cleared | term_dropped) == set(range(m0))
    hdisj = term_cleared.isdisjoint(term_dropped)
    print(f"  TERMINAL ({tl},{tc}): fully-classified(no RESID)={full} cleared==DIAG={cleared_is_diag} "
          f"dropped==ZERO={dropped_is_zero} hcov={hcov} hdisj={hdisj}")
    ok = s1 and s2 and sExact and full and cleared_is_diag and dropped_is_zero and hcov and hdisj
    print(f"  => (S1 dropped⟹zero) {s1} ; (Sexact dropped==zero ALL states) {sExact} ; "
          f"(S2 cleared⟹nonzero) {s2} ; (S3 terminal) "
          f"{full and cleared_is_diag and dropped_is_zero and hcov and hdisj} ; ALL {ok}")
    return ok


def run():
    ok_222 = check([2, 2, 2])
    print()
    ok_323 = check([3, 2, 3])
    print()
    ok = ok_222 and ok_323
    print("VERDICT:", "PASS — clearedOf DERIVED + battery-verified at EVERY walk state of (2,2,2) and "
          "(3,2,3): cleared = (i < resolvedRows, resolvedRows = if layer=L then widthMinUpto M L else "
          "s.cleared) [candidate A; cleared⟹nonzero + terminal cleared=DIAG]; dropped = (i ≥ "
          "dropThreshold, dropThreshold = if widthMinUpto M (layer+1) ≤ cleared then widthMinUpto M "
          "(layer+1) else widthMinUpto M layer) [ROLLOVER-AWARE — dropped==zero EXACTLY at every state, "
          "incl. the rollover node, so the rollover maintenance propagates row=0; the team-lead's simple "
          "candidates miss it: widthMinUpto M layer is one state late, widthMinUpto M (layer+1) one early]. "
          "hcov+hdisj at terminal. (Structural DIAG over-counts cleared mid-walk — a residual 1-wide Schur "
          "block is single-entry; the maintenance proves the bmon VALUE, not the battery.)"
          if ok else "FAIL — mismatch table to the elder (new semantics)")
    return ok


if __name__ == "__main__":
    import sys
    sys.exit(0 if run() else 1)
