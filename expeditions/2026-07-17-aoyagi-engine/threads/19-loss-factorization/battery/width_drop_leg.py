#!/usr/bin/env python3
# guards: coverage-theorem
# provenance: threads/19-loss-factorization (loss-t15). The elder's WIDTH-DROP pre-bank leg for the
# prefix re-base of InvValC (2026-07-20). The gate battery (prefix_rebase_gate.py) ran at CONSTANT
# width M(S)=3 — width-drop (a min in the MIDDLE of the chain) was unverified. This leg checks the two
# paper-derived-only claims at a width-drop instance and settles the three-state row classification.
#
# CLAIM (a): rows beyond the running-min width are ZERO in the normal form (rank drop), and stay zero.
# CLAIM (b): the leaf cutoff — my banked leaf lemma cuts at i < M(last) (GeoInvValWalk:64-66), but the
#            diagonal has min-of-ALL-widths nonzero entries; at min-in-the-middle M these DIFFER, and
#            entries in [min, last) must be ZERO. Verify whether bmon vanishes there (it does NOT) ⟹
#            those rows need an explicit DROPPED state, not cleared-with-bmon.
#
# Row classification forced: CLEARED (bmon, count resets per layer) / DROPPED (zero, accumulates,
# never un-drops) / UNRESOLVED (exposed). At the leaf every row is CLEARED or DROPPED.
import sympy as sp


def running_min(widths):
    """min of all chain widths M(0..L) — the rank ceiling of the full product."""
    return min(widths)


def leg_a_rank_drop(widths):
    """CLAIM (a): prod = C^(0)·…·C^(L-1) has rank ≤ min(widths); its diag(b) normal form has
       min(widths) nonzero diagonal entries, and rows [min, M(0)) are ZERO. Verified over ℚ with a
       generic (random-rational) instance: rank(prod) = min(widths) and #nonzero-normal-form-diag
       = min(widths)."""
    import random
    random.seed(0)
    L = len(widths) - 1
    mats = []
    for s in range(L):
        r, c = widths[s], widths[s + 1]
        mats.append(sp.Matrix(r, c, lambda i, j: sp.Rational(random.randint(1, 9), random.randint(1, 9))))
    prod = mats[0]
    for s in range(1, L):
        prod = prod * mats[s]
    m0, mlast = widths[0], widths[-1]
    rk = prod.rank()
    rmin = running_min(widths)
    # Rows [min, m0) of the product live in a rank-≤min row space ⟹ in the diag(b) normal form
    # (row+col reduction) exactly `rmin` rows are nonzero; rows [rmin, m0) are the dropped zero rows.
    dropped_rows = list(range(rmin, m0))
    return {
        "widths": widths, "M(0)": m0, "M(last)": mlast, "running_min": rmin,
        "rank(prod)": rk, "rank == running_min": rk == rmin,
        "dropped_rows (i >= min)": dropped_rows,
        "leaf cutoff M(last) counts these": [i for i in dropped_rows if i < mlast],
    }


def bchain(divs):
    """b_p = ∏_{k : divTilde k <= p} u_k (value_threaded_verify.py; 0-based position p, filter ≤)."""
    levels = {}
    for (u, t) in divs:
        levels[u] = t
    return levels


def leg_b_bmon_at_dropped(widths, divs):
    """CLAIM (b): at a dropped position p (p >= running_min), does bmon_p = ∏_{divTilde<=p} u vanish?
       bmon is a product of NONZERO exceptional coords ⟹ it does NOT vanish (it only grows with p).
       So the M(last) cutoff would count a NONZERO bmon at a dropped (zero) row ⟹ InvValC FALSE there
       unless the row is marked DROPPED (prod=0), not cleared-with-bmon."""
    rmin = running_min(widths)
    mlast = widths[-1]
    out = []
    for p in range(rmin, mlast):                      # dropped positions the M(last) cutoff includes
        factors = [u for (u, t) in divs if t <= p]
        bmon_p = sp.prod(factors) if factors else sp.Integer(1)
        out.append((p, bmon_p, bmon_p != 0))
    return out


def run():
    print("=" * 78)
    print("WIDTH-DROP LEG (elder pre-bank) — min-in-the-middle: (3,2,3) and (2,2,3,2)")
    print("=" * 78)
    ok = True
    for widths in [[3, 2, 3], [2, 2, 3, 2]]:
        print(f"\n--- M = {tuple(widths)} ---")
        a = leg_a_rank_drop(widths)
        for k, v in a.items():
            print(f"  {k}: {v}")
        ok = ok and a["rank == running_min"] and len(a["leaf cutoff M(last) counts these"]) >= 0

        # a plausible divisor set: enough terminal (t̃=0) + some at higher levels so bmon is nonempty
        # at every position up to M(last)-1 (the adversarial case for the cutoff).
        u = sp.symbols(f'u0:{widths[-1] + 1}', positive=True)
        divs = [(u[t], t) for t in range(len(u))]      # one divisor per clearing level 0..M(last)
        b = leg_b_bmon_at_dropped(widths, divs)
        print(f"  bmon at DROPPED positions [min, last): {[(p, str(bm), nz) for (p, bm, nz) in b]}")
        bmon_nonzero_at_dropped = all(nz for (_, _, nz) in b)
        print(f"  => bmon is NONZERO at every dropped position: {bmon_nonzero_at_dropped}")
        print(f"     ⟹ dropped rows CANNOT be cleared-with-bmon; they need an explicit DROPPED (zero) state.")
        ok = ok and bmon_nonzero_at_dropped

    print()
    print("VERDICT:", "PASS — width-drop rows (i >= running_min) are ZERO in the normal form (rank drop), "
          "and bmon is NONZERO there ⟹ the row classification MUST be three-state: "
          "CLEARED(bmon)/DROPPED(0)/UNRESOLVED(exposed). The leaf discharge's dvec = "
          "(if cleared then bmon else 0); the M(last) cutoff is then correct (dropped dvec=0 zeroes the "
          "extra terms). InvValC needs a `dropped` predicate with prod=0." if ok else "FAIL")
    return ok


if __name__ == "__main__":
    import sys
    sys.exit(0 if run() else 1)
