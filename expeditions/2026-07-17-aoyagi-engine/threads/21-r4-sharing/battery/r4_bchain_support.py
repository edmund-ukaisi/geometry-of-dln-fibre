#!/usr/bin/env python3
# guards: r4-sharing (support derivability)
# provenance: threads/21-r4-sharing/cert-r4-sharing-design.md §1-§2
"""R4 field-design cert — the support-derivability facts (D1, D2, D3).

The design question: is the generator->divisor sharing (`genDivExp`/`support`) INDEPENDENT
data that must be transported across the per-divisor re-indexing, or a DERIVED function of the
`divProfile` (via `divTilde`) already carried at R1?

Exact symbolic (sympy). Three facts, each exit-0 on success:

  D1  b-chain support formula. Solving Aoyagi's recursion b_0=1, b_i = (∏_{t̃=i-1} u)·b_{i-1}
      (worked.tex:484) gives b_i = ∏_{t̃_k < i} u_k, EACH DIVISOR TO POWER EXACTLY 1. So
      support(b_i) = {k : t̃_k < i} — a function of the divisors' t̃ levels only.

  D2  row-determines-content. In the invariant diag(b_1,…,b_m)·[E_J | D_J]·∏C, a loss generator
      in matrix-row i has divisor content EXACTLY b_i, INDEPENDENT of its column (D_J·∏C is a
      divisor-free ratio block). So support(generator in row i) = support(b_i) = {k : t̃_k < i}.

  D3  discrimination (the g-delta-flatten guard). "One divisor shared across two rows" and
      "two divisors, one per row" have DIFFERENT divProfile ledgers — so deriving support from
      divProfile loses NO information (the ⟨δx,δy⟩ vs ⟨δ1 x,δ2 y⟩ distinction survives).
"""
import sys
import sympy as sp

FAILS = []


def check(name, cond, detail=""):
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}" + (f"  — {detail}" if detail else ""))
    if not cond:
        FAILS.append(name)


# ---------------------------------------------------------------------------
# The paper's b-chain recursion, run symbolically over exceptional coords u_k.
# divisors : list of (name, t_tilde). numB = M(S) diagonal cells, indexed i = 1..numB.
# ---------------------------------------------------------------------------
def build_bchain(divisors, numB):
    """Return [b_1, ..., b_numB] as sympy monomials, via b_i = (∏_{t̃=i-1} u)·b_{i-1}, b_0=1."""
    us = {nm: sp.Symbol(nm, positive=True) for nm, _ in divisors}
    b = [sp.Integer(1)]  # b_0
    for i in range(1, numB + 1):
        factor = sp.Integer(1)
        for nm, tt in divisors:
            if tt == i - 1:
                factor *= us[nm]
        b.append(sp.simplify(factor * b[i - 1]))
    return b[1:], us  # drop b_0


def support_symbolic(monomial, us):
    """Which u's actually divide the monomial, with multiplicity (from the sympy expression)."""
    d = sp.Poly(monomial, *us.values()).as_dict() if monomial != 1 else {}
    if not d:
        return {}
    (expvec, _), = d.items()  # a single monomial term
    return {nm: e for nm, e in zip(us.keys(), expvec) if e != 0}


def support_predicted(divisors, i):
    """The divProfile-derived prediction: {k : t̃_k < i}."""
    return {nm for nm, tt in divisors if tt < i}


print("=" * 72)
print("D1  b-chain support formula: b_i = ∏_{t̃_k < i} u_k, exponents ∈ {0,1}")
print("=" * 72)
# Exercise several divisor configurations, incl. equal runs (repeated t̃) and gaps.
configs = [
    ("simple chain",      [("u0", 0), ("u1", 1), ("u2", 2)], 3),
    ("equal run len 2",   [("u0", 0)],                        2),  # t̃=0 only, m=2 -> b1=b2=u0
    ("gap at level 1",    [("u0", 0), ("u2", 2)],             3),  # no divisor at t̃=1
    ("shared 2x2 block",  [("d", 0)],                         2),  # the corank-2 coupling: b1=b2=d
    ("mixed",             [("a", 0), ("b", 0), ("c", 2)],     4),  # two at level 0, one at 2
]
for label, divs, numB in configs:
    bs, us = build_bchain(divs, numB)
    ok_all = True
    for i in range(1, numB + 1):
        sup = support_symbolic(bs[i - 1], us)
        pred = support_predicted(divs, i)
        exps_binary = all(e == 1 for e in sup.values())
        sup_matches = set(sup.keys()) == pred
        ok_all = ok_all and exps_binary and sup_matches
    check(f"D1 {label}", ok_all,
          f"b={[str(x) for x in bs]}  (each u exp=1, support={{k:t̃<i}})")

# The divisibility chain (bChain : Monotone bExp): support(b_i) ⊆ support(b_{i+1}).
for label, divs, numB in configs:
    bs, us = build_bchain(divs, numB)
    mono = all(set(support_symbolic(bs[i - 1], us)).issubset(set(support_symbolic(bs[i], us)))
               for i in range(1, numB))
    check(f"D1-chain {label}", mono, "support(b_i) ⊆ support(b_{i+1}) (bChain monotone)")

print()
print("=" * 72)
print("D2  row-determines-content: generator in row i has divisor content = b_i (col-indep)")
print("=" * 72)
# Build diag(b) · D  where D is a symbolic divisor-FREE ratio block; read off divisor content
# per entry and confirm it is constant along each row = b_i.
for label, divs, numB in [("2x2 shared (corank-2)", [("d", 0)], 2),
                          ("3-row mixed", [("a", 0), ("b", 0), ("c", 2)], 4)]:
    bs, us = build_bchain(divs, numB)
    ncol = 3
    # regular ratio coords (divisor-free), distinct symbols
    D = sp.Matrix(numB, ncol, lambda r, c: sp.Symbol(f"g_{r}_{c}"))
    G = sp.diag(*bs) * D
    row_const = True
    matches_b = True
    for r in range(numB):
        row_sups = []
        for c in range(ncol):
            entry = G[r, c]
            # divisor content = exponents of the u's in this entry (ratio coords carry none)
            row_sups.append(support_symbolic(sp.simplify(entry / D[r, c]), us))
        # constant along the row?
        row_const = row_const and all(s == row_sups[0] for s in row_sups)
        # equals support(b_{r+1})?
        matches_b = matches_b and (set(row_sups[0].keys()) == set(support_symbolic(bs[r], us).keys()))
    check(f"D2 {label} col-independence", row_const, "divisor content constant along each row")
    check(f"D2 {label} = b_i", matches_b, "row-i content = support(b_i)")

print()
print("=" * 72)
print("D3  discrimination: shared vs split have DIFFERENT divProfile ledgers")
print("=" * 72)
# Model the two archetypes as leaf b-chains over a 2-cell diagonal (corank-2 residual):
#   SHARED  : one divisor d at t̃=0, no divisor at t̃=1  -> b1=b2=d  (⟨δx,δy⟩ archetype)
#   SPLIT   : two divisors d1 (t̃=0), d2 (t̃=1)          -> b1=d1, b2=d1·d2 (⟨δ1x,δ2y⟩ archetype)
shared = [("d", 0)]
split = [("d1", 0), ("d2", 1)]
bs_shared, us_s = build_bchain(shared, 2)
bs_split, us_p = build_bchain(split, 2)
# divProfile ledger fingerprint = the multiset of t̃ levels (+ divisor count)
fp_shared = (len(shared), sorted(tt for _, tt in shared))
fp_split = (len(split), sorted(tt for _, tt in split))
check("D3 different ledgers", fp_shared != fp_split,
      f"shared numDiv/t̃ = {fp_shared}  vs  split = {fp_split}")
check("D3 shared coupling", set(support_symbolic(bs_shared[0], us_s)) ==
      set(support_symbolic(bs_shared[1], us_s)),
      f"b1={bs_shared[0]}, b2={bs_shared[1]} (rows share d)")
check("D3 split no-coupling", set(support_symbolic(bs_split[0], us_p)) !=
      set(support_symbolic(bs_split[1], us_p)),
      f"b1={bs_split[0]}, b2={bs_split[1]} (rows differ)")

print()
if FAILS:
    print(f"FAILURES: {FAILS}")
    sys.exit(1)
print("ALL PASS — support is a DERIVED function of divProfile (via divTilde) + row-index.")
sys.exit(0)
