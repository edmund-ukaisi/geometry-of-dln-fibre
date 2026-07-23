"""
seat-KILL's Q1/Q2/Q3 — the LAST-CLEAR-OF-LAYER termwise mechanism on the diagonal.

Decisive case: last clear of layer S=1 where layer 1 HAS uncleared columns (d_1 > widthMinUpto(2)), so
couplingClear does NOT zero A_1(·, uncleared col). Does the escaped-column (layer-2) coefficient c_m still
carry a CLEARED below-diagonal coupling factor in EVERY monomial (⟹ couplingClear kills it termwise, V3
holds), or does some escaped monomial read an uncleared column WITHOUT a coupling factor (⟹ V3 fails)?

Witnesses: (2,3,3,3) [seat-KILL's] and (2,4,4,2) [richer: 2 uncleared L1 cols, 2 escaped L2 cols].
Both: clear layer 0 (2 pivots) → rollover → clear layer 1 cols 0,1 (pivots (1,0,0),(1,1,1)); node (1,2)
is the last-clear child. widthMinUpto(1)=widthMinUpto(2)=2 for both.

couplingClear q = foldResid|_{couplingCoords=0}, couplingCoords = { A_L(r,c) : r>c, c a CLEARED col of L }.
At (1,2): layer 0 cols {0,1} cleared, layer 1 cols {0,1} cleared; UNCLEARED A_1(·,≥2) is NOT zeroed.

For a polynomial, "coeff|_{couplingCoords=0}=0" ⟺ "every monomial has a coupling factor" — zeroing a
variable subset never creates cancellation, so ideal-membership here IS monomial-wise (Q3 collapses to
termwise). Live question (Q1): is the escaped coeff IN ⟨couplingCoords⟩ given it reads the uncleared col.

Exit 0 = escaped-col coefficient vanishes under couplingClear for every slot on both witnesses.
"""
import sympy as sp
from cap_frontier_sufficiency import make, layerCoords, widthMinUpto, real_foldResid

def cc(d, S, J):
    cap = widthMinUpto(d, S)
    return {(L, r, c) for (L, r, c) in make(d)[1] if L == S and J <= r and J <= c and c < cap}

def run(d, l0_pivots=((0, 0, 0), (0, 1, 1)), show_termwise=False, label=""):
    N, u = make(d)
    # couplingClear keys on the STORED fan pivot (#82 / capstone-cert §0): each clear of pivot (a,b) at
    # layer L zeroes u_(L,r,b) for r>a. Diagonal pivot (a=b=cl) ⟹ below-diagonal; row-repeat ⟹ maybe ∅.
    edges = [
        ("case2", 0, 0, l0_pivots[0], cc(d, 0, 0), 1),   # (0,0)->(0,1)
        ("case2", 0, 1, l0_pivots[1], cc(d, 0, 1), 0),   # (0,1)->(0,2)
        ("rollover", 0, 2, (1, 0, 0), set(), 0),         # (0,2)->(1,0)
        ("case2", 1, 0, (1, 0, 0), cc(d, 1, 0), 1),      # (1,0)->(1,1)  δ=1
        ("case2", 1, 1, (1, 1, 1), cc(d, 1, 1), 0),      # (1,1)->(1,2)  δ=0  LAST CLEAR of layer 1
    ]
    resid = real_foldResid(u, d, edges)   # at (1,2)
    clear_pivots = [l0_pivots[0], l0_pivots[1], (1, 0, 0), (1, 1, 1)]   # the 4 case2 clears
    couplingCoords = set()
    for (pL, pa, pb) in clear_pivots:
        couplingCoords |= {(pL, r, pb) for r in range(d[pL + 1]) if r > pa}
    cleared_cols = {0: {0, 1}, 1: {0, 1}}
    uncleared_L1 = sorted(k for k in u if k[0] == 1 and k[2] not in cleared_cols[1])
    wmu2 = widthMinUpto(d, 2)
    escaped = sorted(k for k in u if k[0] == 2 and k[2] >= wmu2)
    zero_cpl = {u[k]: 0 for k in couplingCoords}
    print(f"\n=== d={d} {label}, node (1,2), {len(resid)} slots; couplingCoords={sorted(couplingCoords)} ===")
    print(f"  UNCLEARED L1 (not zeroed): {uncleared_L1};  escaped L2 (col>=wmu(2)={wmu2}): {escaped}")
    all_killed = True; reads_uncl_somewhere = False
    for j, f in enumerate(resid):
        f = sp.expand(f)
        for m in escaped:
            cm = sp.expand(f.coeff(u[m], 1))
            if cm == 0:
                continue
            killed = (sp.expand(cm.subs(zero_cpl)) == 0)
            ru = [k for k in uncleared_L1 if u[k] in cm.free_symbols]
            if ru: reads_uncl_somewhere = True
            all_killed = all_killed and killed
            if not killed:
                print(f"  slot[{j}] u_{m}: SURVIVES couplingClear = {sp.expand(cm.subs(zero_cpl))}")
    print(f"  reads uncleared L1 col somewhere? {reads_uncl_somewhere}  (seat-KILL's Q1 worry is real)")
    print(f"  every escaped coeff KILLED by couplingClear (V3 termwise)? {all_killed}")
    if show_termwise:
        f0 = sp.expand(resid[0])
        for m in escaped:
            cm = sp.expand(f0.coeff(u[m], 1))
            if cm != 0:
                print(f"  TERMWISE witness — slot0 coeff of u_{m}, per-monomial cleared-coupling factor:")
                for t in sp.Add.make_args(cm):
                    cpl = [k for k in couplingCoords if u[k] in t.free_symbols]
                    print(f"    {t}  -> {cpl}  {'OK' if cpl else '*** NONE (survives) ***'}")
                break
    return all_killed

print("### DIAGONAL fan (seat-KILL's hcanon scope) — expect V3 termwise TRUE")
ok1 = run((2, 3, 3, 3), show_termwise=True, label="[diagonal]")
ok2 = run((2, 4, 4, 2), label="[diagonal]")
print("\n### ROW-REPEAT fan (the #95 row-phantom, pivots at row 2) — expect V3 FALSE (boundary)")
okrp = run((2, 3, 3, 3), l0_pivots=((0, 2, 0), (0, 2, 1)), label="[row-repeat (0,2,0)+(0,2,1)]")
print(f"\nDIAGONAL V3 termwise holds? {ok1 and ok2}   ROW-REPEAT V3 holds? {okrp} (expected False = #95)")
assert ok1 and ok2, "V3 FAILS on a DIAGONAL witness — escaped col survives; seat-KILL must NOT render termwise"
assert not okrp, "row-repeat did NOT fail — #95 boundary not reproduced; re-examine couplingClear keying"
print("OK: DIAGONAL-scoped ⟹ escaped coeff ∈ ⟨couplingCoords⟩ MONOMIAL-WISE (termwise). ROW-REPEAT escapes"
      " (couplingClear keys on the stored pivot row; belowPivotCol=∅) — exactly why hcanon/diagonal is needed.")
