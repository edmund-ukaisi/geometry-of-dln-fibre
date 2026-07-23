import sympy as sp, sys, os
sys.path.insert(0, os.path.abspath('.'))
from capstone_adjudication import dims_coords, oracle_edges, coreGen, Phi_p, wmu, blockCoords
from capstone_locus_core import couplingCoords, couplingClear
from capstone_kill_invariant import layerCoords, escaped, state_of, ignored_set

def run(d):
    N, u = dims_coords(d); coords = set(u.keys()); edges, meta = oracle_edges(d)
    br = [e for e in edges if e[0] != "terminal"]
    print(f"\n=== d={d}: at each node, is escaped(S+1) IGNORED by sourceClearedResid? ===")
    for i in range(len(br) + 1):
        S, c = state_of(d, br, i)
        if S + 1 > N - 1:   # escaped(S+1) empty when S+1 >= N
            continue
        escS1 = escaped(d, S + 1)
        if not escS1:
            continue
        ign = ignored_set(d, br[:i], u, coords)
        cc = couplingCoords(d, br[:i], coords)
        lab = br[i-1][0] if i > 0 else "root"
        wmuS1 = wmu(d, S + 1)
        inZ = (c >= wmuS1)   # is escaped(S+1) in pnp's Z at this node?
        print(f"  node{i:2d}[{lab:8s}] S={S} c={c} wmu(S+1)={wmuS1}: escaped(S+1={S+1})⊆ignored={escS1 <= ign}"
              f"   (in pnp-Z? {inZ})   |couplings|={len(cc)}")
for d in [(2,3,3,3),(2,4,4,2)]:
    run(d)
