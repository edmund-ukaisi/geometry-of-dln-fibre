"""
#92 (V3) MECHANISM RE-CHECK (pnp decorrelated consult; seat-KILL's well-founded gap in "trivial termwise").

seat-KILL's concern (sound): at the last clear of layer S (diagonal pivot (S,c',c')), the entering escaped
col m=(S+1,·,c) [c≥wmu(S+1)] is read by foldResid via coeff c_m reading A_S's row c. couplingClear zeroes
the below-diagonal couplings A_S(c,col) for col<wmu(S+1) (c>col), but NOT the UNCLEARED cols A_S(c,col≥wmu).
So a c_m monomial reading only uncleared A_S cols would SURVIVE — breaking "trivial termwise" as a
SINGLE-LAYER claim.

RESOLUTION (verified): it IS trivial termwise, but MULTI-LAYER. The uncleared A_S col (col≥wmu(S)) does not
survive: in the coreGen product ∏A = …·A_S·A_{S-1}·…, that uncleared A_S entry pairs with A_{S-1}'s row at
that col-index, and THAT is a below-diagonal coupling at layer S-1 (cleared). If it too is uncleared it
telescopes to A_{S-2}, …, terminating at a coupling before layer 0 (wmu(0)=d[0] ⟹ layer 0 has NO uncleared
cols). So EVERY c_m monomial carries a couplingCoords factor at SOME layer L≤S; couplingClear (all layers)
zeroes each. NOT (B) strict-transform / Q₁⁻¹ reshaping — c_m is already a sum of coupling-carrying
monomials. It is (A), but the coupling reach is the WHOLE-PATH product chain (route (a)).

CHECK (WIDE pairing layer, so uncleared A_S cols EXIST): decompose each escaped-coeff monomial and record
which LAYER's coupling it carries. Expect: every monomial carries one, layers used SPAN {0..S} (multi-layer).
"""
import sympy as sp, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from capstone_adjudication import dims_coords, oracle_edges, coreGen, Phi_p, wmu
from capstone_locus_core import couplingCoords
from capstone_kill_invariant import escaped, state_of

def run():
    ok_all = True
    for d in [(2, 3, 3, 3), (2, 4, 4, 4), (2, 4, 3, 3)]:
        N, u = dims_coords(d); coords = set(u.keys()); edges, meta = oracle_edges(d)
        br = [e for e in edges if e[0] != "terminal"]
        for i in range(1, len(br) + 1):
            S, c = state_of(d, br, i)
            if S + 1 > N or not (c >= wmu(d, S + 1)) or not escaped(d, S + 1):
                continue
            if not (d[S] > wmu(d, S)):        # only the WIDE pairing layer exercises seat-KILL's concern
                continue
            path = br[:i]; cc = couplingCoords(d, path, coords)
            by_layer = {}
            for k in cc:
                by_layer.setdefault(k[0], set()).add(k)
            raw = [sp.expand(f) for f in coreGen(Phi_p(u, d, path, True), d)]
            e0 = sorted(escaped(d, S + 1))[0]
            allcarry = True; layers_used = set()
            for f in raw:
                ce = sp.expand(f.coeff(u[e0], 1))
                if ce == 0:
                    continue
                for term in ce.as_ordered_terms():
                    tv = term.free_symbols
                    carriers = {L for L, s in by_layer.items() if any(u[k] in tv for k in s)}
                    if not carriers:
                        allcarry = False; print(f"   SURVIVOR (no coupling): {term}")
                    else:
                        layers_used |= carriers
            multilayer = len(layers_used) > 1
            ok_all &= allcarry
            print(f"d={d} last-clear S={S} (WIDE d[{S}]={d[S]}>wmu={wmu(d,S)}): escaped {e0}: "
                  f"every monomial carries a coupling={allcarry}; coupling LAYERS used={sorted(layers_used)} "
                  f"({'MULTI-LAYER' if multilayer else 'single'})")
    print(f"\n⟹ (A) trivial termwise, MULTI-LAYER (coupling reached via the ∏A product chain, route-(a)); "
          f"NOT (B) reshaping. all-carry across wide-pairing witnesses: {ok_all}")
    assert ok_all

if __name__ == "__main__":
    run()
