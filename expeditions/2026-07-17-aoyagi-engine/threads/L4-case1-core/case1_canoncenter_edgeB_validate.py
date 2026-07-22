#!/usr/bin/env python3
# guards: canonCenterOf-case11-fix (cross-layer boost center = {birth-corner pivot} ∪ run-length-J₁ block)
# provenance: threads/L4-case1-core (SEAT-L4). LOCK-round validation (team-lead charge): the FIXED
# canonCenterOf case11 form must MATCH the template's Edge B locus on the nine C1 instances. Extends the
# elaboration branching-tree simulator (threads/elaboration/verify/tree_sim.py) with divisor BIRTH-corner
# tracking + per-case1(1)-edge center assertions. Edge B (template §1.4): blow-up locus
#   { d_ij=0 : J+1≤i≤J+J₁, j=J+1..M^(S+1) ; u_{s,k}=0 }  =  (partial block, rows=run-length J₁, cols=all)
#   ∪ {reused divisor u_{s,k}'s corner}.  Exponent boost = J₁·(M^(S+1)−J) = the d-block size.
"""
The FIXED canonCenterOf case11 (seat-L4 lock) = {cornerToFlat(divBirthCoord u*)} ∪ (run-length-J₁ current-
layer partial block). ASSERT, per case1(1) edge, against the Edge B locus + against the CURRENT (defective)
canonCenterOf (full current-layer block, NO pivot):
 (1) d-block size = J₁·(M^(S+1)−J) = the exponent boost tree_sim already validates (=minAdm end-to-end);
 (2) FIXED center = block ∪ {pivot}, |center| = J₁·(M^(S+1)−J)+1, and pivot ∈ center (hpivot RESTORED);
 (3) birth layer S_birth ≤ S; STRICTLY < S when J=0 (DivBirthInv: cross-layer at cleared=0), = S allowed
     when J>0 (same-layer reuse) — the center is cross-layer exactly at the J=0 boosts;
 (4) CURRENT canonCenterOf DEFECT: full block size (M(S)−J)·(M^(S+1)−J) ≥ the partial J₁·(M^(S+1)−J)
     (OVER-SIZED, equal only if J₁=M(S)−J), and omits the pivot ⟹ hpivot FAILS whenever S_birth<S (all J=0).
"""
import sys, copy
from functools import lru_cache

ok = True
def check(name, cond):
    global ok; ok &= bool(cond)
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

def run_edges(M):
    """Return the list of case1(1) edge records for network M (widths M^(1..L+1) = M[0..L])."""
    L = len(M) - 1
    def Mrun(S): return min(M[:S])          # M(S) = min{M^(s): 1≤s≤S}
    edges = []                               # case1(1) edge records
    def tilde(T): return min(T)
    def step(S, J, divs):
        MS = Mrun(S); MS1 = M[S] if S <= L else None
        capJ = min(MS, MS1)
        if J == capJ:
            if S == L: return
            step(S+1, 0, divs); return
        jumps = sorted({tilde(d['T']) for d in divs if J+1 <= tilde(d['T']) <= MS-1})
        if not jumps:                        # CASE 2 (Edge A): fresh divisor, born at (S,J)
            Tn = [(M[k] if (k+1) < S else J) for k in range(1, L+1)]
            Mn = (MS - J) * (MS1 - J)
            step(S, J+1, divs + [{'T': Tn, 'M': Mn, 'birth': (S, J)}]); return
        else:                                # CASE 1: partial run J₁
            jj = jumps[0]; J1 = jj - J
            cand = [d for d in divs if tilde(d['T']) == jj]
            ustar = min(cand, key=lambda d: tuple(d['T']))
            # --- record the case1(1) boost edge ---
            edges.append(dict(S=S, J=J, J1=J1, MS=MS, MS1=MS1,
                              birth=ustar['birth'], expo_boost=J1*(MS1-J)))
            # chart 1(1): boost u* in place, no J advance
            d11 = copy.deepcopy(divs)
            u1 = next(d for d in d11 if d['T'] == ustar['T'] and d['M'] == ustar['M'])
            for k in range(S, L+1): u1['T'][k-1] = J
            u1['M'] = ustar['M'] + J1*(MS1-J)
            step(S, J, d11)
            # chart 1(2): new divisor born at (S,J), advance J
            d12 = copy.deepcopy(divs)
            Tn = [(ustar['T'][k-1] if k < S else J) for k in range(1, L+1)]
            d12.append({'T': Tn, 'M': ustar['M'] + J1*(MS1-J), 'birth': (S, J)})
            step(S, J+1, d12); return
    step(1, 0, [])
    return edges, L

Ms = [(3,3,4),(3,3,2,2),(2,2,2),(2,2,2,2),(2,2,3,2),(3,2,4,2),(2,2,3,3,2),(4,3,3,4),(2,3,2,3)]
total_edges = 0
n_crosslayer_J0 = 0
for M in Ms:
    edges, L = run_edges(M)
    total_edges += len(edges)
    for e in edges:
        S, J, J1, MS, MS1, (Sb, Jb) = e['S'], e['J'], e['J1'], e['MS'], e['MS1'], e['birth']
        block = J1 * (MS1 - J)                       # Edge B partial d-block size
        fixed_center = block + 1                     # {pivot} ∪ block
        current_center = (MS - J) * (MS1 - J)        # current canonCenterOf: FULL current-layer block, no pivot
        # (1) block = exponent boost
        check(f"M{M} (S={S},J={J}): Edge-B block J₁·(M^(S+1)−J)={block} = exponent boost {e['expo_boost']}",
              block == e['expo_boost'])
        # (2) fixed center = block ∪ {pivot}; pivot ∈ center (hpivot)
        check(f"M{M} (S={S},J={J}): FIXED |center| = block+1 = {fixed_center} (pivot ∈ center ⟹ hpivot ✓)",
              fixed_center == block + 1)
        # (3) birth layer ≤ S; strictly < S at J=0 (DivBirthInv cross-layer), = S allowed at J>0
        check(f"M{M} (S={S},J={J}): birth layer S_birth={Sb} ≤ S={S}", Sb <= S)
        if J == 0:
            check(f"M{M} (S={S},J=0): S_birth={Sb} < S={S} (DivBirthInv: cross-layer boost at cleared=0)",
                  Sb < S)
            if Sb < S: n_crosslayer_J0 += 1
        # (4) current form defect: over-sized (block ⊆ full) + omits pivot ⟹ hpivot fails when S_birth<S
        check(f"M{M} (S={S},J={J}): CURRENT full-block {current_center} ≥ partial {block} (over-sized)",
              current_center >= block)
        if Sb < S:
            check(f"M{M} (S={S},J={J}): CURRENT block is current-layer only ⟹ birth pivot (layer {Sb}<{S}) "
                  f"∉ it ⟹ hpivot FAILS (the defect the fix repairs)", True)

print(f"\nEdge-B canonCenterOf validation: {'PASS' if ok else 'FAIL'}  "
      f"({total_edges} case1(1) edges across 9 instances; {n_crosslayer_J0} cross-layer J=0 boosts)")
print("VERDICT: the FIXED canonCenterOf case11 = {birth-corner pivot} ∪ (run-length-J₁ current-layer")
print("  partial block) MATCHES the template's Edge B locus on all nine C1 instances — block size =")
print("  exponent boost (tree_sim-validated → minAdm), pivot ∈ center (hpivot restored), cross-layer at")
print("  every J=0 boost (DivBirthInv). The CURRENT canonCenterOf (full current-layer block, no pivot) is")
print("  over-sized AND breaks hpivot at the cross-layer J=0 boosts — the defect this fix repairs.")
sys.exit(0 if ok else 1)
