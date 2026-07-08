"""
STEP-0 terminal count<->monomial bridge check (thread genm-sjbuild).

Question (the sharp risk r1predicate/Codex flagged):
  Is   1/2 * minAdm(remChain pi)  <=  monomialThreshold d (sharedDivisorExp) jac
  UNIFORM over ALL route terminals (all Case-1/Case-2 chart sequences)?

Architecture (from the banked regime lemmas RouteMSJCorankPure):
  - regime A  (c' > pq/2, W>0 STRICT): shift c' -> c'-pq/2, hand deeper core W to the IH
                (box-finiteness of the STRICTLY-shorter chain redChain t M).
  - regime B  (c' < pq/2, W>=0)       : Morse dominance, terminate (finite directly).
  - free-matrix base (2-node)          : sjBase1_freeMatrix, EXACT 1/2*M0*M1.
  - monomial terminal                  : sjLoss_terminal, threshold monomialThreshold(d,k,h);
                                          fires ONLY when W cannot be handed to the plain IH
                                          (rank-deficient deeper factor Q_b).

The soundness gate  minAdm M <= peelCharge M u + minAdm(redChain u M)  (LayerSplit_value_eq_minAdm)
makes the regime-A shift land the deeper exponent below the reduced threshold. So along any path that
uses ONLY regime A / regime B / free-matrix base, threshold = EXACTLY 1/2*minAdm and NO monomial
bridge is needed.
"""
from functools import lru_cache
import itertools

@lru_cache(None)
def minAdm(M):
    M = tuple(M); L = len(M) - 1
    if L == 0: return 0
    if L == 1: return M[0] * M[1]
    return min((M[0]-t)*(M[1]-t) + minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))

def redChain(t, M): return (t,) + tuple(M[2:])

def admBound(M, j): return min(M[0], M[1]) if j == 0 else M[j+1]
def is_adm(M, T):
    L = len(T)
    for j in range(L):
        if T[j] > admBound(M, j): return False
    for i in range(L):
        for j in range(L):
            if i <= j and T[j] > T[i]: return False
    return L < 1 or T[L-1] == 0
def adm_cone(M):
    L = len(M) - 1
    return [T for T in itertools.product(*[range(admBound(M, j)+1) for j in range(L)]) if is_adm(M, T)]
def Mval(M, T):
    s = 0
    for j in range(len(T)):
        tprev = M[0] if j == 0 else T[j-1]
        s += (tprev - T[j]) * (M[j+1] - T[j])
    return s

def trace(M):
    print(f"\n{'='*76}\nM={M}  minAdm={minAdm(M)}  (1/2*minAdm = {minAdm(M)/2})")
    mm = minAdm(M)
    binding = [T for T in adm_cone(M) if Mval(M, T) == mm]
    print(f"binding strata (Mval == minAdm): {binding}")
    for T in binding:
        print(f"\n  --- stratum T={T} ---")
        cur = M; layer = 0; charges = []; monomial_needed = False
        while len(cur) >= 3 and layer < len(T):
            t = T[layer]; p, q = cur[0]-t, cur[1]-t; chg = p*q
            charges.append(chg)
            red = redChain(t, cur)
            dwid = cur[2:]                       # widths strictly below node 1 of the current chain
            qb_rank = min(dwid) if dwid else 0   # generic rank of the deeper product Q_b
            # rank-deficient on the block iff Q_b cannot absorb all q free columns as an isotropic Morse:
            rank_def = (dwid != ()) and (qb_rank < q)
            regimeA_possible = (mm/2 > chg/2)    # exists c' in (pq/2, mm/2) -> regime A engaged
            flag = "RANK-DEFICIENT Q_b -> monomial descent" if rank_def else "full-rank Q_b -> regime-A clean"
            if rank_def and regimeA_possible: monomial_needed = True
            print(f"    L{layer+1}: peel t={t}, corank {p}x{q} (charge={chg}); "
                  f"deeper widths below node1={dwid}, generic Q_b rank={qb_rank}; {flag}")
            cur = red; layer += 1
        print(f"    terminal chain after peeling={cur}, minAdm(terminal)={minAdm(cur)}; "
              f"charges={charges} sum={sum(charges)} (=minAdm: {sum(charges)==mm})")
        print(f"    -> monomial-terminal bridge load-bearing on this stratum: {monomial_needed}")

for M in [(3,3,4), (2,2,2,2), (3,3,3,4)]:
    trace(M)
