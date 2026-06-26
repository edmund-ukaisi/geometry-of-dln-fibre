"""Pin minAdm/Mval indexing against the three Lean-known values:
   minAdm(3,3,4)=8, minAdm(4,4,2,2)=4, minAdm(3,3,3,3)=6."""
from itertools import product

def Mval_and_minAdm(M, formula):
    L = len(M) - 1
    best = None
    rngs = [range(0, max(M)+1) for _ in range(L-1)]
    for inner in product(*rngs):
        t = [M[0]] + list(inner) + [0]
        # admissibility: weakly decreasing, t[s] <= M[s] for the relevant widths
        if not all(t[s] >= t[s+1] for s in range(L)):
            continue
        if not formula['adm'](M, t, L):
            continue
        val = formula['val'](M, t, L)
        if best is None or val < best[0]:
            best = (val, tuple(t))
    return best

# Candidate A: codim at boundary s (1..L) uses widths (M[s-1] rows, M[s] cols), rank t[s].
#   Mval = sum_{s=1}^{L} (t[s-1]-t[s]) * (M[s]-t[s]),  with t admissible t[s] <= min(t[s-1], M[s]).
fA = {
  'adm': lambda M,t,L: all(t[s] <= min(t[s-1], M[s]) for s in range(1,L+1)) and t[L]==0 and t[0]==M[0],
  'val': lambda M,t,L: sum((t[s-1]-t[s])*(M[s]-t[s]) for s in range(1,L+1)),
}
# Candidate B: same but col-width M[s-1]? try (M[s-1]-t[s]) variant
fB = {
  'adm': lambda M,t,L: all(t[s] <= min(t[s-1], M[s]) for s in range(1,L+1)) and t[L]==0 and t[0]==M[0],
  'val': lambda M,t,L: sum((t[s-1]-t[s])*(M[s-1]-t[s]) for s in range(1,L+1)),
}

for name,f in [('A',fA),('B',fB)]:
    print(f"--- formula {name} ---")
    for M in [[3,3,4],[4,4,2,2],[3,3,3,3],[4,4,3],[2,2,2],[5,3,4]]:
        print(f"  minAdm{tuple(M)} =", Mval_and_minAdm(M,f))
