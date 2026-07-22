from itertools import product

def runMin(M, j):
    # runMin M j = min(M[0..j+1])
    return min(M[i] for i in range(j+2))

def Mval(M, T):
    L = len(T)
    s = 0
    for j in range(L):
        tprev = M[0] if j == 0 else T[j-1]
        s += (tprev - T[j]) * (M[j+1] - T[j])
    return s

def clamp(M, T):
    L = len(T)
    return tuple(min(T[j], runMin(M, j)) for j in range(L))

# admPred: weak-decrease, last = 0, T_j <= admBound
def admBound(M, j):
    return min(M[0], M[1]) if j == 0 else M[j+1]

def admissible(M, T):
    L = len(T)
    if any(T[j] > admBound(M, j) for j in range(L)): return False
    for i in range(L):
        for j in range(i, L):
            if T[j] > T[i]: return False
    if L >= 1 and T[L-1] != 0: return False
    return True

def test(maxL, maxW, maxT, adm_only):
    fails = 0
    total = 0
    fail_examples = []
    for L in range(1, maxL+1):
        for M in product(range(maxW+1), repeat=L+1):
            for T in product(range(maxT+1), repeat=L):
                if adm_only and not admissible(M, T):
                    continue
                total += 1
                Tc = clamp(M, T)
                if Mval(M, Tc) > Mval(M, T):
                    fails += 1
                    if len(fail_examples) < 10:
                        fail_examples.append((M, T, Tc, Mval(M,T), Mval(M,Tc)))
    return total, fails, fail_examples

print("=== UNCONDITIONAL (all T in range) ===")
tot, f, ex = test(3, 4, 4, adm_only=False)
print(f"L<=3, W<=4, T<=4: {tot-f}/{tot} pass, {f} fails")
for e in ex: print("  FAIL", e)

print("=== ADM-ONLY ===")
tot, f, ex = test(3, 4, 4, adm_only=True)
print(f"L<=3, W<=4, T<=4 (adm): {tot-f}/{tot} pass, {f} fails")
for e in ex: print("  FAIL", e)
