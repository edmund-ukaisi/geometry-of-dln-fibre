"""Thread 08 — pin codimForm split in the EXACT landed-Lean indexing.

Lean target:
  codimForm (N+1) (extendℤ m)
      = codimForm N (extendℤ (peelPart m)) + Δ
with  m : Fin (N+2) × Fin (N+2) → ℕ   (indices 0..N+1).

Lean defs (mirrored, ℤ-indexed exactly):
  codimForm K M = Σ_{1≤i≤u≤j≤v≤K} M(i-1,j-1) * M(u,v)            -- K nested Icc over ℤ
  extendℤ m a b = m(a,b)  if 0≤a≤b≤(box bound)  else 0
       ( for codimForm (N+1): box bound = N+1 ;  for codimForm N: box bound = N )
  peelPart m (I,J) :  Fin(N+1)×Fin(N+1)→ℕ
       J=last N    -> m(I,N)+m(I,N+1)         (merge old col N+1 into col N)
       J=j0<N      -> m(I,j0)                 (untouched)

CONTROLLER'S Δ (verify):  Δ = Σ_{0≤a<u≤N+1} (extendℤ m) a N * (extendℤ m) u (N+1)
   i.e. b_a - x_a = m_{a,N},  x_u = m_{u,N+1}.

We verify, exactly (ints), over many m on Fin(N+2) (N=1,2,3, monotone + non-monotone +
NOT necessarily Kostant — the split is a pure polynomial identity in the entries, must hold
for arbitrary nonneg m supported on i<=j as well as fully arbitrary m).
"""
import sys
from itertools import product as iproduct

def codimForm(K, M):
    # M is a callable (a,b)->int (already zero-padded outside box)
    s = 0
    for i in range(1, K+1):
        for u in range(i, K+1):
            for j in range(u, K+1):
                for v in range(j, K+1):
                    s += M(i-1, j-1) * M(u, v)
    return s

def extend(mdict, bound):
    def M(a, b):
        if 0 <= a <= b <= bound:
            return mdict.get((a, b), 0)
        return 0
    return M

def peelPart(N, m):
    # m: dict on Fin(N+2)^2 ; returns dict on Fin(N+1)^2
    mp = {}
    for I in range(N+1):
        for J in range(N+1):
            if J == N:                       # last column of the smaller form
                v = m.get((I, N), 0) + m.get((I, N+1), 0)
            else:
                v = m.get((I, J), 0)
            if v:
                mp[(I, J)] = v
    return mp

def delta_controller(N, m):
    # Δ = Σ_{0≤a<u≤N+1} m(a,N) * m(u,N+1)
    M = extend(m, N+1)
    s = 0
    for a in range(N+2):
        for u in range(a+1, N+2):
            s += M(a, N) * M(u, N+1)
    return s

def random_ms(N, rng, count, cap=3, triangular=True, allow_arbitrary=False):
    import random
    R = random.Random(rng)
    out = []
    cells = [(a, b) for a in range(N+2) for b in range(N+2)
             if (a <= b or not triangular)]
    for _ in range(count):
        m = {}
        for c in cells:
            v = R.randint(0, cap)
            if v:
                m[c] = v
        out.append(m)
    return out

def main():
    fail = 0
    cntD = 0   # Δ-formula tied to split
    cntS = 0   # split-correctness (the identity itself)
    # Exhaustive-ish small + random over N=1,2,3
    configs = [
        (1, 5000, 3, True),
        (1, 3000, 4, False),   # non-triangular (fully arbitrary entries)
        (2, 6000, 3, True),
        (2, 3000, 3, False),
        (3, 4000, 2, True),
        (3, 2000, 2, False),
    ]
    for (N, count, cap, tri) in configs:
        for m in random_ms(N, hash((N, count, cap, tri)) & 0xffff, count, cap, tri):
            big = codimForm(N+1, extend(m, N+1))
            small = codimForm(N, extend(peelPart(N, m), N))
            delta = delta_controller(N, m)
            cntS += 1
            if big != small + delta:
                fail += 1
                if fail < 20:
                    print(f"SPLIT FAIL N={N} m={m}  big={big} small={small} Δ={delta}")
    # Targeted non-monotone Kostant-flavoured hand cases (entries that vary across columns)
    hand = [
        (1, {(0,0):2,(0,1):1,(1,1):3}),
        (1, {(0,0):0,(0,1):5,(1,1):0}),
        (2, {(0,0):1,(0,1):2,(0,2):3,(1,1):1,(1,2):2,(2,2):4}),
        (2, {(0,2):7,(1,1):2,(2,2):1}),                 # corner-heavy
        (3, {(0,0):1,(0,3):2,(1,2):3,(2,3):1,(3,3):5}),  # sparse non-monotone
        (3, {(0,1):2,(0,2):1,(0,3):4,(1,3):2,(2,2):3,(3,3):1}),
    ]
    for (N, m) in hand:
        big = codimForm(N+1, extend(m, N+1))
        small = codimForm(N, extend(peelPart(N, m), N))
        delta = delta_controller(N, m)
        cntD += 1
        if big != small + delta:
            fail += 1
            print(f"HAND FAIL N={N} m={m}  big={big} small={small} Δ={delta}")
    print("=== thread-08 codimForm-split certificate (exact int, Lean indexing) ===")
    print(f"  split checks (random, tri+arbitrary): {cntS}")
    print(f"  hand non-monotone checks:             {cntD}")
    print("ALL OK" if fail == 0 else f"{fail} FAILURES")
    return fail

if __name__ == "__main__":
    sys.exit(1 if main() else 0)
