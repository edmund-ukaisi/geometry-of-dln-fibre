def minAdm(r,p):
    if r==0: return 0
    return min((r-t)**2+p*t for t in range(r+1))
def lam(r,p): return minAdm(r,p)/2.0

# Refinement 1: r=2 routing is predicate-driven (peel if lam 2 > p/2, else directMorse).
print("=== Refinement 1: r=2 routing (peel iff lam 2 > p/2) ===")
for p in range(1,9):
    L2=lam(2,p); h=p/2.0
    route = "PEEL" if L2>h else "directMorse"
    print(f"p={p}: lam(2,p)={L2:.2f} p/2={h:.1f} → r=2 routes {route}")
# controller claim: peel at p<=3, directMorse at p>=4
print()
# Refinement 2: c* = (p/2 + lam r)/2 is a strict interior point of (p/2, lam r) when lam r > p/2.
print("=== Refinement 2: c*=(p/2+lam r)/2 strictly inside (p/2, lam r), gap>=1/2 ===")
bad=[]
for p in range(1,9):
    for r in range(1,8):
        L=lam(r,p); h=p/2.0
        if L>h:
            cstar=(h+L)/2
            ok = (h < cstar < L)
            gap = L-h
            if not ok or gap < 0.5-1e-9: bad.append((r,p,L,h,cstar,gap))
print("violations (c* not strict interior, or gap<1/2):", bad if bad else "NONE — c* always valid, gap>=1/2")
# both lam r and p/2 are half-integers (minAdm integer /2), so their gap is a multiple of 1/2; >0 ⟹ >=1/2.
