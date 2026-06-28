# Codex's confound: the firing splits on c' vs p/2.
#   peel branch (carve fires): p/2 < c' < lam(r)   — needs lam(r) > p/2
#   direct-Morse branch:       0 < c' <= p/2        — closes without recursion
# Question: do these two branches COVER (0, lam r) for every (r,p)? And WHEN is the peel range empty?
def minAdm(r,p):
    if r==0: return 0
    return min((r-t)**2 + p*t for t in range(r+1))
def lam(r,p): return minAdm(r,p)/2.0

print("r p | lam(r,p)  p/2 | peel-range (p/2,lam) nonempty?  cap-B-binding(lam<=p/2)?")
for p in range(1,9):
    for r in range(1,7):
        L=lam(r,p); h=p/2.0
        peel_ne = h < L
        capB_bind = L <= h
        # sanity: the two branches (0,p/2] and (p/2,L) cover (0,L) iff always (trivially yes by def)
        print(f"{r} {p} | {L:6.2f}  {h:4.1f} | peel {'Y' if peel_ne else 'EMPTY':5} | capB-bind {'Y' if capB_bind else '.'}")
    print()

# Where does the carve's hc2: '2<c'' at p=4 correspond? p/2=2. And r=2: lam=2=p/2 → peel range (2,2) EMPTY,
# r=2 uses the base (c'<2 = direct/non-carve). r>=3: lam>2=p/2 → peel nonempty, carve fires. MATCHES dispatch.
print("p=4 check: r=2 lam=",lam(2,4)," p/2=2 → peel range (2,2) empty (base); r=3 lam=",lam(3,4)," → peel (2,4) nonempty (firing). MATCHES landed dispatch.")
