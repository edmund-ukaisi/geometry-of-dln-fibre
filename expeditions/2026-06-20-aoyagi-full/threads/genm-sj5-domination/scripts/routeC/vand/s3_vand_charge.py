import sympy as sp

# ---------- Part 0: exact charge accounting, per-mode, identify the needed Vandermonde factor ----------
def flag_h(z,j):   return z-j                 # route C (triangular Cholesky/GS) raw power for mode j
def svd_h(s,z,j):  return z+s-2*j             # SVD/Weyl raw power (chamber-bounded Vandermonde)
def cap(x,h):      return min(x, h+1)         # truncated contribution to 2c
def minAdm(x,s,z): return sum(cap(x, svd_h(s,z,j)) for j in range(1,s+1))

print("=== Part 0: per-mode charge, route C vs SVD, at the anchors ===")
for (x,s,z) in [(3,2,3),(4,3,4),(5,4,6),(3,3,4),(4,3,5)]:
    rows=[]
    for j in range(1,s+1):
        hC = flag_h(z,j); hS = svd_h(s,z,j)
        cC = cap(x,hC);   cS = cap(x,hS)
        vand_extra = 2*(s-j)              # chamber Vandermonde power added to mode j
        rows.append((j,hC,hS,cC,cS,cS-cC,vand_extra))
    fC = sum(r[3] for r in rows); fS=sum(r[4] for r in rows)
    print(f"\n({x},{s},{z}): routeC charge(2c)={fC}  minAdm={fS}  UNDERSHOOT={fS-fC}")
    print(f"   {'mode':>4} {'hC=z-j':>7} {'hS=z+s-2j':>9} {'cap_C':>6} {'cap_S':>6} {'miss':>5} {'vandPow':>7}")
    for (j,hC,hS,cC,cS,d,ve) in rows:
        star = "  <== needs Vandermonde" if d>0 else ""
        print(f"   {j:>4} {hC:>7} {hS:>9} {cC:>6} {cS:>6} {d:>5} {ve:>7}{star}")
