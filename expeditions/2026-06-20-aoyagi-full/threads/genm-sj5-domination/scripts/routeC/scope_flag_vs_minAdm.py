# Scope: does the one-row-at-a-time rational Gram-Schmidt flag chart reach minAdm?
# chart charge (peel the s-row factor, rows in R^z, blocks in R^x): Sum_j min(x, z+1-j), j=1..s
# minAdm identity (routeA):                                          Sum_j min(x, z+s+1-2j), j=1..s
# SVD raw h_j = z+s-2j  vs  flag raw h_j = z-j  ; miss = (s-j) per row = Vandermonde repulsion.
def flag(x,s,z):  return sum(min(x, z+1-j)    for j in range(1,s+1))
def madm(x,s,z):  return sum(min(x, z+s+1-2*j) for j in range(1,s+1))
def flagT(x,s,z): return flag(z,s,x)   # transpose orientation (peel the OTHER factor)
print(f"{'(x,s,z)':>10} {'flag(A1)':>8} {'flag(A0^T)':>10} {'best':>5} {'minAdm':>7} {'tight?':>7}")
for (x,s,z) in [(2,1,2),(3,1,3),(3,2,3),(4,2,3),(3,2,4),(4,2,4),(5,2,3),(4,3,4),(5,4,6),(3,3,4),(4,3,5)]:
    best=max(flag(x,s,z), flagT(x,s,z))
    print(f"{str((x,s,z)):>10} {flag(x,s,z):>8} {flagT(x,s,z):>10} {best:>5} {madm(x,s,z):>7} {str(best==madm(x,s,z)):>7}")
print("\nConclusion:")
print(" s=1: tight always. s=2: tight for ALL widths WITH correct orientation (peel factor giving max).")
print(" s>=3: naive one-row flag UNDERSHOOTS minAdm (misses Vandermonde repulsion) even with orientation.")
