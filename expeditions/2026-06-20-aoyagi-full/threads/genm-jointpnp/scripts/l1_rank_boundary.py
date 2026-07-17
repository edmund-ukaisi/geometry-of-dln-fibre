"""
DECORRELATED verification, part 2 -- the ALGEBRAIC single-factor certificate.

Load-bearing claim of the joint-coupled-spec: a Lane-1 leaf (peel corank (r,k), min(r,k)<=1)
is single-factor because the exceptional matrix (Delta . C) has rank <= min(r,k) <= 1, so
||Delta . C . Z||^2 = ||left-vector||^2 * ||right-vector^T Z||^2 (a FreeBilinear rank-1 tensor),
resolved by the banked free-bilinear leaf + projection-radial + recursion.

The min>=2 boundary is exactly where (Delta . C) can be rank >= 2 -> genuine product-corank.

We CERTIFY (exact symbolic, sympy):
 (i)  rank(Delta . C) <= min(r,k) for symbolic Delta (rxk), C (kxM2).
 (ii) for r=1 (any k): Delta.C is a single row; Delta.C.Z = u^T Z with u = C^T Delta^T; rank <=1;
      ||Delta.C.Z||^2 factors.
 (iii) for k=1 (any r): Delta.C = gamma (c^T), rank-1; ||Delta.C.Z||^2 = ||gamma||^2 ||c^T Z||^2.
 (iv) for min(r,k)>=2 (r=k=2): exhibit a Delta,C with rank(Delta.C)=2 (NOT rank-1) -> product-corank.
"""
import sympy as sp

def sym_mat(name, m, n):
    return sp.Matrix(m, n, lambda i,j: sp.Symbol(f"{name}_{i}{j}", real=True))

def rank_generic(M):
    # symbolic rank via sympy .rank() (uses generic/structural rank for symbolic entries)
    return M.rank()

print("=== (i) rank(Delta.C) <= min(r,k) : structural check over small shapes ===")
for r in range(1,4):
    for k in range(1,4):
        for M2 in range(1,4):
            D = sym_mat("d", r, k)
            C = sym_mat("c", k, M2)
            P = D*C
            rk = P.rank()
            bound = min(r,k,M2)
            status = "OK" if rk <= min(r,k) else "!!VIOLATION!!"
            if rk != bound or status!="OK":
                print(f"  r={r} k={k} M2={M2}: rank(DC)={rk}  min(r,k)={min(r,k)}  [{status}]")
print("  (all shapes: rank(Delta.C) == min(r,k,M2) generically, and <= min(r,k) always -- confirmed)")

print()
print("=== (ii) r=1, k=2, M2=2, q=2 : Delta.C is a row; ||Delta.C.Z||^2 factors as FreeBilinear ===")
r,k,M2,q = 1,2,2,2
D = sym_mat("d", r, k)   # 1x2 row  (delta^T)
C = sym_mat("c", k, M2)  # 2x2
Z = sym_mat("z", M2, q)  # 2x2 deep
DC = D*C                 # 1x2 row
DCZ = DC*Z               # 1x2 row
print("  rank(Delta.C) =", DC.rank(), " (expect 1)")
print("  rank(Delta.C.Z) =", DCZ.rank(), " (expect <=1)")
# collapse: Delta.C = (C^T delta)^T ; define u = C^T delta^T  (M2-vector), then Delta.C.Z = u^T Z
delta_vec = D.T                       # 2x1  = delta
u = C.T * delta_vec                   # M2 x 1
lhs = sp.expand((DCZ*DCZ.T)[0,0])     # ||Delta.C.Z||^2 (scalar)
rhs = sp.expand(( (u.T*Z)*(u.T*Z).T )[0,0])   # ||u^T Z||^2
print("  ||Delta.C.Z||^2 == ||u^T Z||^2 with u=C^T delta ? ->", sp.simplify(lhs-rhs)==0)
print("     => collapses to a projection-radial in the single free vector u (u = C^T delta = FreeBilinear tensor)")

print()
print("=== (iii) k=1, r=2 (b=0 tall shape): Delta.C = gamma c^T rank-1; norm factors ===")
r,k,M2,q = 2,1,2,2
D = sym_mat("g", r, k)   # 2x1 column gamma
C = sym_mat("c", k, M2)  # 1x2 row  c^T
Z = sym_mat("z", M2, q)
DC = D*C
DCZ = DC*Z
print("  rank(Delta.C) =", DC.rank(), " (expect 1)")
lhs = sp.expand(sum(DCZ[i,j]**2 for i in range(r) for j in range(q)))
gamma = D                          # 2x1
cZ = (C*Z)                         # 1x2 row = c^T Z
rhs = sp.expand( (sum(g**2 for g in gamma)) * (sum(v**2 for v in cZ)) )
print("  ||Delta.C.Z||^2 == ||gamma||^2 * ||c^T Z||^2 ? ->", sp.simplify(lhs-rhs)==0)

print()
print("=== (iv) min(r,k)=2 (r=k=2): Delta.C can be rank 2 -> NOT a rank-1 tensor -> product-corank ===")
r,k,M2,q = 2,2,3,2
D = sym_mat("d", r, k)
C = sym_mat("c", k, M2)
DC = D*C
print("  rank(Delta.C) generic =", DC.rank(), " (expect 2 = min(r,k))  -> genuine >=2 product, single-factor FAILS")
# exhibit an explicit rank-2 instance
Dn = sp.Matrix([[1,0],[0,1]]); Cn = sp.Matrix([[1,0,0],[0,1,0]])
print("  explicit: Delta=I2, C=[[1,0,0],[0,1,0]] -> rank(Delta.C) =", (Dn*Cn).rank())
