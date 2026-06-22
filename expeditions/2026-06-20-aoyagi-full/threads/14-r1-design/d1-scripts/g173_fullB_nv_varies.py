import sympy as sp
# (2,2,2) full-B with rank-1 B. Loss = ||A1 A2 - B||^2, B = [[1,0],[0,0]] (rank 1).
# optimalSet = {A1 A2 = B}. 
# DEEPEST (rank-exact r=1): A1, A2 each rank EXACTLY 1, product = B.
#   e.g. A1=[[1,0],[0,0]], A2=[[1,0],[0,0]] -> product [[1,0],[0,0]] = B. Both rank 1. ✓ rank-exact.
# NON-rank-exact v: A1, A2 with DIFFERENT ranks but product still B.
#   A1 = [[1,0],[0,1]] (rank 2, = I), A2 = [[1,0],[0,0]] (rank 1) -> product [[1,0],[0,0]] = B. ✓
#   This v has layer ranks (2,1) != (1,1). NON-rank-exact.

a = sp.symbols('a0:4', real=True); b = sp.symbols('b0:4', real=True)
B = sp.Matrix([[1,0],[0,0]])

def analyze(name, A1c, A2c):
    A1 = A1c + sp.Matrix([[a[0],a[1]],[a[2],a[3]]])
    A2 = A2c + sp.Matrix([[b[0],b[1]],[b[2],b[3]]])
    P = sp.expand(A1*A2)
    G = [sp.expand((P-B)[i,j]) for i in range(2) for j in range(2)]  # 4 residual generators
    F = sp.expand(sum(g**2 for g in G))
    vars8=list(a)+list(b)
    J = sp.Matrix([[sp.diff(g,x).subs({xx:0 for xx in vars8}) for x in vars8] for g in G])
    r = J.rank()
    print(f"\n=== {name}: A1c rank={A1c.rank()}, A2c rank={A2c.rank()} ===")
    for nm,g in zip(["g00","g01","g10","g11"],G):
        lin = sum(sp.diff(g,x).subs({xx:0 for xx in vars8})*x for x in vars8)
        print(f"   {nm}: lin = {lin}")
    print(f"   Jacobian rank at v (= n_v, regular Morse dims) = {r}")
    return r

# DEEPEST (rank-exact)
nd = analyze("DEEPEST rank-exact (1,1)", sp.Matrix([[1,0],[0,0]]), sp.Matrix([[1,0],[0,0]]))
# NON-rank-exact (2,1)
nv1 = analyze("NON-rank-exact (2,1): A1=I, A2=B", sp.Matrix([[1,0],[0,1]]), sp.Matrix([[1,0],[0,0]]))
# NON-rank-exact (1,2)
nv2 = analyze("NON-rank-exact (1,2): A1=B, A2=I", sp.Matrix([[1,0],[0,0]]), sp.Matrix([[1,0],[0,1]]))

print("\n" + "="*60)
print(f"n_deepest = {nd},  n_v(2,1) = {nv1},  n_v(1,2) = {nv2}")
print("If these DIFFER, n_v is NOT constant => the simple 'n_v/2 + core' bridge with constant shift FAILS.")
print("If EQUAL, the regular shift is constant and the bridge holds.")
