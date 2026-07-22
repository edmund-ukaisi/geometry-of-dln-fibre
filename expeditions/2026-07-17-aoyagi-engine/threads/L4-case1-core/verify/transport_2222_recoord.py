"""
Diagnosis: does the DEEPER-LAYER RECOORDINATIZATION A_1 -> A_1 * Q^{-1} (which the fold's
canonShearOf OMITS) restore boost-readiness?

From transport_2222.py the real fold gives (u_000 quotiented, (0,1,1) sheared by -u_010*u_001):
  resid[j] = coreGen(qm_ed1(u))
with the extra-block (col-1 of layer 1) coords carrying u_010 (a layer-0 off-diagonal), NOT the
boost pivot u_011.  Aoyagi's clearing of A_0's pivot recoordinatizes the NEXT matrix A_1 -> A_1*Q^{-1}
with Q = [[1,0],[-u_010,1]] (clearing the pivot column gamma=u_010).  In the recoordinatized chart the
NEW layer-1 coords w satisfy  A_1[k][0] = w[k][0] - u_010 * w[k][1],  A_1[k][1] = w[k][1].

We substitute that into the residual and re-test boost-readiness on the center {u_011}+{new col-0}.
"""
import sympy as sp

LAYERS, D = 3, 2
u = {}
for L in range(LAYERS):
    for r in range(D):
        for c in range(D):
            u[(L, r, c)] = sp.Symbol(f"u_{L}{r}{c}")

def matrix(uu, L):
    return sp.Matrix([[uu[(L, r, c)] for c in range(D)] for r in range(D)])

def coreGen_entries(uu):
    M = matrix(uu, 2) * matrix(uu, 1) * matrix(uu, 0)
    return [M[i, j] for i in range(D) for j in range(D)]

# ed1 quotient+shear (the only nontrivial map, from transport_2222.py)
def map_ed1(uu):
    out = dict(uu)
    out[(0, 0, 0)] = sp.Integer(1)
    out[(0, 1, 1)] = uu[(0, 1, 1)] - uu[(0, 1, 0)] * uu[(0, 0, 1)]
    return out

resid = [sp.expand(f) for f in coreGen_entries(map_ed1(u))]

# --- recoordinatization: A_1[k][0] = w[k][0] - u_010 * w[k][1], A_1[k][1] = w[k][1] ---
w = {(1, r, c): sp.Symbol(f"w_1{r}{c}") for r in range(D) for c in range(D)}
recoord = {}
for r in range(D):
    recoord[u[(1, r, 0)]] = w[(1, r, 0)] - u[(0, 1, 0)] * w[(1, r, 1)]
    recoord[u[(1, r, 1)]] = w[(1, r, 1)]
resid_w = [sp.expand(f.subs(recoord, simultaneous=True)) for f in resid]

print("=== residual AFTER recoordinatization A_1 -> A_1*Q^{-1} (new layer-1 coords w) ===")
for j, f in enumerate(resid_w):
    print(f"  resid[{j}] =", f)

pivot = u[(0, 1, 1)]
partial = [w[(1, 0, 0)], w[(1, 1, 0)]]         # col-0 (col < runLen=1)
extra   = [w[(1, 0, 1)], w[(1, 1, 1)]]         # col-1
center  = [pivot] + partial

# boost-readiness on recoordinatized coords
sub0 = {c: 0 for c in center}
A1 = all(sp.expand(f.subs(sub0)) == 0 for f in resid_w)
def maxdeg(f, xs):
    fs = f.free_symbols
    if not any(x in fs for x in xs):
        return 0
    return max(sum(m) for m in sp.Poly(sp.expand(f), *xs).monoms())
A2 = all(maxdeg(f, center) <= 1 for f in resid_w)
print("\nA1 (center-zero => 0)      :", A1)
print("A2 (deg<=1 on center)      :", A2)

print("\n=== extra-block coeffs: do they carry the pivot u_011 now? ===")
for j, f in enumerate(resid_w):
    for e in extra:
        coeff = sp.expand(f.diff(e))
        if coeff == 0:
            continue
        carries = sp.expand(coeff.subs(pivot, 0)) == 0
        print(f"  resid[{j}] d/d {e}: coeff={coeff}  carries_pivot={carries}")

print("\nBOOST-READY after recoordinatization:", A1 and A2)
