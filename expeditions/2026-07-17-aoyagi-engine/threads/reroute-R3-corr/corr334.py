"""
R3 correspondence de-risk (task #180): ι (12 coreGen entries) ↔ bornSiblings (center {0,1}).
Exact algebra over ℚ, layout EXACTLY as the Lean defs.

Lean facts encoded:
 - eWrap: A0 = C1ᵀ = !![u20,u2,u3; u0,u4,u6; u1,u5,u7]  (3x3)
          A1 = C2ᵀ, A1[a][b] = u(8+4b+a)                (4x3)
 - coreGen k = (A1·A0)[i][j] = X[i][j], (i,j)=finProdFinEquiv.symm k, i∈Fin4, j∈Fin3  (12 gens)
 - clearing shearH = id + shearPhiH (Corank2ChartJac.shearPhiH), corrects slots 4..11
 - center {0,1}, born siblings blockBlowupMap {0,1} p (p=0 or 1), stepMap_p = blowup ∘ shearH
"""
import sympy as sp

u = sp.symbols('u0:21')  # u0..u20

# ---- A0 = C1ᵀ  (3x3), rows given by the Lean !![...] ----
A0 = sp.Matrix([[u[20], u[2], u[3]],
                [u[0],  u[4], u[6]],
                [u[1],  u[5], u[7]]])
# ---- A1 = C2ᵀ (4x3): A1[a][b] = u(8+4b+a) ----
A1 = sp.Matrix(4,3, lambda a,b: u[8+4*b+a])

X = A1*A0   # 4x3 = the 12 generators; X[i,j] = coreGen entry (i,j)

print("=== The 12 generators X[i][j] (i in Fin4 rows, j in Fin3 cols) ===")
for i in range(4):
    for j in range(3):
        print(f"X[{i}][{j}] = {sp.expand(X[i,j])}")

# Which coords appear in which generator?
print("\n=== coords appearing in each generator ===")
for j in range(3):
    for i in range(4):
        fs = sorted(int(str(s)[1:]) for s in X[i,j].free_symbols)
        print(f"X[{i}][{j}] col{j}: coords {fs}")

# ---- shearPhiH: corrections in slots 4..11 ----
def shearPhi(w):
    phi = [sp.Integer(0)]*21
    phi[4]  = w[0]*w[2]
    phi[5]  = w[1]*w[2]
    phi[6]  = w[0]*w[3]
    phi[7]  = w[1]*w[3]
    phi[8]  = -(w[0]*w[12]) - w[1]*w[16]
    phi[9]  = -(w[0]*w[13]) - w[1]*w[17]
    phi[10] = -(w[0]*w[14]) - w[1]*w[18]
    phi[11] = -(w[0]*w[15]) - w[1]*w[19]
    return phi

def shearH(w):
    phi = shearPhi(w)
    return [w[i] + phi[i] for i in range(21)]

# ---- blockBlowupMap {0,1} p : coord p ↦ w_p; other center coord ↦ w_p*w_j; spectators fixed ----
def blowup01(w, p):
    center = {0,1}
    out = list(w)
    for j in range(21):
        if j == p:
            out[j] = w[p]
        elif j in center:
            out[j] = w[p]*w[j]
        else:
            out[j] = w[j]
    return out

w = sp.symbols('w0:21')  # fresh source coords

def stepMap(p):
    v = shearH(list(w))         # first apply clearing
    return blowup01(v, p)       # then blow up at pivot p in center {0,1}

print("\n\n########## stepMap_0 = blowup{0,1}0 ∘ shearH ##########")
sm0 = stepMap(0)
print("stepMap_0 coord images (only the non-identity ones):")
for j in range(21):
    if sm0[j] != w[j]:
        print(f"  coord {j}: {sp.expand(sm0[j])}")

print("\n########## stepMap_1 = blowup{0,1}1 ∘ shearH ##########")
sm1 = stepMap(1)
print("stepMap_1 coord images (only the non-identity ones):")
for j in range(21):
    if sm1[j] != w[j]:
        print(f"  coord {j}: {sp.expand(sm1[j])}")

# ---- Pull back the 12 generators through each stepMap; factor out the pivot ----
subs0 = {u[k]: sm0[k] for k in range(21)}
subs1 = {u[k]: sm1[k] for k in range(21)}

def analyze(subs, p, name):
    print(f"\n\n===== generators pulled back through {name} (pivot {p}) =====")
    for j in range(3):
        for i in range(4):
            g = sp.expand(X[i,j].subs(subs))
            # try to factor out w_p
            q, r = sp.div(sp.Poly(g, w[p]), sp.Poly(w[p], w[p]))
            divisible = (r == 0)
            fac = sp.factor(g)
            print(f"  X[{i}][{j}]∘{name} = {g}")
            print(f"        factored: {fac}   | divisible by w{p}: {divisible}")

analyze(subs0, 0, "stepMap_0")
analyze(subs1, 1, "stepMap_1")
