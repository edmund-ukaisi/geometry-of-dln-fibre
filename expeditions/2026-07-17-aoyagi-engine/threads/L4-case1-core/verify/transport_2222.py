"""
Exact-algebra trace of the REAL Aoyagi fold on d=(2,2,2,2), to node p = the case1(1)
BOOST PARENT, and a boost-readiness / chainWeight check.

Faithful to the Lean defs:
  coreGen     : entries of mult = A_2 * A_1 * A_0 (last layer LEFTmost); coord (layer,row,col) = A_layer[row][col]
  blockBlowupMap S p w j = (j==p ? w[p] : j in S ? w[p]*w[j] : w[j])
  blockBlowupCoordQuot p j w = (j==p ? 1 : w[j])
  canonShearOf s u k: decode (lay,row,col); if lay==s.layer and s.cleared<row and s.cleared<col
                      then -u[(lay,row,s.cleared)]*u[(lay,s.cleared,col)] else 0
  edgeShear = id (case11/rollover), blockShear(canonShearOf) (case12/case2), blockShear phi u = u+phi(u)
  stepMap = blockBlowupMap center pivot . edgeShear
  qm      = blockBlowupCoordQuot pivot . edgeShear
  foldResid p_n(u) = coreGen( map_1( map_2( ... map_n(u) ) ) )   (ed1 outermost => applied LAST)
"""
import sympy as sp

LAYERS, D = 3, 2  # N=3 layers 0,1,2; all 2x2

# --- symbolic coords u[(layer,row,col)] ---
u = {}
for L in range(LAYERS):
    for r in range(D):
        for c in range(D):
            u[(L, r, c)] = sp.Symbol(f"u_{L}{r}{c}")

def matrix(uu, L):
    return sp.Matrix([[uu[(L, r, c)] for c in range(D)] for r in range(D)])

def coreGen_entries(uu):
    # mult = A_2 * A_1 * A_0
    M = matrix(uu, 2) * matrix(uu, 1) * matrix(uu, 0)
    return [M[i, j] for i in range(D) for j in range(D)]  # 4 entries

# --- fold maps ---
def canonShear(uu, s_layer, s_cleared):
    """returns phi(uu): dict coord->displacement value"""
    phi = {k: sp.Integer(0) for k in uu}
    for (L, r, c) in uu:
        if L == s_layer and s_cleared < r and s_cleared < c:
            phi[(L, r, c)] = -uu[(L, r, s_cleared)] * uu[(L, s_cleared, c)]
    return phi

def edgeShear(uu, case, s_layer, s_cleared):
    if case in ("case11", "rollover"):
        return dict(uu)
    phi = canonShear(uu, s_layer, s_cleared)
    return {k: uu[k] + phi[k] for k in uu}

def stepMap(uu, case, center, pivot, s_layer, s_cleared):
    w = edgeShear(uu, case, s_layer, s_cleared)
    out = {}
    for j in uu:
        if pivot is not None and j == pivot:
            out[j] = w[pivot]
        elif j in center:
            out[j] = w[pivot] * w[j]
        else:
            out[j] = w[j]
    return out

def qm(uu, case, pivot, s_layer, s_cleared):
    w = edgeShear(uu, case, s_layer, s_cleared)
    return {j: (sp.Integer(1) if j == pivot else w[j]) for j in uu}

# --- the path to the boost parent p (verified by hand-trace of classify/transitions) ---
# ed1: case2 delta=1, parent (layer0,cleared0), pivot (0,0,0)
# ed2: case2 delta=0, parent (layer0,cleared1), pivot (0,1,1), center {(0,1,1)}
# ed3: rollover delta=0, parent (layer0,cleared2), pivot none, center {}
# foldResid_p(u) = coreGen( map_ed1( map_ed2( map_ed3(u) ) ) )   apply ed3 first (innermost)

def map_ed3(uu):  # rollover delta0: stepMap center={} pivot=None  => identity
    return stepMap(uu, "rollover", set(), None, 1, 0)  # parent layer irrelevant (id)

def map_ed2(uu):  # case2 delta0: stepMap center={(0,1,1)} pivot=(0,1,1), parent (layer0,cleared1)
    return stepMap(uu, "case2", {(0, 1, 1)}, (0, 1, 1), 0, 1)

def map_ed1(uu):  # case2 delta1: qm pivot=(0,0,0), parent (layer0,cleared0)
    return qm(uu, "case2", (0, 0, 0), 0, 0)

v = map_ed1(map_ed2(map_ed3(u)))
resid = [sp.expand(f) for f in coreGen_entries(v)]

print("=== the three maps: which are nontrivial? ===")
print("ed3 (rollover) == id :", all(sp.simplify(map_ed3(u)[k]-u[k])==0 for k in u))
print("ed2 (case2 d0) == id :", all(sp.simplify(map_ed2(u)[k]-u[k])==0 for k in u))
m1 = map_ed1(u)
print("ed1 (case2 d1) nontrivial coords:",
      {k: m1[k] for k in u if sp.simplify(m1[k]-u[k]) != 0})

print("\n=== foldResid p (4 slots) ===")
for j, f in enumerate(resid):
    print(f"  resid[{j}] =", f)

# --- boost geometry ---
pivot = (0, 1, 1)                       # div1 birth corner (reused)
partialBlock = [(1, r, 0) for r in range(D)]   # layer-1 col 0 (col < runLen=1)
extraBlock   = [(1, r, 1) for r in range(D)]   # layer-1 col 1 (runLen<=col<2)
support      = partialBlock + extraBlock       # blockCoords(layer1) full
center       = [pivot] + partialBlock
u_pivot = u[pivot]

print("\n=== boost-readiness checks (center = {pivot}+partial) ===")
print("pivot      =", pivot, "=", u_pivot)
print("partial    =", partialBlock)
print("extra      =", extraBlock)

# A1: residual vanishes when ALL center coords set to 0
sub0 = {u[k]: 0 for k in center}
A1 = all(sp.expand(f.subs(sub0)) == 0 for f in resid)
# A2: jointly degree <=1 in the center coords
def maxdeg(f, xs):
    p = sp.Poly(sp.expand(f), *[u[k] for k in xs]) if any(u[k] in f.free_symbols for k in xs) else None
    if p is None:
        return 0
    return max(sum(m) for m in p.monoms())
A2 = all(maxdeg(f, center) <= 1 for f in resid)
print("A1 (center-zero => 0)        :", A1)
print("A2 (deg<=1 on center)        :", A2)

# A3: after boost substitution (center coords *= u_pivot), each residual divisible by u_pivot
def boost_sub(f):
    s = {}
    for k in center:
        if k == pivot:
            continue
        s[u[k]] = u_pivot * u[k]
    # pivot coord itself: blockBlowupMap sets pivot->w[pivot]; the boost multiplies the *partial*
    # block by pivot, pivot stays. We test divisibility of the untouched extra terms.
    return sp.expand(f.subs(s, simultaneous=True))
A3 = []
for f in resid:
    g = boost_sub(f)
    q, rem = sp.div(sp.Poly(g, u_pivot), sp.Poly(u_pivot, u_pivot))
    A3.append(sp.expand(g.subs(u_pivot, 0)) == 0)
print("A3 (extra terms carry pivot) :", all(A3))

# --- KEY: read off the actual b-chain weight each support coord carries ---
print("\n=== per-support-coordinate weight in the residual ===")
print("(coefficient of u_i in resid[j], and whether it carries u_pivot=%s)" % u_pivot)
for j, f in enumerate(resid):
    for i in support:
        coeff = sp.expand(f.diff(u[i]))
        if coeff == 0:
            continue
        carries_pivot = sp.expand(coeff.subs(u_pivot, 0)) == 0
        col = i[2]
        print(f"  resid[{j}] d/d u_{i}  (col={col}): coeff={coeff}   carries_pivot={carries_pivot}")

# --- compare to chainWeight (strict divTilde<col) at parent state ---
# parent divisors: div0 birth (0,0) divTilde 0 ; div1 birth (0,1) divTilde 1
# birth flat coords: div0->(0,0,0), div1->(0,1,1)
print("\n=== chainWeight(col) as DEFINED (strict divTilde<col), at parent ===")
divs = [("div0", (0,0,0), 0), ("div1", (0,1,1), 1)]  # (name, birthflat, divTilde)
def chainWeight_strict(col):
    prod = sp.Integer(1)
    for name, bf, dt in divs:
        if dt < col:
            prod *= u[bf]
    return prod
def chainWeight_nonstrict(col):
    prod = sp.Integer(1)
    for name, bf, dt in divs:
        if dt <= col:
            prod *= u[bf]
    return prod
for col in range(D):
    print(f"  col={col}: strict={chainWeight_strict(col)}   nonstrict={chainWeight_nonstrict(col)}")
