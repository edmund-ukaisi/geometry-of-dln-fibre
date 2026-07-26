"""
Faithful sympy reconstruction of the Lean `gFlat idx` composite for p1=20, to
independently cross-check a3f030's 16-leaf data for the 8 pattern-B leaves.

Pipeline (matches Corank2NativeFan334.gFlat + Corank2CoreGenWrap.A0/A1):
  input x = psiCanon(u) = u + phi(u)
  y3 = bb(sigmaC2Fs20, p3)(x)          # node 3, center {1,5,6,7}
  y2 = bb(sigmaC1Fs20, p2)(y3)         # node 2, center {0..7}
  yp = nativePerm20(y2) = i -> y2[cperm20(i)]
  y1 = nativeSel20(yp) = yp + qdisp(t1P20,t2P20)(yp)
  w  = bb(S1, 20)(y1)                  # node 0, center {0..7,20}, pivot 20
  entry(i,j) = (A1(w) * A0(w))[i,j]
"""
import sympy as sp

u = sp.symbols('u0:21')  # u[0]..u[20]

def bb(S, p, w):
    """blockBlowupMap: j=p -> w[p]; j in S -> w[p]*w[j]; else w[j]."""
    out = list(w)
    for j in range(21):
        if j == p:
            out[j] = w[p]
        elif j in S:
            out[j] = w[p] * w[j]
        else:
            out[j] = w[j]
    return out

# cperm20 index map
def cperm20(k):
    d = {0:8, 1:9, 2:10, 3:11, 4:1, 8:0, 9:2, 10:3, 11:4}
    return d.get(k, k)

def nativePerm20(w):
    return [w[cperm20(i)] for i in range(21)]

def qdisp20(y):
    """sterm(t1P20)+sterm(t2P20). true=+, false=-."""
    out = [sp.Integer(0)]*21
    # t1P20
    out[4]  += y[0]*y[2]
    out[5]  += y[1]*y[2]
    out[6]  += y[0]*y[3]
    out[7]  += y[1]*y[3]
    out[8]  += -(y[0]*y[12])
    out[9]  += -(y[0]*y[13])
    out[10] += -(y[0]*y[14])
    out[11] += -(y[0]*y[15])
    # t2P20
    out[8]  += -(y[1]*y[16])
    out[9]  += -(y[1]*y[17])
    out[10] += -(y[1]*y[18])
    out[11] += -(y[1]*y[19])
    return out

def nativeSel20(y):
    q = qdisp20(y)
    return [y[i] + q[i] for i in range(21)]

SIGMA_C1_20 = {0,1,2,3,4,5,6,7}
SIGMA_C2_20 = {1,5,6,7}
S1 = {0,1,2,3,4,5,6,7,20}

def gCanon(x, p2, p3):
    y3 = bb(SIGMA_C2_20, p3, x)
    y2 = bb(SIGMA_C1_20, p2, y3)
    yp = nativePerm20(y2)
    y1 = nativeSel20(yp)
    w  = bb(S1, 20, y1)
    return w

# A0 (3x3): [[u20,u2,u3],[u0,u4,u6],[u1,u5,u7]]
def A0(w):
    return sp.Matrix([[w[20], w[2], w[3]],
                      [w[0],  w[4], w[6]],
                      [w[1],  w[5], w[7]]])

# A1 (4x3): A1[a][b] = w[8+4b+a]
def A1(w):
    return sp.Matrix(4, 3, lambda a, b: w[8 + 4*b + a])

def entry(w, i, j):
    return (A1(w) * A0(w))[i, j]

def psi(phi_dict):
    """blockShear with displacement given as {coord: expr(u)}."""
    x = list(u)
    for k, expr in phi_dict.items():
        x[k] = u[k] + expr
    return x

# ---- leaf definitions: (p2,p3, block_start, vm_coords, phi_dict, coinciding) ----
def phiB(block_start, p2, p3, coinc):
    """Build phi for a pattern-B leaf per a3f030 data. block_start=12 (p2=6) or 16 (p2=7).
    Returns dict {coord: expr}. col-2 entries straighten to block; col-0 pure."""
    b = block_start
    # The 4 A1-col2 read coords are 16..19 when block=12, 12..15 when block=16.
    # We encode the exact expressions from the data file per leaf below instead.
    return None

leaves = {}

# (20,6,1): block 12, vm {1,6,20}
leaves[(6,1)] = dict(block=12, vm={1,6,20}, coinc=False, phi={
  12: -(u[0]*u[11] + u[1]*u[16]*u[7]),
  13: -(u[1]*u[17]*u[7] + u[11]*u[2]),
  14: -(u[1]*u[18]*u[7] + u[11]*u[3]),
  15: -(u[1]*u[19]*u[7] + u[11]*u[4]),
})
# (20,6,5): block 12, vm {5,6,20}
leaves[(6,5)] = dict(block=12, vm={5,6,20}, coinc=False, phi={
  12: -(u[0]*u[11] + u[16]*u[5]*u[7]),
  13: -(u[11]*u[2] + u[17]*u[5]*u[7]),
  14: -(u[11]*u[3] + u[18]*u[5]*u[7]),
  15: -(u[11]*u[4] + u[19]*u[5]*u[7]),
})
# (20,6,6): block 12, vm {6,20}, coinciding CUBIC
leaves[(6,6)] = dict(block=12, vm={6,20}, coinc=True, phi={
  12: -(u[0]*u[11] + u[16]*u[6]*u[7]),
  13: -(u[11]*u[2] + u[17]*u[6]*u[7]),
  14: -(u[11]*u[3] + u[18]*u[6]*u[7]),
  15: -(u[11]*u[4] + u[19]*u[6]*u[7]),
})
# (20,6,7): block 12, vm {6,7,20}
leaves[(6,7)] = dict(block=12, vm={6,7,20}, coinc=False, phi={
  12: -(u[0]*u[11] + u[16]*u[7]),
  13: -(u[11]*u[2] + u[17]*u[7]),
  14: -(u[11]*u[3] + u[18]*u[7]),
  15: -(u[11]*u[4] + u[19]*u[7]),
})
# (20,7,1): block 16, vm {1,7,20}
leaves[(7,1)] = dict(block=16, vm={1,7,20}, coinc=False, phi={
  16: -(u[0]*u[11] + u[1]*u[12]*u[6]),
  17: -(u[1]*u[13]*u[6] + u[11]*u[2]),
  18: -(u[1]*u[14]*u[6] + u[11]*u[3]),
  19: -(u[1]*u[15]*u[6] + u[11]*u[4]),
})
# (20,7,5): block 16, vm {5,7,20}
leaves[(7,5)] = dict(block=16, vm={5,7,20}, coinc=False, phi={
  16: -(u[0]*u[11] + u[12]*u[5]*u[6]),
  17: -(u[11]*u[2] + u[13]*u[5]*u[6]),
  18: -(u[11]*u[3] + u[14]*u[5]*u[6]),
  19: -(u[11]*u[4] + u[15]*u[5]*u[6]),
})
# (20,7,6): block 16, vm {6,7,20}
leaves[(7,6)] = dict(block=16, vm={6,7,20}, coinc=False, phi={
  16: -(u[0]*u[11] + u[12]*u[6]),
  17: -(u[11]*u[2] + u[13]*u[6]),
  18: -(u[11]*u[3] + u[14]*u[6]),
  19: -(u[11]*u[4] + u[15]*u[6]),
})
# (20,7,7): block 16, vm {7,20}, coinciding CUBIC
leaves[(7,7)] = dict(block=16, vm={7,20}, coinc=True, phi={
  16: -(u[0]*u[11] + u[12]*u[6]*u[7]),
  17: -(u[11]*u[2] + u[13]*u[6]*u[7]),
  18: -(u[11]*u[3] + u[14]*u[6]*u[7]),
  19: -(u[11]*u[4] + u[15]*u[6]*u[7]),
})

# pattern-B reg-seq pairs (row, col), cols {0,2}
pairsB = [(0,0),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,2)]

def vm_expr(vm):
    e = sp.Integer(1)
    for c in sorted(vm):
        e = e * u[c]
    return e

def zc_of(pair, block):
    r, c = pair
    if c == 0:
        return {0:0, 1:2, 2:3, 3:4}[r]   # col-0 -> pure coords 0,2,3,4
    else:  # c == 2
        return block + r                  # col-2 -> block coords

print("=== Pattern-B leaf verification (entry == vm * u_zc) ===")
all_ok = True
for (p2,p3), d in leaves.items():
    x = psi(d['phi'])
    w = gCanon(x, p2, p3)
    vm = vm_expr(d['vm'])
    leaf_ok = True
    for pair in pairsB:
        val = sp.expand(entry(w, pair[0], pair[1]))
        zc = zc_of(pair, d['block'])
        target = sp.expand(vm * u[zc])
        ok = sp.simplify(val - target) == 0
        if not ok:
            leaf_ok = False
            all_ok = False
            print(f"  LEAF (20,{p2},{p3}) pair {pair} zc={zc}: MISMATCH")
            print(f"     got   : {val}")
            print(f"     target: {target}")
    print(f"leaf (20,{p2},{p3}) [{'coinc' if d['coinc'] else 'noncoinc'}, vm={sorted(d['vm'])}, block={d['block']}]: "
          + ("ALL 8 OK" if leaf_ok else "FAIL"))

print("=== overall:", "ALL PATTERN-B LEAVES VERIFIED" if all_ok else "FAILURES PRESENT", "===")
