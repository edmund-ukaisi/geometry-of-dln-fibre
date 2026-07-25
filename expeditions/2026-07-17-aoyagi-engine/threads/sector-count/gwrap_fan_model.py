"""Decorrelated sympy model of the (3,3,4) gWrap fan (sector-count #144).
Atoms from Corank2GWrapDecomp.lean (read directly). Exact rational/symbolic.
  bbA1 = blockBlowupMap {1,5,6,7} pivot 1     (inner)
  bbA0 = blockBlowupMap {0..7}   pivot 0
  permP: reindex by permIdx (fixes >=12)
  shearH: writes {4,5,6,7,8,9,10,11}, reads {0,1,2,3,12..19}
  sigmaPiv = blockBlowupMap {0..7,20} pivot 20   (OUTERMOST)
gWrap = sigmaPiv ∘ shearH ∘ permP ∘ bbA0 ∘ bbA1 ."""
import sympy as sp

D=21
w=sp.symbols('w0:21', real=True)

def blockbb(center, piv, v):
    return [ (v[piv] if k==piv else (v[piv]*v[k] if k in center else v[k])) for k in range(D)]

permIdx = {0:8,1:9,2:10,3:11,4:1,5:5,6:6,7:7,8:0,9:2,10:3,11:4}
def perm(v): return [ v[permIdx.get(k,k)] for k in range(D)]
def shearH(p):
    h=list(p)
    h[4]=p[4]+p[0]*p[2]; h[5]=p[5]+p[1]*p[2]; h[6]=p[6]+p[0]*p[3]; h[7]=p[7]+p[1]*p[3]
    h[8]=p[8]-p[0]*p[12]-p[1]*p[16]; h[9]=p[9]-p[0]*p[13]-p[1]*p[17]
    h[10]=p[10]-p[0]*p[14]-p[1]*p[18]; h[11]=p[11]-p[0]*p[15]-p[1]*p[19]
    return h

def gwrap(w, p3, p2, p1):
    y=blockbb({1,5,6,7}, p3, list(w))
    z=blockbb({0,1,2,3,4,5,6,7}, p2, y)
    p=perm(z)
    h=shearH(p)
    x=blockbb({0,1,2,3,4,5,6,7,20}, p1, h)
    return x, h

# (a) jacDet monomial vs polynomial across sigmaPiv pivot p1 (canonical p3=1,p2=0)
print("=== (a) |jacDet| of gWrap vs sigmaPiv pivot p1 (p3=1,p2=0) ===")
for p1 in [20,0,1,2,3,4,5,6,7]:
    x,h = gwrap(w, 1, 0, p1)
    J = sp.Matrix([[sp.diff(x[i], w[j]) for j in range(D)] for i in range(D)])
    det = sp.factor(J.det())
    ismono = det.is_Mul or det.is_Pow or det.is_Number or det.is_Symbol
    # a coordinate monomial: factor is a product of powers of single w_k (up to sign)
    d2 = sp.factor(det)
    fa = d2.as_ordered_factors()
    coordmono = all( (f.is_Number or (f.is_Symbol) or (f.is_Pow and f.args[0].is_Symbol)) for f in fa)
    print(f"  p1={p1:2d}: det={d2}   coord-monomial={coordmono}")

print()
print("=== (b) shear-slot bound: x_j / x_20 on the canonical chart (p3=1,p2=0,p1=20) ===")
x,h = gwrap(w,1,0,20)
for j in [4,5,6,7]:
    ratio = sp.simplify(x[j]/x[20])
    print(f"  x_{j}/x_20 = {ratio}   (= h_{j}, a bounded poly on the source box)")

print()
print("=== (c) coinciding-pivot jacDets: do exponents STACK? monomial? ===")
cases = [("distinct canonical", 1,0,20),
         ("p2==p3 (both=1)", 1,1,20),
         ("p2==p3 (both=5)", 5,5,20),
         ("p1==p2 (both=0)", 1,0,0),
         ("p1==p2==? (p1=2,p2=2)", 1,2,2),
         ("p1==p2 (both=3),p3=1", 1,3,3)]
for name,p3,p2,p1 in cases:
    try:
        x,h = gwrap(w,p3,p2,p1)
        J = sp.Matrix([[sp.diff(x[i], w[j]) for j in range(D)] for i in range(D)])
        det = sp.factor(J.det())
        fa = sp.factor(det).as_ordered_factors()
        coordmono = all((f.is_Number or f.is_Symbol or (f.is_Pow and f.args[0].is_Symbol)) for f in fa)
        print(f"  {name:26s} p=({p3},{p2},{p1}): det={det}  coord-mono={coordmono}")
    except Exception as e:
        print(f"  {name}: ERR {e}")
