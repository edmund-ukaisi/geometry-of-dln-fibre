"""
Part 2: (a) does the loss monomialize at the {0,1} node?  (b) which indexing covers?
Exact where it matters, MC to GUIDE the cover-fraction question.
"""
import sympy as sp, random, itertools

u = sp.symbols('u0:21')
A0 = sp.Matrix([[u[20], u[2], u[3]],[u[0],u[4],u[6]],[u[1],u[5],u[7]]])
A1 = sp.Matrix(4,3, lambda a,b: u[8+4*b+a])
X = A1*A0
gens = [sp.expand(X[i,j]) for i in range(4) for j in range(3)]  # 12 gens, order (i,j)
labels = [f"X{i}{j}" for i in range(4) for j in range(3)]

w = sp.symbols('w0:21')
def shearH(ww):
    v=list(ww)
    v[4]=ww[4]+ww[0]*ww[2]; v[5]=ww[5]+ww[1]*ww[2]; v[6]=ww[6]+ww[0]*ww[3]; v[7]=ww[7]+ww[1]*ww[3]
    v[8]=ww[8]-ww[0]*ww[12]-ww[1]*ww[16]; v[9]=ww[9]-ww[0]*ww[13]-ww[1]*ww[17]
    v[10]=ww[10]-ww[0]*ww[14]-ww[1]*ww[18]; v[11]=ww[11]-ww[0]*ww[15]-ww[1]*ww[19]
    return v
def blowup01(ww,p):
    out=list(ww)
    for j in range(21):
        if j==p: out[j]=ww[p]
        elif j in (0,1): out[j]=ww[p]*ww[j]
        else: out[j]=ww[j]
    return out
def stepMap(p):
    return blowup01(shearH(list(w)),p)

# ---------- (a) LOSS = sum of squares of the 12 gens, pulled back ----------
print("===== (a) Does the loss monomialize at the {0,1} node? =====")
for p in (0,1):
    sm=stepMap(p); subs={u[k]:sm[k] for k in range(21)}
    loss=sp.expand(sum((g.subs(subs))**2 for g in gens))
    # divisibility by w_p^2 and w_p
    poly=sp.Poly(loss,w[p])
    div1 = sp.rem(poss:=poly, sp.Poly(w[p],w[p]))==0
    # loss at origin and its lowest-degree part in w_p
    loss0 = loss.subs({w[k]:0 for k in range(21)})
    ldeg = sp.Poly(loss,w[p]).monoms()  # exponents of w_p present
    minexp = min(m[0] for m in ldeg)
    print(f" pivot {p}: loss(origin)={loss0}; min power of w{p} dividing loss = {minexp}; divisible by w{p}: {minexp>=1}")

# Check: is ANY monomial m with loss = m^2 * R, R(0)=1 ? Equivalent to loss having a nonzero
# lowest-order term of even degree that is a perfect square with the rest >= it. Just report the
# total lowest-degree (multiplicity) of loss at origin along generic vs pivot directions.
sm0=stepMap(0); subs0={u[k]:sm0[k] for k in range(21)}
loss0expr=sp.expand(sum((g.subs(subs0))**2 for g in gens))
print("\n loss lowest total degree at origin:",
      min(sum(m) for m in sp.Poly(loss0expr, *w).monoms()))
print(" (a monomial^2 * R sandwich with R(0)=1 requires loss = (single monomial)^2 * unit;")
print("  a lowest-degree part that is a SUM of >1 square-monomials => NO single-monomial sandwich)")
# show the lowest-degree homogeneous part
P=sp.Poly(loss0expr,*w); md=min(sum(m) for m in P.monoms())
low=sum(c*sp.prod([w[i]**m[i] for i in range(21)]) for m,c in P.terms() if sum(m)==md)
print(" lowest-degree part of loss∘stepMap_0:", sp.expand(low))

# ---------- (b) COVER: input-pivot (2 charts) vs output-generator (12->2) ----------
print("\n===== (b) cover fractions (MC guide over the box, then EXACT thin-set argument) =====")
gfun=[sp.lambdify(u, g, 'math') for g in gens]
def in_image_pivot(x, p):
    # x in image of blockBlowupMap{0,1}p  <=>  NOT ( x_p==0 and x_other!=0 )
    other = 1 if p==0 else 0
    return not (abs(x[p])<1e-12 and abs(x[other])>1e-12)
random.seed(0); N=200000; boxR=1.0
cov_union=0; # union of 2 born charts (ignoring shear, which is a bijection -> image test is on coords 0,1)
# For the SET-cover of the *target* box the relevant obstruction is exactly the coords-0,1 thin sets
# (shear is a global bijection; blow-up only constrains coords 0,1). So test on (x0,x1).
argmax_pivot_cov=0
outgen_manyto2_fail=0
for _ in range(N):
    x=[random.uniform(-boxR,boxR) for _ in range(21)]
    # union of the 2 pivot images:
    if in_image_pivot(x,0) or in_image_pivot(x,1): cov_union+=1
random.seed(1)
# EXACT thin-set check for output-generator many-to-one:
# a col-1 gen (e.g. X01) is dominant on points with x0=x1=0-ish but col1 coords big; assign it to
# pivot q; it fails to be covered by pivot q's chart on the OTHER thin set. Demonstrate a witness.
print(f" MC: union of the 2 born-chart images covers {100*cov_union/N:.3f}% of the box (obstruction only on coords 0,1 thin sets)")

# EXACT witnesses that output-generator many-to-one FAILS:
print("\n Exact witnesses that output-gen->pivot (many-to-one) breaks per-chart containment:")
# Column-1 generator X01 = u12*u4+u16*u5+u2*u8 : independent of x0,x1.
# survivorRegion(X01) contains points in BOTH {x0=0,x1!=0} and {x1=0,x0!=0}.
pt_a = {k:0.0 for k in range(21)}; pt_a[1]=0.5; pt_a[2]=1.0; pt_a[8]=1.0  # x0=0,x1!=0, X01=u2*u8=1 dominant
pt_b = {k:0.0 for k in range(21)}; pt_b[0]=0.5; pt_b[2]=1.0; pt_b[8]=1.0  # x1=0,x0!=0, X01=1 dominant
def x01val(pt): return pt[2]*pt[8]+pt.get(12,0)*pt.get(4,0)+pt.get(16,0)*pt.get(5,0)
print(f"  pt_a: x0=0,x1={pt_a[1]}, X01={x01val(pt_a)} (dominant). In pivot-0 image? {in_image_pivot([pt_a[k] for k in range(21)],0)}  In pivot-1 image? {in_image_pivot([pt_a[k] for k in range(21)],1)}")
print(f"  pt_b: x1=0,x0={pt_b[0]}, X01={x01val(pt_b)} (dominant). In pivot-0 image? {in_image_pivot([pt_b[k] for k in range(21)],0)}  In pivot-1 image? {in_image_pivot([pt_b[k] for k in range(21)],1)}")
print("  => X01's survivor region straddles BOTH thin sets; pivot-0 misses pt_a, pivot-1 misses pt_b.")
print("  => NO single pivot assignment for X01 covers its survivor region (SET containment). ")

# ---------- confirm gen = pivot coordinates (x0,x1) gives clean per-chart containment ----------
print("\n===== gen = pivot coordinates {x0,x1}: per-chart containment holds =====")
print(" survivorRegion(x0) = {x0!=0, |x1|<=R|x0|} ⊆ {x0!=0} ⊆ pivot-0 image (complement of {x0=0,x1!=0}).")
print(" survivorRegion(x1) = {x1!=0, |x0|<=R|x1|} ⊆ {x1!=0} ⊆ pivot-1 image (complement of {x1=0,x0!=0}).")
print(" commonZero{x0,x1} = {x0=x1=0}: codim 2, Lebesgue-null.  => clean 2<->2 correspondence.")
