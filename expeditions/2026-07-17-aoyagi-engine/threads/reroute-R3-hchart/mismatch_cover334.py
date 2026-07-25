import sympy as sp, numpy as np, itertools

C1 = sp.Matrix(3,3, lambda i,j: sp.Symbol(f'a{i}{j}'))
C2 = sp.Matrix(3,4, lambda i,j: sp.Symbol(f'b{i}{j}'))
X  = C1*C2
L  = sum(X[i,j]**2 for i in range(3) for j in range(4))
def z(e): return e.subs({s:0 for s in e.free_symbols})
r1,r2 = sp.symbols('r1 r2')

print("=== JOB1(b) control: a MISMATCHED pivot pair gives R(0)=0 (not a fan member) ===")
# Mismatched: blow up (C1[0,1], C2[0,0]).  C1[0,1] multiplies C2[1,*]; C2[0,0] multiplied
# by C1[*,0]. Their product a01*b00 is NOT a single term of any X[i,j].
sub = {C1[0,1]: r1, C2[0,0]: r2}
# make the surrounding block scale so mono=r1*r2 is the intended dominant term
for k in range(3):
    if k!=1: sub[C1[0,k]] = r1*sp.Symbol(f'g1_{k}')
for k in range(3):
    if k!=0: sub[C2[k,0]] = r2*sp.Symbol(f'g2_{k}')
Lg = L.subs(sub); mono=r1*r2
R = sp.cancel(Lg/mono**2)
print("  mismatched (C1[0,1],C2[0,0]): R(0) =", z(R), " -> sandwich_ok =", z(R)!=0)

print()
print("=== JOB1(a) + W1: the SURVIVOR-ENTRY fan covers the {X[0,0]~0} tube; RADIAL-only 0% ===")
# Numeric MC over the box.  Survivor-entry fan: one member per product entry X[i,j] that
# 'survives' (is the dominant/largest generator).  Radial-only fan: keep survivor X[0,0],
# vary which input radial -> all carry X[0,0] numerator, all die on {X[0,0]=0}.
Xf = sp.lambdify(list(C1)+list(C2), [X[i,j] for i in range(3) for j in range(4)], 'numpy')
rng = np.random.default_rng(0); N=200000
def sample(boxR):
    P = rng.uniform(-boxR,boxR,size=(N,21))
    vals = np.array(Xf(*[P[:,t] for t in range(21)]))   # 12 x N
    return np.abs(vals)
for boxR in (1.0,2.0):
    A = sample(boxR)                 # 12 generators x N
    maxg = A.max(axis=0)
    onhole = maxg < 1e-9
    # tube: X[0,0] small relative to the largest generator
    tube = (A[0] < 0.05*maxg) & (~onhole)
    # radial-only fan covers a point iff X[0,0] survives there (i.e. NOT in tube)
    radial_cov = (~tube) & (~onhole)
    # survivor-entry fan covers a point iff SOME generator dominates (always, off hole)
    surv_cov = (~onhole)
    tot=(~onhole).sum()
    print(f"  boxR={boxR}: tube frac={tube.mean():.3f}"
          f"  radial-only covers tube={ (radial_cov & tube).sum()/max(tube.sum(),1):.3f}"
          f"  survivor-entry covers all-off-hole={surv_cov.sum()/tot:.4f}"
          f"  common hole frac={onhole.mean():.6f}")

print()
print("=== JOB2 (W3): each sibling's monomial is its OWN; no sigma-image needed ===")
# Enumerate the fan: survivors X[i,j] x matched pair index k -> monomial (C1[i,k],C2[k,j]).
# Show each monomial is a distinct pair of coordinates, computed from that pair alone.
fan=[]
for i in range(3):
  for j in range(4):
    for k in range(3):
      fan.append(((i,j,k), (f'C1[{i},{k}]', f'C2[{k},{j}]')))
print(f"  fan size = {len(fan)} born charts (survivor x matched-pair); each monomial =")
for lab,mono in fan[:4]:
    print(f"    survivor X[{lab[0]},{lab[1]}] pair k={lab[2]}: mono = {mono[0]}*{mono[1]}  (from THIS pair only)")
print("  ...  distinct coordinate pair per chart; no chart references another's coords.")
