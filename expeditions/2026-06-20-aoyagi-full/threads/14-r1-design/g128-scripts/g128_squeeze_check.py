import sympy as sp, numpy as np
# Verify the squeeze c1(ΣE²+G²) ≤ F ≤ c2(ΣE²+G²) near 0 for (2,2,2) r=1.
# F = g00²+g01²+g10²+g11². E1=g00,E2=g01,E3=g10 (regular), G = Schur core = g11 on regular-zero locus.
# But ΣE²+G²: E_i are the regular generators (functions of w), G the core. Compute F vs ΣE_i²+G² ratio.
w = sp.symbols('w0:8', real=True)
W1=sp.Matrix([[w[0],w[1]],[w[2],w[3]]]); W2=sp.Matrix([[w[4],w[5]],[w[6],w[7]]])
v1=sp.Matrix([[1,0],[0,0]]); v2=sp.Matrix([[1,0],[0,0]]); B=v1*v2
P=sp.expand((v1+W1)*(v2+W2))
g=[sp.expand((P-B)[i,j]) for i in range(2) for j in range(2)]
F = sum(gi**2 for gi in g)
# G = g11 on {g00=g01=g10=0}: G = −w3 w7/(w1 w6−1). But as a function of ALL w (not on the locus),
# the "core" for the squeeze should be g11 itself OR G(w0,w1,w3,w6,w7). Use the comparison form
# Phi = g00²+g01²+g10² + G_full² where G_full = g11 (the actual 4th generator). Then F = Phi exactly!
# (F IS g00²+g01²+g10²+g11².) So the squeeze F vs ΣE²+G² is really g11² vs G²(reduced).
# The real comparison: rlctAt(g00²+g01²+g10²+g11²) vs rlctAt(g00²+g01²+g10²+G²), G=g11 mod regular.
# g11 = w2 w5 + w3 w7. G (reduced) = g11 − (combo). On the regular block, g11 and G differ by terms in
# the ideal (g00,g01,g10). The squeeze is between F=Σg² and Phi=g00²+g01²+g10²+G².
fF = sp.lambdify(w, F, 'numpy')
G_red = -w[3]*w[7]/(w[1]*w[6]-1)
Phi = g[0]**2+g[1]**2+g[2]**2+G_red**2
fPhi = sp.lambdify(w, Phi, 'numpy')
np.random.seed(0)
ratios=[]
for scale in [0.3,0.1,0.03,0.01]:
    X = np.random.randn(20000,8)*scale
    vals_F = fF(*[X[:,i] for i in range(8)])
    vals_Phi = fPhi(*[X[:,i] for i in range(8)])
    mask = vals_Phi > 1e-30
    r = vals_F[mask]/vals_Phi[mask]
    ratios.append((scale, np.min(r), np.max(r), np.median(r)))
print("=== squeeze F / Phi (Phi = g00²+g01²+g10²+G_reduced²), near 0 ===")
print("scale  min(F/Phi)  max(F/Phi)  median")
for s,mn,mx,md in ratios:
    print(f"{s:6.3f}  {mn:9.4f}  {mx:11.4e}  {md:.4f}")
print()
print("If min stays bounded BELOW by c1>0 and max bounded ABOVE by c2<∞ as scale→0, the squeeze HOLDS")
print("=> rlctAt(F)=rlctAt(Phi). If max BLOWS UP (→∞), the upper squeeze FAILS (Phi vanishes faster than F).")
