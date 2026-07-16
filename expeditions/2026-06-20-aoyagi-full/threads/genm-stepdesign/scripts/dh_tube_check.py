import numpy as np

rng = np.random.default_rng(0)

# Borderline case: b=2, u=2, a=2, d=3 (rho=5, a+b=4 = rho-1). ub=4.
# The claim: keeping B in its box (NOT substituting H=BD, NOT enlarging to R^{ub})
#   T(tau) = INT_{D in box} |det D|^{d-a} * [ INT_{B in box} (||B D||^2 + tau^2)^{-q} dB ] dD
# should behave like tau^{ub - 2q} as tau->0  (tube RECOVERS the full ub = 4),
# and the D-integral must be finite for each tau (d-a = 1 > -1).
#
# Contrast: the NAIVE enlargement gives |det D|^{d-a-u} = |det D|^{-1}, whose D-integral DIVERGES.

b, u, a, d = 2, 2, 2, 3
ub = u*b
q = 1.7   # test exponent; 2q=3.4 < ub=4 so tau^{ub-2q}->0. also test q>2 below.

def inner_B(D, tau, nB=200000):
    # MC over B in [-1,1]^{u x b}: mean of (||B D||^2 + tau^2)^{-q}, times vol(box)=2^{ub}
    B = rng.uniform(-1,1,size=(nB,u,b))
    BD = np.einsum('nij,jk->nik', B, D)      # n x u x d
    nrm2 = np.sum(BD**2, axis=(1,2))
    vals = (nrm2 + tau**2)**(-q)
    return (2**ub)*np.mean(vals)

def T(tau, nD=4000, nB=40000):
    # MC over D in [-1,1]^{b x b}: mean of |det D|^{d-a} * inner_B, times vol=2^{b*b}
    acc = 0.0
    Ds = rng.uniform(-1,1,size=(nD,b,b))
    for D in Ds:
        dw = abs(np.linalg.det(D))**(d-a)
        acc += dw*inner_B(D, tau, nB=nB)
    return (2**(b*b))*acc/nD

# Also the D-integral of the NAIVE enlarged weight |det D|^{d-a-u} = |det D|^{-1}: should look divergent
def naive_D_integral(nD=2000000, eps=None):
    Ds = rng.uniform(-1,1,size=(nD,b,b))
    dets = np.abs(np.linalg.det(Ds))
    w = dets**(d-a-u)   # |det D|^{-1}
    return (2**(b*b))*np.mean(w)

taus = [0.2, 0.1, 0.05, 0.025]
print(f"# case b={b} u={u} a={a} d={d}  ub={ub}  q={q}  2q={2*q}")
Tvals=[]
for tau in taus:
    val = T(tau, nD=3000, nB=30000)
    Tvals.append(val)
    print(f"tau={tau:.4f}  T={val:.5e}")
# effective exponent gamma from consecutive ratios: T ~ tau^{gamma-2q}
print("# effective (gamma-2q) slopes (log-log), and implied gamma  [expect gamma ~ ub=4]:")
for i in range(len(taus)-1):
    slope = np.log(Tvals[i+1]/Tvals[i])/np.log(taus[i+1]/taus[i])
    print(f"  tau {taus[i]:.3f}->{taus[i+1]:.3f}: slope={slope:.3f}  gamma={slope+2*q:.3f}")

print("\n# NAIVE enlarged D-weight |det D|^{-1} integral (MC estimate; diverges log => grows with nD):")
for nD in [200000, 800000, 3200000]:
    print(f"  nD={nD:>8}: est={naive_D_integral(nD):.4f}")
