import numpy as np

# Front charge Ch(S) = int_{A in [-T,T]^{b x n}} det( (A S)(A S)^T )^{-a/2} dA
# Test: b, a, rho.  S = I_rho (n=p=rho), so A is b x rho, P = A S = A, Gram = A A^T (b x b).
# Probe: dyadic-shell mass.  For each dyadic level k, estimate the integral-mass
# contributed by samples with det(Gram) in [2^{-(k+1)}, 2^{-k}].
# Signature:
#   convergent  -> shell mass decays to 0 as k->inf
#   log-diverge -> shell mass ~ CONSTANT per octave
#   power-diverge -> shell mass grows

rng = np.random.default_rng(12345)

def shell_masses(b, a, rho, T=1.0, N=8_000_000, kmax=26):
    # sample A uniform in [-T,T]^{b x rho}
    A = rng.uniform(-T, T, size=(N, b, rho))
    G = np.einsum('nij,nkj->nik', A, A)          # A A^T, shape N,b,b
    det = np.linalg.det(G)
    det = np.maximum(det, 0.0)
    vol = (2*T)**(b*rho)                          # box volume
    # integrand = det^{-a/2}
    # Monte-Carlo estimate of int over {det in shell} = vol * mean( det^{-a/2} * 1_shell )
    masses = []
    for k in range(kmax):
        hi = 2.0**(-k)
        lo = 2.0**(-(k+1))
        mask = (det > lo) & (det <= hi)
        if mask.sum() == 0:
            masses.append((k, lo, hi, 0.0, 0))
            continue
        integ = det[mask]**(-a/2.0)
        m = vol * integ.sum() / N
        masses.append((k, lo, hi, m, int(mask.sum())))
    return masses

for (b,a,rho,label) in [(2,2,3,'EDGE  a+b=rho+1 (predict LOG-DIVERGE)'),
                        (2,2,4,'INTERIOR a+b=rho  (predict CONVERGE)'),
                        (2,3,3,'DEEP a+b=rho+2 (predict POWER-DIVERGE)'),
                        (1,1,1,'b=1 edge rho=a (predict LOG-DIVERGE)'),
                        (1,1,2,'b=1 interior a+b=rho (predict CONVERGE)')]:
    print('='*70)
    print(f'b={b} a={a} rho={rho}  |  {label}')
    ms = shell_masses(b,a,rho)
    print(f'{"k":>3} {"shell (lo,hi]":>22} {"shell-mass":>14} {"nsamp":>9}')
    tot = 0.0
    for (k,lo,hi,m,ns) in ms:
        tot += m
        print(f'{k:>3} ({lo:.2e},{hi:.2e}] {m:>14.5f} {ns:>9}')
    print(f'  cumulative mass over shells = {tot:.4f}  (+ bulk det>1 not shown)')
