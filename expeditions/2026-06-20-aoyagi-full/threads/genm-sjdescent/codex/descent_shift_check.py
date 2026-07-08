import numpy as np
from numpy.random import default_rng

# Probe the EFFECTIVE exponent shift of the inner Gamma-integral
#   I(W) = ∫_{Γ ∈ [-T,T]^{a×b}} ( W + frobSq(C0 + Γ·Qb) )^{-c'} dΓ
# as W -> 0.  Claim under test: I(W) ~ const · W^{-(c' - shift/2)} with
#   shift = a·s   (s = rank Qb)   NOT   a·b   (the pinned peelCharge).
# We estimate the shift by fitting log I(W) vs log W over small W.

rng = default_rng(0)

def frobSq(M): return float(np.sum(M*M))

def inner_integral(a, b, C0, Qb, W, cprime, T=3.0, N=200000):
    # Monte-Carlo over Γ uniform on [-T,T]^{a×b}; volume = (2T)^{a b}
    ab = a*b
    G = rng.uniform(-T, T, size=(N, a, b))
    vals = np.empty(N)
    for k in range(N):
        R = C0 + G[k] @ Qb            # a×n
        vals[k] = (W + frobSq(R))**(-cprime)
    vol = (2*T)**ab
    return vol*vals.mean(), vol*vals.std()/np.sqrt(N)

def estimate_shift(a, b, n, s, cprime, seed=1):
    r = default_rng(seed)
    # Qb: b×n with rank exactly s  (s <= min(b,n))
    U = r.standard_normal((b, s)); V = r.standard_normal((s, n))
    Qb = U @ V                        # rank s
    C0 = r.standard_normal((a, n))    # generic offset (nonzero)
    # sanity: numeric rank of Qb
    srank = np.linalg.matrix_rank(Qb, tol=1e-8)
    Ws = np.array([1e-1, 3e-2, 1e-2, 3e-3, 1e-3, 3e-4, 1e-4])
    Is = []
    for W in Ws:
        val,_ = inner_integral(a,b,C0,Qb,W,cprime)
        Is.append(val)
    Is = np.array(Is)
    # fit log I = A - alpha log W  over the smallest few W (asymptotic regime)
    lw, li = np.log(Ws), np.log(Is)
    # use smallest 4 points
    A = np.vstack([np.ones(4), -lw[-4:]]).T
    coef,_,_,_ = np.linalg.lstsq(A, li[-4:], rcond=None)
    alpha = coef[1]                   # I ~ W^{-alpha}
    shift_est = 2*(cprime - alpha)    # since alpha = c' - shift/2  =>  shift = 2(c'-alpha)
    return srank, alpha, shift_est

# Case: a=1, b=3, n=1  (M=(2,4,1), t=1 chart).  s = rank Qb <= min(3,1)=1.
for (a,b,n) in [(1,3,1),(2,3,1),(2,4,2),(1,2,1)]:
    s = min(b,n)
    # need c' > ab/2 for a clear power law under the pinned claim; use c' well above
    cprime = a*b/2 + 1.5
    srank, alpha, shift = estimate_shift(a,b,n,s,cprime)
    print(f"a={a} b={b} n={n}: rank(Qb)={srank}  c'={cprime:.2f}  "
          f"alpha(fit)={alpha:.3f}  shift_est={shift:.3f}   ab={a*b}  a*s={a*srank}")
