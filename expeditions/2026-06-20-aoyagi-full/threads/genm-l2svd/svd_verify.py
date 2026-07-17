import numpy as np
import sympy as sp

print("="*70)
print("CLAIM 1: frobSq(Gamma*S) is a PSD quadratic form in Gamma of rank a*rank(S)")
print("="*70)
# symbolic: a=2, b=3, q=2, S rank 2 (b=3 -> corank), check frobSq = sum_i Gamma_i (S S^T) Gamma_i^T
a, b, q = 2, 3, 2
# S: b x q, choose rank 2
S = sp.Matrix([[1,0],[0,1],[1,1]])  # 3x2, rank 2
r = S.rank()
print(f"a={a}, b={b}, q={q}, rank(S)={r}, a*rank(S)={a*r}")
G = S*S.T  # b x b Gram
print("Gram S S^T rank =", G.rank(), "(should equal rank(S) =", r, ")")

# Gamma a x b symbolic
Gsym = sp.Matrix(a, b, lambda i,j: sp.Symbol(f'g{i}{j}'))
GS = Gsym*S           # a x q
frob = sum(GS[i,j]**2 for i in range(a) for j in range(q))
frob = sp.expand(frob)
# compare to sum_i Gamma_i G Gamma_i^T
gram_form = 0
for i in range(a):
    row = Gsym[i,:]           # 1 x b
    gram_form += (row*G*row.T)[0,0]
gram_form = sp.expand(gram_form)
print("frobSq(GS) == sum_i Gamma_i (S S^T) Gamma_i^T :", sp.simplify(frob-gram_form)==0)

# rank of the quadratic form in the a*b variables = a * rank(G)
vars_ = list(Gsym)
Hess = sp.hessian(frob, vars_)/2   # the symmetric matrix of the quadratic form
print("rank of quadratic-form matrix =", Hess.rank(), " expected a*rank(S) =", a*r)

print()
print("="*70)
print("CLAIM 2: threshold 2c' < a*rank(S) is exact & tight (BOUNDED box), Morse")
print("="*70)
# After orthogonal CoV diagonalising G, integrand = (sum_{i, j<=r} sigma_j^2 y_{ij}^2)^{-c'}
# a PD form in n = a*r active vars. Radial: finite over bounded ball iff c' < n/2.
# Numerically confirm with Monte-Carlo-free exact 1D radial reduction:
# int_{ball_R} rho^{-2c'} dy_active ~ int_0^R rho^{-2c'} rho^{n-1} drho, finite iff n-2c' > 0.
def radial_finite(n, cp):
    # exponent of rho after polar: n-1-2cp ; integrable at 0 iff n-1-2cp > -1 iff 2cp < n
    return (n-1-2*cp) > -1
for (aa,rr) in [(2,1),(2,2),(2,3),(3,2)]:
    n=aa*rr
    thr=n/2
    for cp in [thr-0.2, thr-1e-9, thr+0.2]:
        print(f"  a={aa} r={rr} n={n} thr(c')={thr}  c'={cp:.3f} -> finite={radial_finite(n,cp)} (want c'<{thr})")

print()
print("="*70)
print("CLAIM 3: hbox: volume box < top is INSUFFICIENT (counterexample)")
print("="*70)
# a=b=2, q=1, S = [[1],[0]] (2x1, rank 1). rank(S)=1, a*rank(S)=2, threshold c'<1.
# frobSq(Gamma S) = g00^2 + g10^2 (active); g01,g11 free.
# box = { rho=sqrt(g00^2+g10^2) < 1 ; 0<g01< rho^{-beta} ; 0<g11<1 }, beta in (0,2) -> finite vol.
# vol = int_disk rho^{-beta} dA = 2pi int_0^1 rho^{1-beta} drho finite iff beta<2.
# integral = int_disk rho^{-2c'} * rho^{-beta} dA = 2pi int_0^1 rho^{1-2c'-beta} drho finite iff 2c'+beta<2.
import scipy.integrate as si
def counterexample(cp, beta, R=1.0):
    # exact 1D: I = 2pi * int_0^R rho^{1-2c'-beta} drho ; vol = 2pi* int_0^R rho^{1-beta} drho
    expo_I = 1-2*cp-beta
    expo_V = 1-beta
    vol_finite = expo_V > -1
    I_finite = expo_I > -1
    return vol_finite, I_finite
cp, beta = 0.9, 0.5   # c'=0.9 < 1 (WITHIN threshold), beta=0.5 (<2, finite vol)
vf, If = counterexample(cp,beta)
print(f"  a=b=2, rank(S)=1, threshold c'<1;  c'={cp} (WITHIN), beta={beta}")
print(f"    box has finite volume: {vf};   integral finite: {If}")
print(f"    => c' within threshold but integral DIVERGES on a finite-VOLUME box: {vf and not If}")
# numeric sanity: actually integrate over the box with a cutoff to show growth
def numeric_box_integral(cp, beta, eps):
    # I(eps) = 2pi int_eps^1 rho^{1-2cp-beta} drho ; blows up as eps->0 iff 1-2cp-beta <= -1
    from scipy.integrate import quad
    f=lambda rho: rho**(1-2*cp-beta)
    val,_=quad(f, eps, 1.0)
    return 2*np.pi*val
for eps in [1e-1,1e-3,1e-6,1e-9]:
    print(f"    partial integral (cutoff eps={eps:.0e}) = {numeric_box_integral(cp,beta,eps):.4f}")
print("  (grows without bound as eps->0  =>  divergent, confirming counterexample)")
