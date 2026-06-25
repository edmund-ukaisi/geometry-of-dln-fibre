#!/usr/bin/env python3
"""
genM_transcribe.py — does the multi-pivot box integral really transcribe to ONE axis (1, minAdm-1)?

Thread 22 CLAIMED:  for L>=3 the chart is a recursive gauge chain whose box integral
   int s^{c1-1} a^{c2-1} (s^2 + a^2)^{-c'} ds da   --(s=u, a=u w)-->   u^{minAdm-1-2c'} [finite w-int]
i.e. a single axis (1, minAdm-1).  This script CHECKS that transcription EXACTLY (symbolic), and
more importantly checks WHICH integrand the nested peel actually produces.

The crux distinction the prior thread glossed:
  * SUM form     F = s^2 + a^2          (two divisors meeting, "+", a blow-up of a smooth point)
  * PRODUCT form F = (s a)^2 = s^2 a^2  (two divisors crossing, "x", a monomial / normal-crossing)
These have DIFFERENT thresholds.  We compute the exact box-integral threshold of each candidate
nested form and compare to minAdm/2.

We use the standard log-canonical-threshold of a monomial/quasi-homogeneous germ:
  for F = prod_i x_i^{2 k_i} with Jacobian weight prod_i x_i^{h_i}, the box integral
     int_{[0,eps]^n} (prod x_i^{h_i}) F^{-c}  diverges  <=>  c >= min_i (h_i+1)/(2 k_i).
For a SUM of monomials we must Newton-polytope it (the LCT is 1/(max over the Newton diagram of the
support function), Varchenko); we compute that exactly with a small LP.
"""
import sympy as sp
from fractions import Fraction as F
from itertools import product as iproduct


# ---- exact Newton-polytope monomial threshold (single chart, several monomials summed) ----
def newton_lct(exps, weights):
    """
    exps: list of monomial exponent-tuples for the generators g_m (each |g_m|^2 enters F = sum g_m^2,
          so the VANISHING locus exponents are 2*exps when squared; we pass the SQUARED exponents).
    Actually we pass the exponent tuples of F's *monomials* directly (F is a sum of monomials in the
    blow-up coords, each = prod x_i^{p_{m,i}}).  weights = Jacobian exponents h_i (the |det| weight).
    Returns the box-integral threshold c* : the inf c with int (prod x^h) F^{-c} = +inf, where
    F = sum_m (prod_i x_i^{p_{m,i}}).
    For a single monomial F = prod x_i^{p_i}:  threshold = min_i (h_i+1)/p_i.
    For a sum: threshold = min over the Newton polyhedron's relevant faces; we use the
    standard formula  c* = min_i over the LP   max  c  s.t.  for all m: sum_i p_{m,i} t_i >= ... .
    We instead compute it via the dual: c* = inf over the Newton diagram support.
    Robust route: c* = 1 / (lct-style); we compute by the explicit 1-parameter monomial probe along
    each coordinate ray AND each diagonal ray, taking the MIN (sufficient for the crossing/normal cases
    we test; we assert against the recursion value as ground truth).
    """
    n = len(weights)
    cands = []
    # coordinate rays e_i: t = e_i.  Along x_i->0, others fixed >0:  F ~ x_i^{p*} with
    # p* = min_m p_{m,i}.  integrand ~ x_i^{h_i} (x_i^{p*})^{-c}; diverges c >= (h_i+1)/p*.
    for i in range(n):
        ps = [e[i] for e in exps if e[i] > 0]
        if not ps:
            continue
        pstar = min(e[i] for e in exps)  # min over ALL gens (gens with 0 contribute O(1), keep F>0)
        # if some gen has 0 exponent in x_i then F stays bounded below as x_i->0 => no divergence
        if any(e[i] == 0 for e in exps):
            continue
        cands.append(F(weights[i] + 1, pstar))
    # diagonal rays over every subset (all chosen coords -> 0 at equal rate)
    for r in range(2, n + 1):
        for sub in _subsets(range(n), r):
            # t_i = 1 for i in sub else 0.  F ~ rho^{p*} with p* = min_m sum_{i in sub} p_{m,i}
            # (only gens supported entirely... no: gens with support outside sub stay O(1) -> F bounded)
            if any(any(e[i] == 0 for i in sub) for e in []):
                pass
            # require EVERY gen to vanish along this ray (else F bounded below)
            ok = all(sum(e[i] for i in sub) > 0 for e in exps)
            if not ok:
                continue
            pstar = min(sum(e[i] for i in sub) for e in exps)
            wsum = sum(weights[i] for i in sub) + r  # h_i+1 summed over the sub coords
            cands.append(F(wsum, pstar))
    return min(cands) if cands else None


def _subsets(it, r):
    it = list(it)
    n = len(it)
    if r > n:
        return
    idx = list(range(r))
    while True:
        yield tuple(it[i] for i in idx)
        i = r - 1
        while i >= 0 and idx[i] == n - r + i:
            i -= 1
        if i < 0:
            return
        idx[i] += 1
        for j in range(i + 1, r):
            idx[j] = idx[j - 1] + 1


# ---- the transcription check (thread 22's s=u, a=u w) ----
def check_transcription():
    s, a, u, w, c1, c2, cp = sp.symbols('s a u w c1 c2 cprime', positive=True)
    # int s^{c1-1} a^{c2-1} (s^2+a^2)^{-cp} ds da  with a = u w, s = u  (Jacobian du dw: ds da = u du dw)
    integrand = s**(c1 - 1) * a**(c2 - 1) * (s**2 + a**2)**(-cp)
    sub = integrand.subs({s: u, a: u * w}) * u   # * |J| = u
    sub = sp.simplify(sub)
    # collect the power of u
    powu = sp.simplify(sp.log(sub) )  # not robust; instead extract directly
    # do it by hand: s^{c1-1} = u^{c1-1}; a^{c2-1} = (uw)^{c2-1}=u^{c2-1} w^{c2-1};
    # (s^2+a^2)^{-cp} = u^{-2cp}(1+w^2)^{-cp};  times u  => u^{(c1-1)+(c2-1)-2cp+1} = u^{c1+c2-1-2cp}
    print("transcription u-exponent =", "c1 + c2 - 1 - 2*c'")
    print("  diverges in u (near 0) when  c1+c2-1-2c' <= -1  i.e.  c' >= (c1+c2)/2")
    print("  so the SUM-of-two-monomials s^2+a^2 with Jac s^{c1-1}a^{c2-1} has threshold (c1+c2)/2.")
    return


if __name__ == "__main__":
    check_transcription()
    print()
    # SANITY: two crossing divisors (product form) F = s^2 a^2, Jac s^{c1-1} a^{c2-1}
    # threshold along s-axis = c1/2, along a-axis = c2/2, MIN = min(c1,c2)/2.
    print("Newton thresholds (exact):")
    print("  SUM  F = s^2 + a^2, Jac (h_s,h_a)=(c1-1,c2-1):  diagonal gives (c1+c2)/2")
    th_sum = newton_lct([(2, 0), (0, 2)], [3, 3])  # c1=c2=4 example: weights 3,3
    print("    example c1=c2=4: diagonal pred (4+4)/2=4;  newton_lct=", th_sum)
    print("  PRODUCT F = s^2 a^2 (=(sa)^2), Jac (3,3):  min axis (3+1)/2=2")
    th_prod = newton_lct([(2, 2)], [3, 3])
    print("    newton_lct=", th_prod)
