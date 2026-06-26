"""theta adjudication certificate (exact algebra, no floats load-bearing).

Adjudicates whether the two published "theta" invariants are the same:
  theta_LR     = C(m, |delta|)            Lehalleur-Rimanyi 2024, Thm main-codim (eqn:number_top_comp)
                                            = # top-dimensional irreducible components of Sigma^0_d
                                            = # of optimal solutions of the QIP (Thm QIP)
  theta_Aoyagi = a(ell - a) + 1            Aoyagi 2023, Theorem 2 (deep DLN), order of the maximal pole

with, for a weakly-increasing shifted-width vector dp = d' (r already subtracted):
  m   = max{ l in 1..N : sum_{i=0..l} dp_i >= l*dp_l }          (LR Def d1 == Aoyagi ell)
  S   = sum_{i=0..m} dp_i
  delta = S - m*round(S/m),  round(x)=floor(x+1/2)              (LR eqn:delta)
  M   = ceil(S/m),   a = S - (M-1)*m                            (Aoyagi residue; a in 1..m)

Results (run me):
  * For (2,2,2,2,2), r=0: lambda agree EXACTLY (3/2 == 3/2) but theta_LR=6 != theta_Aoyagi=5.
  * The true count (direct exhaustive QIP enumeration) = 6 = C(4,2) = theta_LR.
  * theta_LR == direct-QIP-optimum-count : 0 mismatches over the sweep (LR closed form faithful).
  * theta_Aoyagi == theta_LR  <=>  |delta| <= 1  (purely a function of (m,|delta|)).
"""
import itertools, math
from fractions import Fraction as F


def lr_m(dp):
    N = len(dp) - 1
    best = 1
    for l in range(1, N + 1):
        if sum(dp[i] for i in range(l + 1)) >= l * dp[l]:
            best = l
    return best


def lr_S(dp, m):
    return sum(dp[i] for i in range(m + 1))


def lr_delta(dp):
    m = lr_m(dp); S = lr_S(dp, m)
    fl = (2 * S + m) // (2 * m)          # floor(S/m + 1/2)
    return S - m * fl


def theta_LR(dp):
    m = lr_m(dp)
    return math.comb(m, abs(lr_delta(dp)))


def aoyagi_a(dp):
    m = lr_m(dp); S = lr_S(dp, m)
    M = (S + m - 1) // m                  # ceil(S/m)
    return S - (M - 1) * m                # residue a in {1..m}


def theta_Aoyagi(dp):
    m = lr_m(dp)
    a = aoyagi_a(dp)
    return a * (m - a) + 1


def qip_min_and_count(dp):
    """Direct exhaustive QIP (LR eq:QIP): min G over e in N^N with sum e_i = d'_0."""
    N = len(dp) - 1; d0 = dp[0]

    def G(e):
        tot = 0
        for i in range(1, N + 1):
            for j in range(1, i + 1):
                tot += e[i - 1] * (e[j - 1] + dp[j] - dp[j - 1])
        return tot

    def comps(total, parts):
        if parts == 1:
            yield (total,); return
        for first in range(total + 1):
            for rest in comps(total - first, parts - 1):
                yield (first,) + rest

    best = None; cnt = 0; opt = []
    for e in comps(d0, N):
        g = G(list(e))
        if best is None or g < best:
            best, cnt, opt = g, 1, [e]
        elif g == best:
            cnt += 1; opt.append(e)
    return best, cnt, opt


def lr_codim(dp):
    """LR thm:main-codim r=0 closed form (exact rational)."""
    m = lr_m(dp); S = lr_S(dp, m)
    frac = F(S, m) - (S // m)
    return (F(m, 2) * frac * (1 - frac) - F(m * (m - 1), 2) * F(S, m) ** 2
            + sum(dp[i] * dp[j] for i in range(m + 1) for j in range(i + 1, m + 1)))


def aoyagi_lambda_equalwidth(L, M1, r):
    """Aoyagi Thm-2 Example (all M^(s) equal), exact rational lambda."""
    M = math.ceil(F(L + 1, L) * M1)
    a = (L + 1) * M1 - (M - 1) * L
    return F(-r * r + 2 * r * M1, 2) + F(a * (L - a), 4 * L) + F(L + 1, 4 * L) * M1 ** 2


def crux_222222():
    dp = [2, 2, 2, 2, 2]
    minval, cnt, opt = qip_min_and_count(dp)
    print("=== CRUX: (2,2,2,2,2), r=0 ===")
    print(f" LR codim = {lr_codim(dp)}  => lambda_LR = codim/2 = {lr_codim(dp)/2}")
    print(f" lambda_Aoyagi (Example, L=4,M1=2,r=0) = {aoyagi_lambda_equalwidth(4,2,0)}")
    print(f" lambdas equal? {lr_codim(dp)/2 == aoyagi_lambda_equalwidth(4,2,0)}")
    print(f" theta_LR = C({lr_m(dp)},{abs(lr_delta(dp))}) = {theta_LR(dp)}")
    print(f" theta_Aoyagi = a(ell-a)+1, a={aoyagi_a(dp)}, ell={lr_m(dp)} = {theta_Aoyagi(dp)}")
    print(f" DIRECT exhaustive QIP optimum count (= # top components) = {cnt} at min value {minval}")
    print(f" optima: {opt}")
    assert cnt == theta_LR(dp) == 6
    assert theta_Aoyagi(dp) == 5
    assert lr_codim(dp) / 2 == aoyagi_lambda_equalwidth(4, 2, 0)


def sweep():
    mism_closed = []; differ = []; checked = 0
    for N1 in range(2, 6):
        for tup in itertools.combinations_with_replacement(range(1, 6), N1):
            dp = list(tup)
            checked += 1
            _, cnt, _ = qip_min_and_count(dp)
            if theta_LR(dp) != cnt:
                mism_closed.append((dp, theta_LR(dp), cnt))
            if theta_Aoyagi(dp) != theta_LR(dp):
                differ.append((dp, lr_m(dp), lr_delta(dp), theta_LR(dp), theta_Aoyagi(dp)))
    print(f"\n=== SWEEP (len2..5, widths1..5): {checked} vectors ===")
    print(f" theta_LR == direct-QIP-count : {len(mism_closed)} mismatches  (LR closed form faithful)")
    print(f" theta_Aoyagi != theta_LR     : {len(differ)} cases; all have |delta|>=2:")
    print(f"   |delta| of differing cases : {sorted(set(abs(d) for _,_,d,_,_ in differ))}")
    assert len(mism_closed) == 0
    assert all(abs(d) >= 2 for _, _, d, _, _ in differ)


def mb_table():
    """Decouple from dim vectors: theta as a function of (m,b), b=S mod m."""
    print("\n=== (m,b) decoupling: a, |delta|, theta_Aoyagi, theta_LR ===")
    for m in range(1, 8):
        for b in range(0, m):
            a = m if b == 0 else b
            if 2 * b <= m:
                absd = b
            else:
                absd = m - b
            ta = a * (m - a) + 1
            tl = math.comb(m, absd)
            flag = "  DIFFER" if ta != tl else ""
            if m <= 6:
                print(f"  m={m} b={b} a={a} |delta|={absd}  theta_Aoy={ta}  theta_LR={tl}{flag}")


if __name__ == "__main__":
    crux_222222()
    sweep()
    mb_table()
    print("\nAll assertions passed.")
