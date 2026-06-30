"""
Confirm rank Dg(v) - nReg >= 0 at EVERY admissible optimal v, and find where it is TIGHT
(=0, the case the brief calls 'deepest') vs SLACK (>0).

rank Dg(v) = H0*b + a*H2 - a*b   where a=rkA1, b=rkA2.
nReg       = r*(H0+H2-r)         where r = rk(A1 A2).
Admissible: max(0,a+b-H1) <= r <= min(a,b), and 0<=a<=min(H0,H1), 0<=b<=min(H1,H2).

slack(a,b,r) = H0*b + a*H2 - a*b - r*(H0+H2-r).
"""
import sympy as sp

H0, H1, H2, a, b, r = sp.symbols('H0 H1 H2 a b r', integer=True, nonnegative=True)
rankDg = H0*b + a*H2 - a*b
nReg = r*(H0 + H2 - r)
slack = sp.expand(rankDg - nReg)
print("slack = rankDg - nReg =", slack)

# Substitute the worst case r = min(a,b). WLOG check r = a (a<=b) and r = b (b<=a).
# Case r=a (so a<=b): slack = H0 b + a H2 - a b - a(H0+H2-a)
s_ra = sp.expand(slack.subs(r, a))
print("slack at r=a:", sp.factor(s_ra))   # expect (b-a)(H0-a)
s_rb = sp.expand(slack.subs(r, b))
print("slack at r=b:", sp.factor(s_rb))   # expect (a-b)(H2-b)... check sign

# General: slack as function of r is a downward... it's r^2 - r(H0+H2) + (H0 b + a H2 - a b).
# d/dr = 2r-(H0+H2) <0 for r<=min(a,b)<=min(H0,H2)<= (H0+H2)/2, so slack DECREASES in r on
# the admissible range => minimised at r = min(a,b). Confirm both endpoints >=0 under
# r<=a<=H0, r<=b<=H2 type constraints (a<=min(H0,H1), b<=min(H1,H2)).
print()
print("At r=a (a<=b): slack = (b-a)(H0-a). Since a<=b and a<=H0 => >=0. Tight iff a=b or a=H0.")
print("At r=b (b<=a): slack = (a-b)(H2-b). Since b<=a and b<=H2 => >=0. Tight iff a=b or b=H2.")

# Exhaustive numeric sweep over widths up to 6 to be sure NO admissible (a,b,r) gives slack<0.
print()
print("--- exhaustive sweep widths<=6, all admissible (a,b,r): min slack and any negatives ---")
neg = 0
minpos = None
tight_examples = []
for h0 in range(1, 7):
    for h1 in range(1, 7):
        for h2 in range(1, 7):
            for aa in range(0, min(h0, h1)+1):
                for bb in range(0, min(h1, h2)+1):
                    lo = max(0, aa+bb-h1)
                    hi = min(aa, bb)
                    for rr in range(lo, hi+1):
                        val = h0*bb + aa*h2 - aa*bb - rr*(h0+h2-rr)
                        if val < 0:
                            neg += 1
                            print("  NEGATIVE", (h0,h1,h2,aa,bb,rr), val)
                        if val == 0 and rr >= 1:
                            tight_examples.append((h0,h1,h2,aa,bb,rr))
print(f"  negative-slack cases: {neg}")
print(f"  # of TIGHT (slack=0, r>=1) admissible cases up to width 6: {len(tight_examples)}")
print("  sample tight cases (h0,h1,h2,a,b,r):", tight_examples[:8])
# The 'deepest' point in the build = a=b=r (full-rank factors of the rank-r target).
print()
print("  At a=b=r (deepest): slack =", sp.factor(slack.subs({a:r,b:r})))
