import sympy as sp
a,b = sp.symbols('a b', real=True)
# Z = a*b (1x1 product). corank(Z)=1 on {ab=0}. Codex's counterexample: at a=b=0, m>1 but corank stays 1.
sigmin = sp.Abs(a*b)   # σ_min of the 1x1 matrix
# distance to the singular locus {ab=0} = {a=0} ∪ {b=0}:  dist = min(|a|,|b|)
# m=1 would require σ_min² ≍ dist². Check on the diagonal a=b=t→0:
t=sp.symbols('t', positive=True)
sig_diag = (a*b).subs({a:t,b:t})          # = t^2
dist_diag = sp.Min(t,t)                     # = t
print(f"[Z=ab, diagonal a=b=t]  σ_min = {sig_diag} = t²;  dist({{ab=0}}) = {dist_diag} = t")
print(f"   σ_min² = t⁴  vs  dist² = t²  →  σ_min² ≍ dist²?  NO (t⁴ ≠ t²). m=1 FAILS at the crossing a=b=0.")
print(f"   corank(Z) at a=b=0 = 1 (the 1×1 zero); NO higher-corank stratum catches it.  [Codex's catch CONFIRMED]")
# The crossing a=b=0 is the INTERSECTION RAY (both factors degenerate) — handled by the ITERATED/coupled corner,
# NOT by a corank-of-Z stratum. σ_min=|ab| is the coupled-corner monomial, resolved by blowing up a=b=0.
print(f"\n   ⟹ the non-transverse (m>1) locus = the INTERSECTION RAY (both product factors vanish).")
print(f"     NOT caught by corank-of-Z; IS the coupled corner (blow up a=b=0: a=u, b=uτ ⟹ ab=u²τ, the u₀²·unit form).")
print(f"     Well-founded recursion variable = ARITY (peel a factor), NOT corank(Z). Intersection rays = the iterated corner.")
