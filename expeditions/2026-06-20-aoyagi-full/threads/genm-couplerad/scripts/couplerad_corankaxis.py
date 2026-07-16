"""
couplerad_corankaxis.py -- does my E-recursion route/reduce the deep corank cuts (a+b>=rho+2)?
ANSWER: NO. The corank-cut axis (a,b, from the FRONT peel) is ORTHOGONAL to the deep-factor rank axis
(rank S = rank Z_deep) that my E-recursion + deepCover_aux resolve.

Charge int_Acor det((Acor S)(Acor S)^T)^{-a/2} finite iff a+b <= rank(S). E-recursion steps rank S down
(rho, rho-1, ...). k_eff(r) := (a+b) - r = corank-excess at rank level r. Reducing rank S raises k_eff.
For a deep cut a+b >= rho+2: a+b > rho >= rank S at EVERY level => charge non-integrable everywhere =>
E-recursion never starts, and cannot reduce k>=2 to k<=1.
"""
for rho in [4, 5, 6]:
    for k in [1, 2, 3]:
        ab = rho + k
        levels = []
        for drop in range(0, 3):
            r = rho - drop
            levels.append(f"rankS={r}:k_eff={ab-r}({'INT' if ab<=r else 'NON-int'})")
        print(f"rho={rho} cut a+b={ab}(k={k}): " + "  ".join(levels))
print()
print("=> reducing rank S RAISES k_eff (rho_eff shrinks). a+b>=rho+2 is charge-non-integrable at ALL levels")
print("   => E-recursion never starts; CANNOT reduce k>=2 corank cuts to k<=1. Corank-cut axis ⟂ deep-rank axis.")
print("   => deep corank cuts a+b>=rho+2 are hit DIRECTLY; the joint rank-sector build (D) is needed for them.")
