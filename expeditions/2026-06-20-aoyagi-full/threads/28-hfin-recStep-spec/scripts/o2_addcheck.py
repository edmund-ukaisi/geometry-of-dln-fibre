import sympy as sp
from functools import lru_cache

# ============================================================
# Does the recursion NEED the disjoint-sum ADD (jp/2 + lambda_{r-j,p}), or does
# dropping the Morse block (giving only lambda_{r-j,p}) suffice for the UPPER bound?
# The per-chart threshold is lambda_{r,p} = min(r^2/2, min_j(jp/2 + lambda_{r-j,p})).
# If we PROVE finiteness only up to the Sc-core threshold lambda_{r-j,p} (dropping the top Morse),
# we'd be claiming finiteness only for c' < lambda_{r-j,p}, which is WEAKER than c' < jp/2+lambda_{r-j,p}.
# Is jp/2 + lambda_{r-j,p} ever the BINDING min (so the ADD is load-bearing)?
# ============================================================

@lru_cache(maxsize=None)
def lam(r, p):
    if r == 0:
        return sp.Rational(0)
    cand = [sp.Rational(r*r, 2)]
    for j in range(1, r+1):
        cand.append(sp.Rational(j*p, 2) + lam(r-j, p))
    return min(cand)

# minAdm(r,r,p): for the square-corank core ||Delta*S||^2 (Delta r x r, S r x p) the
# achiever threshold. The cert says lambda_{r,p} = 1/2 * minAdm(r,r,p). Just check the recursion values
# and which j binds.
print("r  p  lambda_{r,p}   binding j (the min argument)    a-divisor r^2/2   Sc-core-only lambda_{r-j,p}")
for r in range(1,5):
    for p in range(2,6):
        L = lam(r,p)
        # find binding
        cands = {'a-div': sp.Rational(r*r,2)}
        for j in range(1, r+1):
            cands[f'j={j}'] = sp.Rational(j*p,2) + lam(r-j,p)
        binders = [k for k,v in cands.items() if v == L]
        # for the binding j, what is the Sc-core-only threshold (dropping the Morse jp/2)?
        msg = ""
        for k in binders:
            if k.startswith('j='):
                j = int(k[2:])
                core_only = lam(r-j,p)
                add = sp.Rational(j*p,2)+lam(r-j,p)
                msg += f"  [{k}: ADD={add}, core-only={core_only}, jp/2={sp.Rational(j*p,2)}]"
        print(f"{r}  {p}   {str(L):>8}     {','.join(binders):<28}  {str(sp.Rational(r*r,2)):>5}   {msg}")
print()
print("VERDICT on the ADD: if the binding j has jp/2 > 0 (always for j>=1,p>=1), then the ADD")
print("jp/2 + lambda_{r-j,p} is STRICTLY GREATER than lambda_{r-j,p} (the Sc-core-only).")
print("=> Dropping the top Morse block UNDERSHOOTS the threshold. The ADD IS load-bearing.")
print("   The recursion MUST realize the disjoint-sum additivity, NOT just dominate by the core.")
