import sympy as sp
# My fabricated finding-1 case: hsQ=(z0;A_cor) 3x3, B 2x3.  As a B·W product: B is p×q=2×3, W is q×n=3×3.
p,q,n=2,3,3
def codim_r(r): return (p-r)*(q-r)+r*n
strata={r:codim_r(r) for r in range(0,min(p,q)+1)}
mA=min(strata.values())
print(f"My fabricated case B(2x3)·W(3x3): codim by rank r = {strata}")
print(f"  minAdm_full = {mA}  => T1 = {sp.Rational(mA,2)}")
print(f"  ab = a*b = 1*2 = 2 ; minAdm_red (z=1x3 single matrix) = 3 ; T2 = (3+2)/2 = {sp.Rational(5,2)}")
print(f"  => T1 == T2 == 5/2 : this cut is BINDING (argmin r=1 == u=1), so the MC could NOT discriminate T1 vs T2.")
print(f"  My finding-1 '2.5' was T1(=T2), mislabelled as 'finite to T2>T1'.")
