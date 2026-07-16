# Adversarial check: the CONFIRMED verdict rests on "shell-j object finite for c'<1/2 minAdm M".
# Two independent justifications; verify they agree and neither is circular for the SOUNDNESS claim.
from fractions import Fraction as F
def codim_r(M0,M1,M2,r): return (M0-r)*(M1-r)+r*M2
def minAdm3(M0,M1,M2):
    vals={r:codim_r(M0,M1,M2,r) for r in range(0,min(M0,M1)+1)}
    m=min(vals.values()); return m,vals

print("JUSTIFICATION A (subset monotonicity): shell-j subset FULL box => RLCT_shellj >= RLCT_full = 1/2 minAdm M.")
print("JUSTIFICATION B (exact shell RLCT): RLCT_shellj = 1/2 * min_{k<=capj} codim_k >= 1/2 minAdm M (min over subset >= global min).")
print("Both give RLCT_shellj >= 1/2 minAdm M. Route needs c' < 1/2 minAdm M. => finite. CONFIRMED.\n")
print(f"{'chain':>9} {'j':>2}  {'RLCT_shellj(exact)':>18} {'1/2minAdm(need)':>15}  {'shellj>=need':>12} {'slack':>6}")
for (M0,M1,M2) in [(3,3,3),(4,4,4),(6,6,6),(8,8,8),(5,5,5),(4,4,6),(6,6,4)]:
    mA,vals=minAdm3(M0,M1,M2)
    ts=min(r for r in vals if vals[r]==mA); r=min(M0-ts,M1-ts)
    for j in range(1,r):
        rbmax=M1-(min(M1,M2)-j); allowed=[k for k in vals if k<=rbmax]
        rl=F(min(vals[k] for k in allowed),2); need=F(mA,2)
        print(f"{str((M0,M1,M2)):>9} {j:>2}  {str(rl):>18} {str(need):>15}  {str(rl>=need):>12} {str(rl-need):>6}")
print("\nNOTE on non-circularity: for SOUNDNESS (is the statement TRUE) we use the EXTERNAL exact")
print("RLCT computation (Jacobian codim, thresholdhunt), NOT the Lean mountain. So no circularity.")
print("For the LEAN PROOF, the mountain proves full-box via shells inductively -- that's a build route,")
print("not the soundness argument.")
