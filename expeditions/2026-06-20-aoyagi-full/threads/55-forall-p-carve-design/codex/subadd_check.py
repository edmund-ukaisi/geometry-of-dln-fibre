# Decorrelated check of the peel_le lemma (the one MEDIUM):
#   minAdm(r,r,p) <= j*p + minAdm(r-j,r-j,p)   for 1<=j<=r, all p>=1.
# minAdm(r,r,p) = min_{t=0..r}[(r-t)^2 + p*t]   (integer min).
def minAdm(r, p):
    if r == 0: return 0
    return min((r - t)**2 + p*t for t in range(r+1))

bad = []
for p in range(1, 12):
    for r in range(1, 12):
        lhs = minAdm(r, p)
        for j in range(1, r+1):
            rhs = j*p + minAdm(r-j, p)
            if lhs > rhs:
                bad.append((r,p,j,lhs,rhs))
print("peel_le (sub-additivity) violations:", bad if bad else "NONE (holds)")

# Also verify the lift mechanism I claimed: a binding t' for (r-j) lifts to t'+j for r with
#   (r-(t'+j))^2 + p(t'+j) = (r-j-t')^2 + p*t' + p*j = [minAdm(r-j,p) value at t'] + p*j.
# i.e. the t=(t'+j) stratum of (r,p) EQUALS the t=t' stratum of (r-j,p) plus j*p. Check identity:
import itertools
idok = True
for p in range(1,12):
    for r in range(1,12):
        for j in range(1, r+1):
            for tp in range(0, r-j+1):
                lhs = (r - (tp+j))**2 + p*(tp+j)
                rhs = ((r-j) - tp)**2 + p*tp + p*j
                if lhs != rhs:
                    idok = False; print("ID FAIL", r,p,j,tp,lhs,rhs)
print("stratum-lift identity (r-(t'+j))^2+p(t'+j) = (r-j-t')^2+p t' + pj :", "HOLDS" if idok else "FAILS")
